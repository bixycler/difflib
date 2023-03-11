#!/usr/bin/python3
'''
Patching Chromium
'''

import argparse
import subprocess
import sys
import os
import re
import filecmp
import shutil
from pathlib import Path 
import json

import worddifflib as wdl

#### Helper functions ########################

tab = '  '
GitHashLength = 40
GitShortHashLength = 8

def fopen(fn, mode='r', encoding="utf-8", newline=''):
  return open(fn,mode=mode, encoding=encoding, newline=None if mode=='r' else newline)

def ensureDir(path):
  path = path.replace('\\','/')
  if path[-1] != '/': path += '/'
  return path

def nunit(n, unit,pl='s', sep=', ', showZero=False, unique=False):
  if unique: sep = ''; showZero = True
  if n > 1: unit+=pl
  s = '{} {}{}'.format(n,unit,sep) if n or showZero else ''
  return s

def splitwords(s):
  return list(filter(lambda x: x, re.split(r'(\W)', s)))

def command(cmd):
  res = subprocess.run(cmd, shell=True, capture_output=True, encoding="utf-8")
  return res

def gitdiff(a,b, opt=''):
  '''Check if 2 files a & b are different
    - Return the diff if diff, or errno if error
    - Return False if not diff
    Note: res.returncode != 0 means "different", doesn't mean "error" (for this type of `git diff {} {}` only)
  '''
  res = command('git diff --no-index {} -- "{}" "{}"'.format(opt, a,b))
  if res.returncode != 0: # := "different", doesn't mean "error"
    if res.stderr: 
      print('Error from git diff "{}" "{}": {}'.format(a,b, res.stderr))
      return res.returncode
    else: return res.stdout
  return False

def briefList(ls, pre='\n'+tab, maxn=10, noHead=False):
  '''Return the printed list from `ls` with max `maxn` lines'''
  m = len(ls); post = ''; head = [] if noHead else ['']
  if maxn+1 < m: m = maxn//2; post = pre+'...'
  s = pre.join(head+ls[:m]) + post
  return s

def syncFile(src, dst):
  '''Sychronize whole files between 2 full paths: src --> dst
    Return False if failed, or a string (ftype,action) indicating what was synced, where
      `ftype` in ['file','dir'];
      `action` in ['ADD','DEL','REP',''], empty action means "do nothing"
    Note: 
    - Overwrite & delete without warning!
    - To sync dirs, the full path must have trailing recursive wildcard, e.g. "dir/**"
  '''
  (ftype,action) = ('','')
  (d,b) = os.path.split(dst)
  try:
    if '*' in b and b!='**': print('syncFile Error: unsupported wildcard (only trailing recursive "/**" is supported): {}'.format(dst)); return False
    if b=='**': b = ''; src = src[:-2]; dst = dst[:-2]
    if d: Path(d).mkdir(parents=True, exist_ok=True)
    if b: # sync file
      ftype = 'file'
      if os.path.isdir(src) or os.path.isdir(dst): print('syncFile Error: directory not suffixed by recursive wildcard "/**": {}'.format(dst)); return False
      if os.path.isfile(src): # update the dest file if different from the src
        action = 'REP' if os.path.isfile(dst) else 'ADD'
        if action=='REP':
          if not filecmp.cmp(dst,src):
            shutil.copy2(src,dst) #always overwrite!
          else: action = ''
      elif os.path.isfile(dst): os.remove(dst); action = 'DEL'
    else: # sync dir
      ftype = 'dir'; srcexists = os.path.isdir(src)
      if os.path.isdir(dst): 
        shutil.rmtree(dst) #remove first, because copytree() doesn't overwrite.
        action = 'REP' if srcexists else 'DEL'
      elif srcexists: action = 'ADD'
      if srcexists: shutil.copytree(src,dst)
  except OSError as e: print('syncFile Error syncing "{}" -> "{}": {}'.format(src,dst,e)); return False
  return (ftype,action)

#### Patch helper functions ########################

def fixPatch(oldpatch, newpatch):
  '''Return a patch which is oldpatch with files replaced by newpatch
    Replacement: For each file in oldpatch, if it's also in newpatch, use the new one.
  '''
  ops = wdl.splitPatch(oldpatch)
  nps = wdl.splitPatch(newpatch)
  ps = ''
  for p in ops:
    ps += nps[p] if p in nps else ops[p]
  return ps

############################

class ChromiumPatcher(object):
  '''The object that holds patching info and does patching works
    Metadata:
      - Chromium src repo: $src/$f
      - Skynet patch repo: $patch/{{original,whole,patched}/$f, $comp.patch}
      - Component defs: {$comps-path = $src/Beowulf-Docs/filelists}/$comp-files.txt
      - Base commit $base(h) and original base $obaseh
    Update all & patch wholes:
      $src/     :$base     :index
                ↓ [update] ↓    ↑[patch]              
      $patch/   original/  {whole,patched}/
    Patch mods:
      $src/     :$obaseh :base  :index <------------[git add]------------ :workdir
                       |        /_\ ---[3-way merge]-----↴-------------------↴   ↑[patch]           
      $patch/          original/  patched/        conflict/ --[resolve]--> merged/ 
      - $patch/conflict/$f is partially patched with conflicting mods excluded
      - resolve: manually edit $patch/conflict/$f then invoke action `resolve`
  '''
  def __init__(self, argv):
    self.srcPath = './' # $src/
    self.patchPath = './' # $patch/
    self.compsPath = './filelists/'  # $comps-path/
    self.base = 'HEAD' # the new base for updating $patch/ <-- $src/
    self.baseh = '' # the full hash code of $base
    self.obaseh = '' # the original base of $patch/original/
    self.metadata = {'src':'', 'patch':'', 'comps_path':'', 'obaseh':''}
    self.metadatafn = '.metadata.json'
    self.allComps = {'all':{'wholes':[], 'mods':[], 'parts':[], 'atomic':False}, } # available comps in $compsPath/
    self.comps = {} # the comps to be handled
    self.total = {'wholes':[], 'mods':[], 'parts':[], 'atomic':False} # collect data from self.comps
    self.localUpdate = False
    try:
      with fopen(self.metadatafn,'r') as f: self.metadata = json.loads(f.read())
    except OSError as e: pass    
    if 'src' in argv and argv['src']: self.srcPath = ensureDir(argv['src'])
    elif 'src' in self.metadata and self.metadata['src']: self.srcPath = ensureDir(self.metadata['src'])
    if 'patch' in argv and argv['patch']: self.patchPath = ensureDir(argv['patch'])
    elif 'patch' in self.metadata and self.metadata['patch']: self.patchPath = ensureDir(self.metadata['patch'])
    if 'comps_path' in argv and argv['comps_path']: self.compsPath = ensureDir(argv['comps_path'])
    elif 'comps_path' in self.metadata and self.metadata['comps_path']: self.compsPath = ensureDir(self.metadata['comps_path'])
    if 'obaseh' in self.metadata and self.metadata['obaseh']: self.obaseh = self.metadata['obaseh']
    if 'base' in argv and argv['base']: self.base = argv['base']
    elif self.obaseh: self.base = self.obaseh
    if len(self.base)==GitHashLength: self.base = self.base[:GitShortHashLength]
    if 'comps' not in argv or 'none' in argv['comps']: argv['comps'] = [] # "none" means empty
    elif 'all' in argv['comps']: argv['comps'] = ['all'] # "all" means nothing else
    if 'local_update' in argv: self.localUpdate = argv['local_update']
    res = self._git('rev-parse '+self.base)
    if res.returncode != 0:
      print('Error from git rev-parse "{}": {}'.format(self.base,res.stderr))
    else: self.baseh = res.stdout.strip()
    self.metadata = {'src':self.srcPath, 'patch':self.patchPath, 'comps_path':self.compsPath, 'obaseh':self.obaseh}
    print('Metadata:')
    print(tab+'Source repository $src = [{}]'.format(os.path.abspath(self.srcPath)))
    print(tab+'Patch repository $patch = [{}]'.format(os.path.abspath(self.patchPath)))
    print(tab+'Component definitions $comps-path = [{}]'.format(os.path.abspath(self.compsPath)))
    print(tab+'Base commit $base = {} [{}]'.format(self.base,self.baseh))
    print(tab+'Original base commit $obaseh = [{}]'.format(self.obaseh))
    print()
    print('Available components in $comps-path:')
    for compfn in Path(self.compsPath).glob('*-files.txt'):
      compfn = str(compfn); comp = compfn[len(self.compsPath):-len('-files.txt')]
      ucomps = ['all'] # super-comps of this comp
      ucomp = comp
      while ucomp: # collect super-comps
        if ucomp not in self.allComps: self.allComps[ucomp] = {'wholes':[], 'mods':[], 'parts':[], 'atomic':ucomp==comp}
        if ucomp!=comp: ucomps+=[ucomp]
        i = ucomp.rfind('-')
        ucomp = ucomp[:i] if i >= 0 else ''
      try: compf = fopen(compfn)
      except OSError as e: 
        print('Error opening file "{}": {}'.format(compfn,e))
        continue
      with compf: files = compf.readlines()
      if not files: print(tab+'Component "{}" is empty!'.format(comp)); continue
      print(tab+'Component "{}" contains {}'.format(comp, nunit(len(files),'file/dir',unique=True)))
      for f in files:
        fa = f.split('\t'); fd = {'tag':fa[0].strip(), 'file':fa[1].strip()}
        if len(fa)>2: fd['note'] = fa[2].strip()
        else: fd['note'] = None
        if fd['tag']=='MOD': self.allComps[comp]['mods'].append(fd)
        elif fd['tag'] in ['ADD','DEL','REP']: self.allComps[comp]['wholes'].append(fd)
        elif fd['tag'] in ['BAK','PAR']: pass
        else: print('Error @ {}: Invalid tag "{}" in entry "{}"'.format(comp,fd['tag'],fd['file']))
      files = []; pfn = self.patchPath+ comp+'.patch.parts'
      if os.path.isfile(pfn):
        with fopen(pfn) as f: files = f.readlines()
      for fn in files: self.allComps[comp]['parts'].append({'tag':'PAR', 'file':fn.strip(), 'note':None})
      # collect sub-comp to the super-comp
      for ucomp in ucomps:
        self.allComps[ucomp]['wholes'] += self.allComps[comp]['wholes']
        self.allComps[ucomp]['mods']   += self.allComps[comp]['mods']
        self.allComps[ucomp]['parts']  += self.allComps[comp]['parts']
    print(tab+'Total {}'.format(nunit(len(self.allComps['all']['wholes']),'whole file/dir',unique=True)))
    print(tab+'Total {}'.format(nunit(len(self.allComps['all']['mods']),'modified file',unique=True)))
    print()
    compls = sorted(self.allComps.keys()) # sort comps so that super & sub-comps are contiguous
    for comp in argv['comps']: # expand super-comps to atomic comps --> self.comps[]
      try: j = 0 if comp=='all' else compls.index(comp)
      except ValueError as e: print('Error: Component "{}" (given via option --comps) not found.'.format(comp)); continue
      while j < len(compls) and (comp=='all' or compls[j].find(comp)==0): # list subcomps via format "comp-subcomp"
        if self.allComps[compls[j]]['atomic']: self.comps[compls[j]] = self.allComps[compls[j]]
        j+=1
    print('Component(s) to be handled: {}'.format(', '.join(list(self.comps.keys()))))
    for comp in self.comps: # collect total comp := sum(self.comps)
      self.total['wholes'] += self.comps[comp]['wholes']
      self.total['mods']   += self.comps[comp]['mods']
      self.total['parts']  += self.comps[comp]['parts']
    print(tab+'Total {}'.format(nunit(len(self.total['wholes']),'whole file/dir',unique=True)))
    print(tab+'Total {}'.format(nunit(len(self.total['mods']),'modified file',unique=True)))
    print(tab+'Total {}'.format(nunit(len(self.total['parts']),'partially patched file',unique=True)))
    print()
    try:
      with fopen(self.metadatafn,'w') as f: f.write(json.dumps(self.metadata, indent=2))
    except OSError as e: pass

  def _git(self, gcmd, workDir=''):
    if not workDir: workDir = self.patchPath+'original/'
    res = command('git --git-dir="{}.git" --work-tree="{}" {}'.format(self.srcPath,workDir, gcmd))
    return res

  def _gitcheckout(self, f, outDir='', orig=False):
    '''Very slow! Only useful for checking out dir'''
    if not outDir: outDir = self.patchPath+'original/'
    base = self.obaseh if orig else self.baseh
    res = self._git('checkout {} -- "{}"'.format(base,f), workDir=outDir)
    return res

  def _gitshow(self, f, out='', orig=False):
    '''`git show` is 10 times faster than `git checkout`!!!'''
    if out: out = '> "'+out+'"'
    base = self.obaseh if orig else self.baseh
    res = self._git('show {}:"{}" {}'.format(base,f, out))
    return res
  
  def _testShow(self):
    src = self.patchPath+'/.src.tmp'
    for fd in self.allComps['all']['mods']:
      res = self._gitshow(fd['file'], src)
      print('.',end=''); sys.stdout.flush()
      if os.path.isfile(src): os.remove(src)
    print()
  
  def _testCheckout(self):
    basesrc = self.patchPath+'.src.dir.tmp/'
    for fd in self.allComps['all']['mods']:
      Path(basesrc).mkdir(parents=True, exist_ok=True)
      res = self._gitcheckout(fd['file'], basesrc)
      print('.',end=''); sys.stdout.flush()
      if basesrc and os.path.isdir(basesrc): shutil.rmtree(basesrc)
    print()

  def expandDir(self, fls):
    '''Expand all dir glob [/**] in the file list `fls` and return (efls,dls) where
      - efls is the list of expanded files
      - dls is the list of dirs
    '''
    efls = []
    dls = []
    for fd in fls:
      if len(fd['file'])>=2 and fd['file'][-2:]=='**': 
        dn = fd['file'][:-2]; dls+=[{'tag':fd['tag'], 'file':dn}]
        dp = Path(self.patchPath+'/whole/'+dn)
        #print('>{}'.format(dp))
        for fn in dp.glob('**/*'): 
          if os.path.isdir(fn): dls+=[{'tag':fd['tag'], 'file':fn.as_posix()}]; continue
          fn = dn+Path(os.path.relpath(fn,start=dp)).as_posix()
          #print(' >> {}'.format(fn))
          efls+=[{'tag':fd['tag'], 'file':fn}]
      else: efls+=[fd]
    return (efls, dls)

  def checkStatus(self):
    '''Check for consistency between $comps-path/, $patch/, and $src/
    '''
    print('\n=== Check Status ===\n')
    updated = True
    # check the status of file lists
    #git diff --numstat HEAD > Beowulf-Docs\filelists\l.txt
    res = self._git('diff --cached --name-status '+self.baseh)
    if res.returncode != 0: 
      print('Error from git diff "{}": {}'.format(self.base,res.stderr)); return False
    else:
      files = res.stdout.splitlines()
      pfiles = {} # the files in $patch/
      (pfs,pds) = self.expandDir(self.allComps['all']['wholes'])
      for fd in pfs + self.allComps['all']['mods']: pfiles[fd['file']] = fd['tag']
      gitfiles = {} # the files in $src/
      gnpfiles = {} # the files in $src/ but not in $patch/
      wtfiles = {} # the files with wrong tag
      def checkConsistency(fn,tag): # check for consistency with $patch/
        nonlocal pfiles, gnpfiles, wtfiles
        if fn not in pfiles: gnpfiles[fn] = tag
        else:
          ptag = pfiles[fn]
          if tag!=ptag and not (tag=='MOD' and ptag=='REP'): 
            wtfiles[fn] = 'patch({}) <> src({})'.format(ptag,tag)
          del pfiles[fn]
      for fn in files:
        gfd = fn.split('\t'); (tag,fn) = gfd[:2]
        tag = 'ADD' if tag[0]=='A' else 'DEL' if tag[0]=='D' else 'MOD' if tag[0]=='M' else 'REN' if tag[0]=='R' else ''
        if not tag: print('checkStatus ERROR: unknown git status: '+str(gfd))
        if tag=='REN': # REN old -> new == DEL old, ADD new
          gitfiles[fn] = 'DEL'; gitfiles[gfd[2]] = 'ADD'
          checkConsistency(fn,'DEL'); checkConsistency(gfd[2],'ADD')
        else: 
          gitfiles[fn] = tag
          checkConsistency(fn,tag)
      # `pfiles` now contains the ones left over in $patch/ only
      if gnpfiles:
        updated = False
        print('File changes in $src/ not refected in $comps-path/ and $patch/:')
        for fn in gnpfiles: print(tab+'{} {}'.format(gnpfiles[fn],fn))
        print()
      if pfiles:
        updated = False
        print('Patched files in $comps-path/ and $patch/ not refected in $src/:')
        for fn in pfiles: print(tab+'{} {}'.format(pfiles[fn],fn))
        print()
      if wtfiles:
        updated = False
        print('Patched files in $comps-path/ and $patch/ with mismatched change in $src/:')
        for fn in wtfiles: print(tab+'[{}]\t{}'.format(wtfiles[fn],fn))
        print()
      if updated: print('File lists in $comps-path/ are in sync with $src/.\n')
  
    # check the status of individual files
    src = self.patchPath+'/.src.tmp'
    for comp in self.allComps:
      if not self.allComps[comp]['atomic']: continue
      (wholes,_) = self.expandDir(self.allComps[comp]['wholes'])
      mods = self.allComps[comp]['mods']
      print('Component "{}": in {} ...'.format(comp, nunit(len(wholes+mods),'file',unique=True)))
      origdiff = []
      if self.baseh!=self.obaseh: # check orig
        for fd in wholes + mods:
          res = self._gitshow(fd['file'], src)
          fn = self.patchPath+'/original/'+fd['file']
          if not os.path.isfile(fn) or not filecmp.cmp(src, fn): origdiff+=[fd['file']]
      if origdiff:
        updated = False
        print('Component "{}": {} mismatched{}\n'.format(
          comp, nunit(len(origdiff),'original file',unique=True), briefList(origdiff)))
      # check patched
      pdiff = []
      for fd in wholes:
        f1 = self.srcPath+fd['file']; f2 = self.patchPath+'/whole/'+fd['file']
        if not os.path.isfile(f1) or not os.path.isfile(f2) or not filecmp.cmp(f1, f2): pdiff+=[fd['file']]
      for fd in mods:
        f1 = self.srcPath+fd['file']; f2 = self.patchPath+'/patched/'+fd['file']
        if not os.path.isfile(f1) or not os.path.isfile(f2) or not filecmp.cmp(f1,f2): pdiff+=[fd['file']]
      if pdiff:
        updated = False
        print('Component "{}": {} mismatched{}\n'.format(
          comp, nunit(len(pdiff),'patched file',unique=True), briefList(pdiff)))
    if os.path.isfile(src): os.remove(src)
    
    if updated: print("Everything's updated! $patch/ and $comps-path/ are in sync with $src/. ")

  def syncWhole(self, f, srcPath, dstPath):
    '''Update the file/dir $f from repo $src/, orig (base) or patched (work dir)
    '''
    basesrc = self.patchPath+'.src.dir.tmp/' if srcPath[0]=='$' else ''
    src = srcPath + f
    dst = dstPath + f
    if basesrc: # get the src from git base
      src = basesrc + f; fn = f
      if len(f) > 2 and f[-2:]=='**': fn = f[:-2]
      try: Path(basesrc).mkdir(parents=True, exist_ok=True)
      except OSError as e: print('syncWhole Error: cannot make dir "{}": {}'.format(basesrc,e)); return False
      if fn!=f: res = self._gitcheckout(fn, basesrc, srcPath=='$obaseh')
      else: src = basesrc+'.src.tmp'; res = self._gitshow(f, src, srcPath=='$obaseh')
      if res.returncode != 0: print('Error from git checkout/show "{}:{}": {}'.format(srcPath,fn, res.stderr)); return False

    # update the dest file if different from the src
    res = syncFile(src,dst)
    if res:
      (ft,tag) = res
      acted = 'created' if tag=='ADD' else 'removed' if tag=='DEL' else 'updated' if tag=='REP' else ''
      if acted: print(tab+'Sync {} --> {}: {} {} {}'.format(srcPath,dstPath, ft,f,acted))
    if basesrc and os.path.isdir(basesrc): shutil.rmtree(basesrc)
    return res

  def updateBase(self):
    self.metadata['obaseh'] = self.obaseh = self.baseh
    try:
      with fopen(self.metadatafn,'w') as f: f.write(json.dumps(self.metadata, indent=2))
    except OSError as e: return False    
    return True

  def updateWholes(self):
    '''Update whole files (& original files) from the Chromium source
    '''
    if self.localUpdate: return
    nps = nc = 0
    for comp in self.comps: 
      wholes = self.comps[comp]['wholes']
      print('Update component "{}": {} whole file/dir(s) ...'.format(comp,len(wholes)))
      nfo=ndo = nfp=ndp = nd = 0
      for fd in wholes: 
        if not fd or not fd['file'] or fd['tag'] not in ['ADD','DEL','REP']: continue
        if fd['tag'] != 'ADD' and self.baseh!=self.obaseh: # update origs 
          res = self.syncWhole(fd['file'], '$base', self.patchPath+'original/')
          if not res: continue
          if res[1]: 
            if res[0]=='file': nfo+=1
            else: ndo+=1
        res = self.syncWhole(fd['file'], self.srcPath, self.patchPath+'whole/')
        if not res: continue
        if res[1]:
          if res[0]=='file': nfp+=1
          else: ndp+=1
        print('.',end=''); sys.stdout.flush(); nd+=1
      if nd: print()
      print('Component "{}": updated {}{}{}{}'.format(comp, nunit(nfo,'orig file'),nunit(ndo,'orig dir'), nunit(nfo,'patch file'),nunit(ndo,'patch dir',sep='')))
      nd = nfo+ndo + nfp+ndp
      if nd: nps+=nd; nc+=1
    print('Total {} in {} updated\n'.format(nunit(nps,'file',unique=True),nunit(nc,'component',unique=True)))
    self.updateBase()
  
  def patchWholes(self):
    '''Patch the Chromium source with whole files
    '''
    for comp in self.comps: 
      wholes = self.comps[comp]['wholes']
      print('Patch component "{}" with {} whole file/dir(s) ...'.format(comp,len(wholes)))
      nf = 0; nd = 0
      for fd in wholes: 
        res = self.syncWhole(fd['file'], self.patchPath+'whole/', self.srcPath)
        if not res: continue
        if res[1]:
          if res[0]=='file': nf+=1
          else: nd+=1
      print('Component "{}" patched by wholes: {}{}\n'.format(comp, nunit(nf,'file'),nunit(nd,'dir')))
  
  def updateMods(self, part='mods'):
    '''Update modified files (& original files) from the Chromium source
    '''
    nps = 0; nc = 0; loc = 'locally' if self.localUpdate else ''
    for comp in self.comps:
      fn = self.patchPath + comp+'.patch'
      no=np = nd = 0
      oldpatch = newpatch = ''
      if os.path.isfile(fn):
        try: 
          with fopen(fn) as f: oldpatch = f.read()
        except OSError as e: print('Error reading file "{}": {}'.format(fn,e)); continue
      #print('Component "{}": {}'.format(comp,self.comps[comp]))
      print('Update component "{}": {} in "{}" ...'.format(comp, nunit(len(self.comps[comp][part]),'mod file',unique=True), fn))
      for fd in self.comps[comp][part]: # update orig, patched, and patch if needed
        if not fd or not fd['file']: continue
        #print(tab+'{} ... '.format(fd['file']),end=''); sys.stdout.flush()
        diff = False
        if not self.localUpdate:
          if self.baseh!=self.obaseh:
            res = self.syncWhole(fd['file'], '$base', self.patchPath+'original/')
            if not res: print('Original file update error: {}'.format(fd['file'])); continue
            if res[1]: diff = True; no+=1
          res = self.syncWhole(fd['file'], self.srcPath, self.patchPath+'patched/')
          if not res: print('Patched file update error: {}'.format(fd['file'])); continue
          if res[1]: diff = True; np+=1
        else: diff = True; np+=1
        if diff or not oldpatch: newpatch+=wdl.diffFile('original/'+fd['file'],'patched/'+fd['file'])
        #print('{} mod(s) '.format(diff.count('\n#<')))
        print('.',end=''); sys.stdout.flush(); nd+=1
      if nd: print()
      if not newpatch: continue
      nc+=1
      try: # update $comp.patch if needed
        if oldpatch: 
          shutil.copy2(fn,fn+'.bak') # backup this patch and overwrite the old backup
          newpatch = fixPatch(oldpatch, newpatch)
        with fopen(fn,'w') as f: f.write(newpatch)
        #if os.path.isfile(fn+'.notfound'): os.remove(fn+'.notfound') # should be removed manually because manually resolved
      except OSError as e: print('Error handling file "{}": {}'.format(fn,e)); continue
      diff = wdl.diffFile(fn+'.bak', fn) if os.path.isfile(fn+'.bak') else newpatch 
      nm = diff.count('\n#<')
      print('Component "{}": {}{} updated {} with {}\n'.format(comp, nunit(no,'mod file'), nunit(np,'patch file',sep=''), loc, nunit(nm,'modification',unique=True)))
      nps += no+np
    print('Total {} in {} updated {}\n'.format(nunit(nps,'file',unique=True),nunit(nc,'component',unique=True), loc))
    if not loc: self.updateBase()
    return nps
  
  def fixMods(self):
    self.updateMods('parts')
  
  def patchMods(self):
    '''Patch the Chromium source using *.patch
    '''
    np = 0; prefix = ''
    for comp in self.comps:
      if not self.comps[comp]['mods']: continue
      print('Check component "{}": ...'.format(comp))
      ners = self.checkPatches(comp)
      print('... {}'.format('OK' if ners==0 else str(ners)+' failures' if ners>0 else 'ERROR!'))
      if ners==0: prefix = 'Patched '; suffix = ''
      else: prefix = 'Partly patched '; suffix = '.parts.patch'
      fn = self.patchPath + comp+'.patch' + suffix
      if not os.path.isfile(fn): continue
      try: pass #syncFile(...) 
      except OSError as e: print('Error handling file: {}'.format(e)); continue
    if prefix:
      print(prefix+'component "{}":'.format(comp))
      print('Total {} file(s) patched\n'.format(np))

  def checkPatches(self, comp):
    '''Check the patches for applicability
      Returns the number of conflict hunks + files not found, or negative number if error
      Outputs:
      - ./merged/: the files successfully 3-way merged from patched + orig + new_rev, to be used later in patchMods()
      - ./conflict/: the partially merged files, to be manually resolved
      - $comp.merged: the list of files in ./merged/
      - $comp.conflict: the list of files in ./conflict/
      - $comp.notfound: the list of files not found
      - $comp.merged.patch: the patch for merged files 
      - $comp.conflict.patch: the partial patch whose conflict hunks are excluded
      - $comp.conflict.diff: the conflict hunks with diff between [old originals](./original/) and new originals in the source repo.
          and with automatically fixed hunks included
    '''
    if not self.allComps[comp]['mods']: return 0
    mergedfs = []; mpatches = ''
    fnf = []; conflicts = []; confldiffs = conflpatches = ''
    fn = self.patchPath + comp+'.patch'
    nd = 0
    try: pf = fopen(fn)
    except OSError as e: 
      print('Error opening patch file "{}": {}'.format(fn,e))
      return -1
    with pf: lines = pf.read()
    if not lines: return 0
    patches = wdl.splitPatch(lines, byhunk=True)
    for pf in patches:
      #print(tab+'{} ... '.format(pf),end=''); sys.stdout.flush()
      newrevf = self.srcPath + pf
      originalf = self.patchPath+'original/' + pf
      patchedf = self.patchPath+'patched/' + pf
      mergedf = self.patchPath+'merged/' + pf
      conflictf = self.patchPath+'conflict/' + pf
      newrev = original = patched = ''
      # check for files not found
      found = True
      if not os.path.isfile(newrevf): found = False; fnf+=[newrevf]
      if not os.path.isfile(originalf): found = False; fnf+=[originalf]
      if not os.path.isfile(patchedf): found = False; fnf+=[patchedf]
      if not found: 
        #print('FILE NOT FOUND!')
        print('0',end=''); sys.stdout.flush(); nd+=1
        continue
      # try 3-way merge
      if os.path.isfile(mergedf) or os.path.isfile(conflictf) or filecmp.cmp(patchedf,newrevf): 
        #print('checked')
        continue
      try:
        with fopen(newrevf,'r') as f: newrev = f.read()
        with fopen(originalf,'r') as f: original = f.read()
        with fopen(patchedf,'r') as f: patched = f.read()
      except OSError as e: 
        print('Error opening file: {}'.format(e))
      #(mtxt,md,conflict,ids) = wdl.mergeDiff(original, patched, newrev, 'txt','txt')
      (merged,md,confl,ids) = wdl.mergeDiff(original, patches[pf][1:], newrev, 'hunks','txt','hunks')
      try: # write merged files and record conflicts
        if confl:
          conflicts+=[pf]; 
          hdr = wdl.makeDiffHeader('worddiff', [originalf,patchedf,newrevf,conflictf])
          conflpatches+=hdr+''.join(md)
          Path(os.path.dirname(conflictf)).mkdir(parents=True, exist_ok=True)
          with fopen(conflictf,'w') as f: f.write(merged)
          (cdp,cdd) = confl
          hdr = wdl.makeDiffHeader('worddiff', [conflictf,patchedf,newrevf,mergedf])
          confldiffs+=hdr+''.join(cdp)+'@@@ DIFF @@@\n'+''.join(cdd) # FIXME: sort & for
        else: 
          hdr = wdl.makeDiffHeader('worddiff', [originalf,patchedf,newrevf,mergedf])
          mergedfs+=[pf]; mpatches+=hdr+''.join(md)
          Path(os.path.dirname(mergedf)).mkdir(parents=True, exist_ok=True)
          with fopen(mergedf,'w') as f: f.write(merged)
        if len(ids) > 1: print('WARNING: {} seems already patched!'.format(f))
      except OSError as e: 
        print('Error writing file: {}'.format(e))
      #print('{}'.format('CONFLICT!!!' if confl else 'merged'))
      print('!' if confl else '.',end=''); sys.stdout.flush(); nd+=1
    if nd: print()
  
    def export(ls,fn, msg):
      if ls:
        if msg: print('{}: [{}]{}'.format(msg, fn, briefList(ls)))
        with fopen(fn,'w') as f: f.write(('\n' if msg else '').join(ls))
    try: # export working state to files
      Path(self.patchPath+'work/').mkdir(parents=True, exist_ok=True)
      fn = self.patchPath+'work/'+comp+'.patch'
      export(fnf,fn+'.notfound','Not found')
      export(mergedfs,fn+'.merged','Merged')
      export(mpatches,fn+'.merged.patch','')
      export(conflicts,fn+'.conflict','Conflict')
      export(conflpatches,fn+'.conflict.patch','')
      export(confldiffs,fn+'.conflict.diff','')
    except OSError as e: 
      print('Error writing working state: {}'.format(e))
      return -1
    return len(conflicts) + len(fnf)

  def checkMods(self):
    ok = True
    for comp in self.comps:
      print('Check component "{}": {} ...'.format(comp, nunit(len(self.comps[comp]['mods']),'mod file',unique=True)))
      ners = self.checkPatches(comp)
      print('... {}'.format('OK' if ners==0 else nunit(ners,'issue',unique=True) if ners>0 else 'ERROR!'))
      if ners!=0: ok = False
    return ok

############################

def main(args):
  #print(args)
  p = ChromiumPatcher(vars(args))
  #p._testShow(); return
  #p._testCheckout(); return
  if not args.action: print('Error: Action is empty'); return
  doCheck = 'check' == args.action[0]
  doUpdate = 'update' == args.action[0]
  doPatch = 'patch' == args.action[0]
  doFix = 'fix' == args.action[0]
  forMods = 'mods' in args.action or 'all' in args.action
  forWholes = 'wholes' in args.action or 'all' in args.action
  forStatus = 'status' in args.action or 'all' in args.action
  done = False
  if doCheck and forStatus: done = True; p.checkStatus()
  if doUpdate and forWholes: done = True; p.updateWholes()
  if doUpdate and forMods: done = True; p.updateMods()
  if doCheck and forMods: done = True; p.checkMods() #p.checkPatches()
  if doPatch and forWholes: done = True; p.patchWholes()
  if doPatch and forMods: done = True; p.patchMods()
  if doFix and forMods: done = True; p.fixMods()
  if not done: print('Error: Invalid action "{}"'.format(' '.join(args.action))); return

if __name__ == "__main__": 
  parser = argparse.ArgumentParser(formatter_class=argparse.RawDescriptionHelpFormatter ,
    description='''\
patch.py manages patches in $patch/ dir for a source git repository in $src/ dir, referencing the lists of patched files in $comps-path/ dir, which are separated into components corresponding to $comps-path/$comp-files.txt.

Requirements
  - All new files in $src/ must be tracked by git, i.e. `git add`ed, for this script to work properly. 
  - $src repo should contain the original base commit, so that the action `check status` can work properly.

Command examples:
  patch.py check updates
  patch.py update mods --local-update
  patch.py patch all
  patch.py fix all --comps branding others\
    ''')
  parser.add_argument('action', metavar='[action part]', nargs='*', default=['patch','all'], 
    help='the `action` to do: "patch" to apply patches to the Chromium source, "check" to check for updates and patch applicability, "update" to update the patches from the Chromium source (see --base), "fix" to fix the failed patches; And which `part` to be acted upon: "wholes" for whole-file added/replaced files, "mods" for modififed files, "status" for status of $src repo and $patch repo, "all" for all files. Possible combinations: "patch wholes|mods|all", "check status|mods|all", "update wholes|mods|all", "fix mods|all" . Note: these arguments should be specified before any option, or else they must be separated from options by "-- ", e.g. "--comps branding others -- update all". [Default: "patch all"] ')
  parser.add_argument('--comps', metavar='COMP', nargs="+", default=['branding'], 
    help='the list of component(s) to be patched, "all" for all of available components, "none" for patching/updating nothing (just checking info) [Default: "branding"]')
  parser.add_argument('--src', metavar='DIR', default='../chromium/src/', 
    help='the directory containing the Chromium source [Default: "../chromium/src/"]')
  parser.add_argument('--patch', metavar='DIR', default='./', 
    help='the directory containing patches [Default: "./"]')
  parser.add_argument('--comps-path', metavar='DIR', default='../chromium/src/Beowulf-Docs/filelists/',
    help='the directory containing components\' file lists [Default: "../chromium/src/Beowulf-Docs/filelists/"]')
  parser.add_argument('--base', metavar='REF', default='', 
    help='the commit that patches are based on; can be a ref like "HEAD" or a commit hash; enter new base to update $patch, or leave it empty (default), i.e. `--base=""`, to get the original base stored in metadata [Default: ""]')
  parser.add_argument('--local-update', action='store_true', default=False, 
    help='the flag telling that the patches $patch/$comp.patch will be updated using local files in $patch/ dir only, without referencing $src/ dir [Default: False]')
  main(parser.parse_args())
  print()