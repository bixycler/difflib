#!/usr/bin/python3
'''
Patching Chromium
'''

import argparse
import subprocess
import os
import re
import shutil
import pathlib
import worddifflib as wdl

#### Helper functions ########################

def fopen(fn, mode='r', encoding="utf-8", newline=''):
  return open(fn,mode=mode, encoding=encoding, newline=None if mode=='r' else newline)

def ensureDir(path):
  path = path.replace('\\','/')
  if path[-1] != '/': path += '/'
  return path

def splitwords(s):
  return list(filter(lambda x: x, re.split(r'(\W)', s)))

#### Patch helper functions ########################

def applyMod(mods, s, reverse=False, sorted=True):
  if not sorted: mods.sort(key=lambda m: m[3])
  (fri,toi) = (1,0) if reverse else (0,1)
  oj = 0; fr = s; to = ''
  for mod in mods:
    frs = mod[1+fri]; tos = mod[1+toi]
    frj = mod[3+fri]; toj = mod[3+toi]
    to += fr[oj:frj] + tos
    oj = frj + len(frs)
  to += fr[oj:]
  return to

def combineHunks(h1, h2, from_lines):
  '''Return new hunk = h1 + h2 referencing the from-text from_lines
    or None if any error
    Notes: 
      - The gap between h1 & h2 is considered no-diff.
      - This does not check the from-text of h1 & h2 against from_lines.
  '''
  h1l = h1.splitlines(True); h2l = h2.splitlines(True)
  h1a = wdl.parseHunkHeader(h1l[0]); h2a = wdl.parseHunkHeader(h2l[0])
  fl0 = h1a[0]; fl1 = fl0 + h1a[1]; fl2 = h2a[0]; fl3 = fl2 + h2a[1]
  tl0 = h1a[2]; tl1 = tl0 + h1a[3]; tl2 = h2a[2]; tl3 = tl2 + h2a[3]
  gap = fl2 - fl1
  #print('Merge {}-{} + {}-{} [{}-{} + {}-{}]'.format(fl0,fl1,fl2,fl3, tl0,tl1,tl2,tl3))
  if gap < 0 or gap != tl2-tl1 or fl3 > len(from_lines): return None
  hdr = makeHunkHeader(fl0,fl3-fl0, tl0,tl3-tl0, h1a[4])
  #print(hdr)
  gap = ''
  for i in range(fl1,fl2): gap += ' '+from_lines[i-1]
  h = hdr + ''.join(h1l[1:]) + gap + ''.join(h2l[1:])
  return h

def splitPatch(patch, splitHunks=False, header = 'diff --git a/'):
  '''Split a meta patch into single-file patches
    and optionally further into individual hunks
  '''
  pat = re.compile(r'^(@@ -\d+(?:,\d+)? \+\d+(?:,\d+)? @@.*)$', flags=re.MULTILINE)
  ps = {}
  for p in re.split('^'+header, patch, flags=re.MULTILINE):
    if not p.strip(): continue
    m = re.match('(.*) b/', p); f = m.group(1)
    p = header + p
    if not splitHunks: ps[f] = p; continue
    hss = pat.split(p)
    hs = [hss[0]] # patch file header
    for i in range(len(hss)//2): hs.append(hss[1+i*2]+hss[1+i*2+1])
    ps[f] = hs
  return ps

def fixPatch(oldpatch, newpatch, header = 'diff --git a/'):
  '''Return a patch which is oldpatch with files replaced by newpatch
    Replacement: For each file in oldpatch, if it's also in newpatch, use the new one.
  '''
  ops = splitPatch(oldpatch, header)
  nps = splitPatch(newpatch, header)
  ps = ''
  for p in ops:
    ps += nps[p] if p in nps else ops[p]
  return ps

def fixHunk(hunk, fdiff):
  return hunk

def checkPatch(fpatch, fdiff, flines):
  '''Check the single-file patch $fpatch against single-file diff $fdiff, referencing $flines
    and return the partial/fixed patch $patch with the remaining diff $diff
    old_f + fpatch = patched_f
    old_f + fdiff  = new_f
    old_f + patch + diff = new_patched_f
    Notes:
      - $fdiff is supposed to be raw diff without context
  '''
  if type(fpatch) is str:
    t = splitPatch(fpatch, splitHunks=True)
    fpatch = t[list(t)[0]]
  if type(fdiff) is str:
    t = splitPatch(fdiff, splitHunks=True)
    fdiff = t[list(t)[0]]
  if type(flines) is str: flines = flines.splitlines(True)
  nhunks = len(fpatch); ndhunks = 0
  phs = ''; i = 1; ib=ie= 0; dhs = ''
  interlockh = ''; pseudo = False; dhheader = ''
  for j in range(nhunks):
    if j==0: continue #patch file header
    h = fpatch[j]; hheader = h.splitlines(True)[0]
    if interlockh: h = interlockh
    #print(hheader)
    ads = wdl.parseHunkHeader(h); b = ads[0]; e = b+ads[1]
    # search for fdiff[ib:ie] matching flines[b:e]
    while i<len(fdiff): # seek the beginning
      adis = wdl.parseHunkHeader(fdiff[i]); bi = adis[0]; ei = bi+adis[1]
      if ei>b: #reach/pass the beginning
        if pseudo or not interlockh: ib = i; dhheader = ''
        break
      else: i+=1
    else: phs += h; break #fdiff[] exhausted without reaching
    interlockh = ''; pseudo = False
    while i<len(fdiff): # process until the end
      adis = wdl.parseHunkHeader(fdiff[i]); bi = adis[0]; ei = bi+adis[1]
      if bi>=e: break #reach/pass the end
      elif ei>e: #(pseudo-)interlock
        if j+1 < nhunks: hn = fpatch[j+1]; bn = wdl.parseHunkHeader(hn)[0]
        if j+1>=nhunks or bn>=ei: #speudo (empty hunk)
          bn = ei; pseudo = True
          hn = makeHunkHeader(bn,0, ads[2]+ads[3]+(bn-e),0, '[speudo hunk]')
        interlockh = combineHunks(h,hn, flines)
      mrk = '*' if pseudo else '+' if interlockh else ''
      print('    {}-{}{} <> {}-{}'.format(b,e,mrk, bi,ei))
      ie = i+1
      if interlockh and not pseudo: break #real interlock
      else: i+=1
    #end while process until the end
    dhheader += ('<+' if interlockh and not pseudo else '<<') + hheader
    if interlockh and not pseudo: continue #real interlock
    if ie-ib > 0: # insert fdiff[ib:ie] to dhs, and merge them to h if they contain simple replacements only
      dhs += dhheader + ''.join(h)+'>>'+str(ie-ib)+' diff(s):\n' + ''.join(fdiff[ib:ie])
      h = fixHunk(h,fdiff[ib:ie])
    interlockh = ''; pseudo = False
    if h: ndhunks+=1
    phs += h
  #end for j in range(nhunks)

  patch = diff = ''
  if dhs: diff = 'diff --fix'+fpatch[0][10:] + dhs
  if phs: patch = fpatch[0] + phs
  return (patch, diff, ndhunks)

############################

class ChromiumPatcher:
  '''The object that holds patching info and does patching works
  '''
  srcPath = './'
  patchPath = './'
  compsPath = ''
  comps = {'branding':{'wholes':[], 'mods':[], 'parts':[]}, }
  wholes = []; mods = []
  base = 'HEAD'
  def __init__(self, argv):
    tab = '    '
    print('Component info:')
    if 'comps' in argv and argv['comps']: self.comps = {}
    else: argv['comps'] = ['branding']
    if 'src' in argv and argv['src']: self.srcPath = ensureDir(argv['src'])
    if 'patch' in argv and argv['patch']: self.patchPath = ensureDir(argv['patch'])
    if 'comps_path' in argv and argv['comps_path']: self.compsPath = ensureDir(argv['comps_path'])
    if 'base' in argv and argv['base']: self.base = argv['base']
    for comp in argv['comps']:
      self.comps[comp] = {'wholes':[], 'mods':[], 'parts':[]}
      compfn = self.compsPath+ comp+'-files.txt'
      try: compf = fopen(compfn)
      except BaseException as e: 
        print('Error opening file "{}": {}'.format(compfn,str(e)))
        continue
      with compf: files = compf.readlines()
      if not files: print(tab+'Component "{}" is empty!'.format(comp)); continue
      print(tab+'Component "{}" contains {} file/dir(s)'.format(comp, len(files)))
      for f in files:
        fa = f.split('\t'); fd = {'tag':fa[0].strip(), 'file':fa[1].strip()}
        if len(fa)>2: fd['note'] = fa[2].strip()
        else: fd['note'] = None
        if fd['tag']=='MOD': self.mods.append(fd); self.comps[comp]['mods'].append(fd)
        elif fd['tag'] in ['ADD','REP']: self.wholes.append(fd); self.comps[comp]['wholes'].append(fd)
        elif fd['tag'] in ['BAK','PAR']: pass
        else: print('Error @ {}: Invalid tag "{}" in entry "{}"'.format(comp,fd['tag'],fd['file']))
      files = []; pfn = self.patchPath+ comp+'.patch.parts'
      if os.path.isfile(pfn):
        with fopen(pfn) as f: files = f.readlines()
      for fn in files: self.comps[comp]['parts'].append({'tag':'PAR', 'file':fn.strip()})
    print(tab+'Total {} whole file/dir(s)'.format(len(self.wholes)))
    print(tab+'Total {} modified file(s)'.format(len(self.mods)))
    print()
  
  def copyWholes(self, srcPath, dstPath):
    '''Copy whole files from srcPath to dstPath
    Note: Overwrite without warning!
    '''
    nf = 0; nd = 0
    for fd in self.wholes: 
      f = fd['file']
      src = srcPath + f
      dst = dstPath + f
      (d,b) = os.path.split(dst)
      try:
        if d: pathlib.Path(d).mkdir(parents=True, exist_ok=True)
        if '*' in b and b!='**': print('Error: unsupported wildcard (only "**" is supported): {}'.format(f)); continue
        if b=='**': b = ''; src = src[:-2]; dst = dst[:-2]
        if b: shutil.copy2(src,dst); nf += 1 #always overwrite!
        else: shutil.rmtree(dst); shutil.copytree(src,dst); nd += 1 #remove first, because copytree() doesn't overwrite.
      except BaseException as e: print('Error copying "{}" -> "{}": {}'.format(src,dst,str(e)))
    print('Copied "{}" -> "{}": {} file(s), {} dir(s)\n'.format(srcPath,dstPath, nf,nd))

  def updateWholes(self):
    '''Update whole files (& original files) from the Chromium source
    '''
    for comp in self.comps:
      for fd in self.comps[comp]['wholes']: 
        if not fd or not fd['file'] or fd['tag']!='REP': continue
        if not self.updateFile(fd['file'],'original'): continue
    self.copyWholes(self.srcPath, self.patchPath+'whole/')
  
  def patchWholes(self):
    '''Patch the Chromium source with whole files
    '''
    self.copyWholes(self.patchPath+'whole/', self.srcPath)
  
  def updateFile(self, f, ftype='original'):
    '''Update the original file $f
    '''
    # git show HEAD:chrome/...$f > .../original/.tmp > git diff .../original/...$f
    src = self.patchPath+'.src.tmp' if ftype=='original' else self.srcPath+f
    dst = self.patchPath+('original/' if ftype=='original' else 'patched/')+f

    # get the original src file from git base
    if ftype=='original':
      res = subprocess.run('git -C {} show {}:{} > {}'.format(
        self.srcPath,self.base,f, src), 
        shell=True, capture_output=True, encoding="utf-8")
      if res.returncode != 0: print('Error from git show "{}:{}": {}'.format(self.base,f,res.stderr)); return False

    # update the dest file if different from the src
    try:
      if not os.path.isfile(dst): # copy original
        (d,b) = os.path.split(dst)
        pathlib.Path(d).mkdir(parents=True, exist_ok=True)
        if os.path.isdir(dst): shutil.rmtree(dst)
        shutil.copy2(src,dst)
        print('{} created'.format(dst))
      else: # update original
        res = subprocess.run('git diff --no-index --shortstat -- {} {}'.format(dst,src),
          shell=True, capture_output=True, encoding="utf-8")
        if res.returncode != 0: # := "different", doesn't mean "error" (for this type of `git diff {} {}` only)
          if res.stderr: print('Error from git diff: {}'.format(res.stderr)); return False
          else: 
            shutil.copy2(src,dst)
            print('{} updated: {}'.format(dst, res.stdout[17:-1]))
      if src==self.patchPath+'.src.tmp' and os.path.isfile(src): os.remove(src)
    except BaseException as e: print('Error updating "{}": {}'.format(dst,str(e))); return False
    return True
  
  def updateMods(self, part='mods'):
    '''Update modified files (& original files) from the Chromium source
    '''
    #git diff --numstat HEAD > Beowulf-Docs\filelists\l.txt
    nps = 0; nc = 0
    for comp in self.comps:
      np = 0
      cmd = 'git -C {} diff {} -- '.format(self.srcPath, self.base)
      #print('Component "{}": {}'.format(comp,self.comps[comp]))
      for fd in self.comps[comp][part]: 
        if not fd or not fd['file']: continue
        cmd += ' '+fd['file']; np += 1
        if not self.updateFile(fd['file'],'original'): continue
        if not self.updateFile(fd['file'],'patched'): continue
      if not np: continue
      nc += 1
      #print('cmd: '+cmd)
      res = subprocess.run(cmd, shell=True, capture_output=True, encoding="utf-8")
      if res.returncode != 0: print('Error from git diff: {}'.format(res.stderr)); continue
      fn = self.patchPath + comp+'.patch'
      oldpatch = ''; newpatch = res.stdout
      try: 
        if part=='parts':
          with fopen(fn) as f: oldpatch = f.read()
          newpatch = fixPatch(oldpatch, newpatch)
        with fopen(fn,'w') as f: f.write(newpatch)
        #if os.path.isfile(fn+'.notfound'): os.remove(fn+'.notfound') # should be removed manually because manually resolved
        if os.path.isfile(fn+'.parts'): os.remove(fn+'.parts')
        #if os.path.isfile(fn+'.parts.diff'): os.remove(fn+'.parts.diff') # should be removed manually because manually resolved
        if os.path.isfile(fn+'.parts.patch'): os.remove(fn+'.parts.patch')
      except BaseException as e: print('Error handling file "{}": {}'.format(fn,str(e))); continue
      print('Updated component "{}": {} file(s) in "{}"\n'.format(comp, np, fn))
      nps += np
    print('Total {} file(s) in {} component(s) updated'.format(nps,nc))
    return nps
  
  def fixMods(self):
    self.updateMods('parts')
  
  def patchMods(self):
    '''Patch the Chromium source using *.patch
    '''
    tab = '    '
    np = 0
    for comp in self.comps:
      if not self.comps[comp]['mods']: continue
      print('Check component "{}": ...'.format(comp))
      ners = self.checkPatches(comp)
      print('... {}'.format('OK' if ners==0 else str(ners)+' failures' if ners>0 else 'ERROR!'))
      if ners==0: prefix = 'Patched '; suffix = ''
      else: prefix = 'Partly patched '; suffix = '.parts.patch'
      fn = self.patchPath + comp+'.patch' + suffix
      if not os.path.isfile(fn): continue
      res = subprocess.run('git -C {} apply --verbose < {} '.format(self.srcPath, fn), 
        shell=True, capture_output=True, encoding="utf-8")
      ress = tab + res.stderr[:-1].replace('\n','\n'+tab)
      if res.returncode != 0: 
        print('Error from git apply:')
        if ress.count('\n') < 10: print(ress)
        else: 
          print(tab+'see file "{}.err"'.format(fn))
          with fopen(fn+'.err','w') as f: f.write(ress)
        continue
      print(prefix+'component "{}":'.format(comp))
      print(ress+'\n')
      np += ress.count(tab+'Applied patch')
    print('Total {} file(s) patched\n'.format(np))

  def checkPatches(self, comp):
    '''Check the patches for applicability
      Returns the number of inapplicable hunks + files not found, or negative number if error
      Outputs:
      - $comp.parts.patch: the partial patch whose inapplicable hunks are excluded, 
          and with automatically fixed hunks included
      - $comp.parts.diff: the inapplicable hunks with diff between [old originals](./original/) and new originals in the source repo.
      - $comp.parts: the list of files to be fixed (later) by `fix mods`
      - $comp.notfound: the list of files not found
    '''
    ndh = 0; fnf = []; parts = []; diffs = ''; ps = ''
    fn = self.patchPath + comp+'.patch'
    try: pf = fopen(fn)
    except BaseException as e: 
      print('Error opening patch file "{}": {}'.format(fn,str(e)))
      return -1
    with pf: lines = pf.read()
    if not lines: return 0
    patches = splitPatch(lines, splitHunks=True)
    for p in patches:
      #print('patch {}:'.format(p))
      sfn = self.srcPath + p
      src = self.patchPath+'original/.tmp'
      dst = self.patchPath+'original/' + p
      # check source files (modified $sfn and originals $src, $dst)
      if not os.path.isfile(sfn): 
        print('Checking component "{}": File not found: {}'.format(comp,sfn))
        fnf.append(p); continue
      res = subprocess.run('git -C {} show {}:{} > {}'.format(
        self.srcPath,self.base,p, src), 
        shell=True, capture_output=True, encoding="utf-8")
      if res.returncode != 0:
        print('Error from git show "{}:{}": {}'.format(self.base,p,res.stderr))
        fnf.append(p); continue
      try:
        with fopen(dst) as f: olds = f.readlines()
      except BaseException as e: 
        print('Error reading original file: {}'.format(str(e)))
        fnf.append(p); continue
      # check diff between 2 originals (old $dst and new $src)
      res = subprocess.run('git diff --no-index -U0 -- {} {}'.format(dst,src),
        shell=True, capture_output=True, encoding="utf-8")
      if res.returncode == 0:  # := "no diff"
        ps += ''.join(patches[p]); continue
      if res.stderr: print('Error patching component "{}" from git diff: {}'.format(res.stderr)); continue
      ds = splitPatch(res.stdout, splitHunks=True)[dst]
      # check for the overlapping between diff hunks and patch hunks
      (phs,dhs, ndh) = checkPatch(patches[p],ds, olds)
      if dhs:
        diffs += dhs; parts.append(p)
        print('<<{}'.format(p))
      if phs: ps += phs
    #end for p in patches
    if src and os.path.isfile(src): os.remove(src)
    try:
      if fnf:
        with fopen(fn+'.notfound','w') as f: f.write('\n'.join(fnf))
      if parts:
        with fopen(fn+'.parts','w') as f: f.write('\n'.join(parts))
      if diffs:
        with fopen(fn+'.parts.diff','w') as f: f.write(diffs)
      if ps and (fnf or ndh):
        with fopen(fn+'.parts.patch','w') as f: f.write(ps)
    except BaseException as e: 
      print('Error writing working state: {}'.format(str(e)))
      return -1
    return ndh + len(fnf)

  def checkMods(self):
    ok = True
    for comp in self.comps:
      print('Check component "{}": ...'.format(comp))
      ners = self.checkPatches(comp)
      print('... {}'.format('OK' if ners==0 else str(ners)+' failures' if ners>0 else 'ERROR!'))
      if ners!=0: ok = False
    return ok

############################

def main(args):
  #print(args)
  p = ChromiumPatcher(vars(args))
  if not args.action: print('Error: Action is empty'); return
  doUpdate = 'update' == args.action[0]
  doPatch = 'patch' == args.action[0]
  doCheck = 'check' == args.action[0]
  doFix = 'fix' == args.action[0]
  forMods = 'mods' in args.action or 'all' in args.action
  forWholes = 'wholes' in args.action or 'all' in args.action
  done = False
  if doUpdate and forWholes: done = True; p.updateWholes()
  if doPatch and forWholes: done = True; p.patchWholes()
  if doUpdate and forMods: done = True; p.updateMods()
  if doPatch and forMods: done = True; p.patchMods()
  if doCheck and forMods: done = True; p.checkMods()
  if doFix and forMods: done = True; p.fixMods()
  if not done: print('Error: Invalid action "{}"'.format(' '.join(args.action))); return

if __name__ == "__main__": 
  parser = argparse.ArgumentParser(formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    description='Patch the Chromium source')
  parser.add_argument('action', metavar='[action part]', nargs='*', default=['patch','all'], 
    help='the action to do: "patch" to apply patches to the Chromium source; "check" to check the patches for applicability; "update" to update the patches from the Chromium source (see --base); "fix" to fix the failed patches using the Chromium source (see --base); and which part to be acted upon: "wholes" for whole files; "mods" for modififed files; "all" for all files. Note: when there are options, this argument must be prefixed with "--", eg. "-- update all" ')
  parser.add_argument('--comps', metavar='COMP', nargs="+", default=['branding'], 
    help='the list of component(s) to be patched')
  parser.add_argument('--src', metavar='DIR', default='../chromium/src/', help='the directory containing the Chromium source')
  parser.add_argument('--patch', metavar='DIR', default='./', help='the directory containing patches')
  parser.add_argument('--comps-path', metavar='DIR', default='../chromium/src/Beowulf-Docs/filelists/',
    help="the directory containing components' file lists")
  parser.add_argument('--base', metavar='REF', default='HEAD', help='the commit that patches are based on; can be a ref like "HEAD" or a commit hash')
  main(parser.parse_args())
  print()