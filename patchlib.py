#!/usr/bin/python3
'''
`patchlib`: Functions supporting word-level diff and merging 2 diffs (patch + diff)

* Merge patch + diff:
  In the parallel flows of upstream (u) and downstream (d)
  --> u1 --> u2 --> u3 -->
      ↓      ↓      ↓
  --> d1 --> d2 --> d3 -->
  there are 3 diff arrows (math functions):
  "patch" := d - u    <=>  u + patch = d   <=>  u --[patch]--> d
  "diff"  := u2 - u1  <=>  u1 + diff = u2  <=>  u1 --[diff]--> u2
  "mdiff" := patch + diff  <=>  u1 + mdiff = d2  <=>  old --[mdiff]--> new-patched
  --> u(old) ----------> u(new) ----------> 
      ↓                  ↓      
  --> d(old-patched) --> d(new-patched) --> 

* Word-diff of patch + diff:
  "diff" = modify[i] = (tag, dels,inss, frj,toj) where 
  (frj,toj) is in char unit but `dels` and `inss` are in word unit
  Mods are collectively shown in 2-char-prefixed lines.
  Mods of patch, diff and both are marked by (+), (#) and (*), resp.
    -!Modified by: patch, diff, and both, ...
    -?             ++++++ ##### **********
    +<patch,>--> patched,
    +<and both, >--
    #< diff, and both>--> diffed
    #> with another line
'''

import re
#import difflib # replaced by our own worddifflib
import worddifflib as wdl

#### Constants and data structures ###################

class CONST(object):
  __slots__ = ()
  
  # Types of diff
  (DTUniDiff, DTWordDiff, DTPatchDiff) = (1, 2, 3)
  DiffTypePat = r'(unified|git|unidiff|worddiff|patchdiff)'
  DiffTypeMap = {'unified':DTUniDiff, 'git':DTUniDiff, 'unidiff':DTUniDiff, 
    'worddiff':DTWordDiff, 'patchdiff':DTPatchDiff,
    DTUniDiff:'unidiff', DTWordDiff:'worddiff', DTPatchDiff:'patchdiff'}
  Mod2Mark = {'orig':'-', 'patch':'+', 'diff':'#', '':'?'}

CONST = CONST()

#### General helper functions ########################
import pprint
pp = pprint.PrettyPrinter(sort_dicts=False, indent=2, width=100)

def fopen(fn, mode='r', encoding="utf-8", newline=''):
  return open(fn,mode=mode, encoding=encoding, newline=None if mode=='r' else newline)

#### Patch functions ########################


def splitPatch(patch, splitHunks=False, header = r'diff --'+CONST.DiffTypePat+r' "?a/'):
  '''Split a multiple-file patch (string) into single-file diffs indexed by orig file path
    and optionally further into individual hunks
  '''
  hunkpat = re.compile(r'^(@@ -\d+(?:,\d+)? \+\d+(?:,\d+)? @@.*)$', flags=re.MULTILINE)
  ps = {}
  for p in re.split('^('+header+')', patch, flags=re.MULTILINE):
    if not p.strip(): continue # skip the first empty match before diff header
    m = re.fullmatch(header, p)
    if m: phdr = m.group(0); continue # store the diff command header into `phdr`
    if re.fullmatch(CONST.DiffTypePat, p): continue # skip the diff-type match
    m = re.match(r'([^"\n]*)"? "?b/', p); f = m.group(1) # catch the orig file path with `f`
    p = phdr + p # restore the diff command header 
    if not splitHunks: ps[f] = p; continue
    hss = hunkpat.split(p)
    # process diff file header
    phdr = ''
    for hl in hss[0].splitlines(True): # filter out extended header lines
      if re.match('^'+header, hl) or re.match(r'^(---|\+\+\+) ', hl): phdr += hl
    hs = [phdr]
    # collect the pairs of (hunk header + hunk body)
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
    ads = parseHunkHeader(h); b = ads[0]; e = b+ads[1]
    # search for fdiff[ib:ie] matching flines[b:e]
    while i<len(fdiff): # seek the beginning
      adis = parseHunkHeader(fdiff[i]); bi = adis[0]; ei = bi+adis[1]
      if ei>b: #reach/pass the beginning
        if pseudo or not interlockh: ib = i; dhheader = ''
        break
      else: i+=1
    else: phs += h; break #fdiff[] exhausted without reaching
    interlockh = ''; pseudo = False
    while i<len(fdiff): # process until the end
      adis = parseHunkHeader(fdiff[i]); bi = adis[0]; ei = bi+adis[1]
      if bi>=e: break #reach/pass the end
      elif ei>e: #(pseudo-)interlock
        if j+1 < nhunks: hn = fpatch[j+1]; bn = parseHunkHeader(hn)[0]
        if j+1>=nhunks or bn>=ei: #speudo (empty hunk)
          bn = ei; pseudo = True
          hn = makeHunkHeader(bn,0, ads[2]+ads[3]+(bn-e),0, '[speudo hunk]')
        interlockh = combineHunks(h,hn, flines)
      mrk = '*' if pseudo else '+' if interlockh else ''
      #print('    {}-{}{} <> {}-{}'.format(b,e,mrk, bi,ei))
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


#### Testing functions ########################

import argparse

def test_parseHunk():
  '''with fopen('test/patchlib-test.txt') as f: txt = f.read()
  with fopen('test/patchlib-test-patched.txt') as f: patched = f.read()
  with fopen('test/patchlib-test.patch') as f: ps = f.read()
  hs = splitPatch(ps, splitHunks=True)['test\\\\patchlib-test.txt']
  #phs = parseHunk(hs[1], byword=True)
  #diffs,_,_ = mods2Diff(phs['modify'], phs['from'], line_diff=False, context_lines=1)
  mods = wordDiff(txt, patched, junk_match=JunkWordMatch, bitty_match=0.0) # WordSeparatorMatch JunkWordMatch 0.1
  diffs,_,_ = mods2Diff(mods, txt, line_diff=False, context_lines=1)
  diffhdr = hs[0]
  f = fopen('test/patchlib-test.patch.diff','w')
  f.write(diffhdr + ''.join(diffs))
  return mods #phs'''
  pass

def main(args):
  #print(args)
  test_parseHunk()

if __name__ == "__main__": 
  parser = argparse.ArgumentParser(formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    description='Test the module "patchlib"')
  main(parser.parse_args())
  print()