#!/usr/bin/python3
'''
`worddifflib`: Functions supporting word-level diff

* Diff of 2 strings:
  Compare(from_s, to_s) = [same1, diff1, same2, diff2, ...], where
  "same" = "longest (best) common substring (LCS)", and the remaining
  "diff" = modify[i] = (tag, dels,inss, frj,toj) where 
    from_s[frj: frj+len(dels)] --[modify[i]]--> to_s[toj: toj+len(inss)]
    tag = "delete" if inss==''  <=>  '...' --> ''
    tag = "insert" if dels==''  <=>  '' --> '...'
    tag = "replace" if dels!='' && inss!=''  <=>  '...' --> '...'

* Word-level diff (word-diff):
  "diff" = modify[i] = (tag, dels,inss, frj,toj) where 
  (frj,toj) is in char unit but `dels` and `inss` are in word unit
  Mods are collectively shown in 2-char-prefixed lines.
  Visualize source text `dels`:
    All mods with `dels` within a line are shown in the same couple of lines ((-!)(-?)), where
      the second line (-?) specifies the indices `frj`, `tag` and diff type, e.g.
      -!Mods: delete, insert here, replace. [this match is to separate from next mods]
      -?     --------        ^     ########
    If `dels` spans accross lines, the whole lines are shown in single lines {(--),(-#)}
  Visualize dest text `inss`:
    Each mod is shown in a line [(#<) dels >--> inss], where 
      the overflowing text to the next lines are shown in lines [(#>) inss], e.g.
      #<  delete,>--
      #<^>--> this_word 
      #< replace. >--> replaced. 
    Those mods are shown in the order of `frj`.
    Special cases of `dels` has reps: 
      '<$>' for `dels` spanning accross lines
      '<^>' for dels=='', or '<.>' for dels+ == '^...'

* Theory: 
  from: "DELETE."
    to: ".INSERT"
  - Matches: \.(7,1), \E(2,5), \E(4,5), \E(6,5), \T(5,7)
  - LCS = [\E(2,5),\T(5,7)], [\E(4,5),\T(5,7)]
  - Mods:
    1 mod 0 match (trivial): DELETE.-->.INSERT
    2 mods 1 match:
      DELETE-- \.(7,1) >INSERT
      D-->.INS \E(2,5) LETE.-->RT
      DEL-->.INS \E(4,5) TE.-->RT
      DELET-->.INS \E(6,5) .-->RT
      DELE-->.INSER \T(5,7) E.--
    3 mods 2 matches:
      D-->.INS \E(2,5) LE-->R \T(5,7) E.--
      DEL-->.INS \E(4,5) >R \T(5,7) E.--
  - Element length: 
    Each element here can be not only a letter but also a string, like a word, or more complicated object. So the true length of an element e should be given by a function `length(e)`, where the special case here is length(e='E')=1.
  - Number of contiguous substrings:
    To reduce the number of mods, the number of matches should be reduced (they are the same). That means between many short matches and a long match, we should choose the long one. So there are 2 solutions:
    1. In many LCSs, we choose the one with least matches, i.e. the "compact" one (CLCS).
    2. Use the "gestalt pattern matching" (GPM) with recursive longest match as in `difflib.py`.
    When the mods are (much) smaller than the matches, the 2 approaches lead to the same result.
      #fr     = 'word.diff.lib'
      #to     = 'word-level.difference.library'
      #LCS=GPM= 'word      .diff      .lib    '
    When the mods are large, the results can be significantly different:
      ### CLCS and CLS better than GPM
      #fr   = 'microcosm-macrocosm'
      #to   = "microwave.background.of.the.cosmos.in.microcomputer's.memory"
      #LCS  = 'mi          c  r     o      cosm      m croco       s   m   '
      #CLCS = 'micro                       cosm      m croco       s   m   ' #Git, GNU's diffutils
      #GPM  = '                                      microco       s m m r ' #Python
      #diff = 'micro       c   o             sm      m croco       s m     ' #BusyBox (Hunt–Szymanski algorithm)
      #diff = 'micro                                                       ' #WinDiff
      ### CLCS better than GPM (GPM ~ LCS!)
      #fr   = 'microcosm'
      #to   = "microwave.background.of.the.cosmos.in.microcomputer's.memory"
      #LCS  = '                                      microco       s   m   '
      #CLCS = 'micro                       cosm                            '
      #GPM  = '                                      microco       s m     '

* References:
  - Longest common subsequence (LCS): https://en.wikipedia.org/wiki/Longest_common_subsequence_problem
  - Edit distance: https://en.wikipedia.org/wiki/Edit_distance
  - Levenshtein distance: https://en.wikipedia.org/wiki/Levenshtein_distance
  - String metric: https://en.wikipedia.org/wiki/String_metric
  - A greedy algorithm for LCS by Eugene W. Myers: http://www.xmailserver.org/diff2.pdf
  - Hirschberg's algorithm: https://en.wikipedia.org/wiki/Hirschberg%27s_algorithm
'''

import re
import shlex
import difflib 
'''`difflib` implements the "gestalt pattern matching" (by Ratcliff and Obershelp) 
  to find the longest *contiguous* matching subsequence that contains no "junk" elements (separators) `find_longest_match()`, which is extended as far as possible by matching (only) junk elements on both sides, then recursively find longest matches in the remaining two ends `get_matches()`. This does not yield minimal edit sequences, but does tend to yield matches that naturally "look right" to people. 
  In `worddifflib`, we use our own algorithm to treat the junks (word separators, stop words, ...) and completely disable the "junk" feature of `difflib`.  
'''

#### Constants and data structures ###################

class CONST(object):
  __slots__ = ()
  # RE patterns of word separators (don't use r'[...]+' because each one should be treated separately)
  BlobWordSepPat = r'[ \t\n]' # the most general word, e.g. "this-long/string+without*space"
  RegularWordSepPat = r'[\W]' # the general word of the world, e.g. "a_word", "từ", "ことば"
  EnglishWordSepPat = r'[^A-Za-z_0-9]' # the most restricted word (in programming)
  
  # Types of diff
  DiffTypePat = r'(unified|git|unidiff|worddiff|patchdiff)'
  Mod2Mark = {'delete':'-', 'insert':'^', 'replace':'#', '':'?'}

  # Control chars
  (NUL, SOH,STX,ETX,EOT, ENQ,ACK,BEL, 
    BS,HT,LF,VT,FF,CR,SO,SI, DLE,DC1,DC2,DC3,DC4, 
    NAK,SYN,ETB,CAN,EM,SUB,ESC, FS,GS,RS,US) = (
    '\x00',  '\x01','\x02','\x03','\x04',  '\x05','\x06','\x07',
    '\x08','\x09','\x0A','\x0B','\x0C','\x0D','\x0E','\x0F',  '\x10','\x11','\x12','\x13','\x14',
    '\x15','\x16','\x17','\x18','\x19','\x1A','\x1B',  '\x1C','\x1D','\x1E','\x1F')

CONST = CONST()

# The separators between words, can be set by lib users to define what's a word
WordSepPat = CONST.RegularWordSepPat 
# The common words that should not be compared
StopWords = {'also':1, 'an':1, 'and':1, 'are':1, 'as':1, 'at':1, 
  'be':1, 'because':1, 'been':1, 'but':1, 'by':1, 'for':1, 'from':1, 'has':1, 'have':1, 'however':1, 'if':1, 'in':1, 'is':1, 'not':1, 'of':1, 'on':1, 'or':1, 'so':1, 'than':1, 'that':1, 'the':1, 'their':1, 'there':1, 'these':1, 'this':1, 'to':1, 'was':1, 'were':1, 'whatever':1, 'whether':1, 'which':1, 'with':1, 'would':1}

#### General helper functions ########################

def splitWords(s):
  ''' Split the string `s` into a list of words together with the surrounding separators. 
    The EOL should be treated as a special separator (defined in `WordSepPat`).
  '''
  return list(filter(lambda x: x, re.split('('+WordSepPat+')', s))) # filter out empty strings
  #return re.split('('+WordSepPat+')', s)

def quote(s):
  if s.find(' ') >= 0: s = '"{}"'.format(s.replace('"','\\"'))
  return s

def addr(s, lo=0, co=0):
  '''Zero-based 2D address (line, column) of the last position in `s`, i.e. of `len(s)`
    Optional offset `(lo,co)` can be given to rebase the address.
  '''
  l = s.count('\n')
  s = s[::-1]+'\n'
  c = s.index('\n')
  return (l+lo, c+co)

def fopen(fn, mode='r', encoding="utf-8", newline=''):
  return open(fn,mode=mode, encoding=encoding, newline=None if mode=='r' else newline)

# Junk matches
def WordSeparatorMatch(m): return re.fullmatch(WordSepPat+'+',m)
def JunkWordMatch(m):
  for s in list(filter(lambda x: x, re.split(WordSepPat, m))):
    if not(len(s) <= 1 or s in StopWords):
      return False
  return True

#### Hash list ########################

class HashList(object):
  '''The object wrapping a given list (of strings) with its hashed values for quick comparation
  '''
  hashed = {} # object -> hash value
  unhashed = {} # hash value -> object
  length = {} # hash value -> object's length
  #self.hlist = [] # index -> hash value
  class HashedElement(object):
    '''The wrapper of HashList's elements
    '''
    def __init__(self, i, h, l): 
      self.i = i # the index of this element in hlist
      self.h = h # the hash value of this element
      self.l = l # the length this element
      #print('{} #{} [{}] '.format(i,h,l))
    def __len__(self):
      return self.l
    def __eq__(self, other):
      return self.h==other.h

  def __init__(self, ls, dummy=CONST.NUL):
    self.elements = [] # the list of HashedElement objects 
    for i in range(len(ls)):
      hobj = obj = ls[i]
      if obj not in HashList.hashed: 
        h = hash(obj)
        while h in HashList.unhashed and obj!=HashList.unhashed[h]: # check collision
          print('!!! HASH COLLISION: #{} = hash({})#{} == hash({})#{} !!!'.format(h, hobj,hash(hobj), HashList.unhashed[h],hash(HashList.unhashed[h])))
          hobj+=dummy; h = hash(hobj)
        if h in HashList.unhashed: # DEBUG check logic
          print('HashList ERROR: Wrong logic!\n#[{}] = {} \n HashList.unhashed = {}\nHashList.hashed = {} '.format(hobj,h, HashList.unhashed,HashList.hashed))
        HashList.hashed[obj] = h; HashList.unhashed[h] = obj; HashList.length[h] = len(obj)
      else: h = HashList.hashed[obj]
      self.elements+=[HashList.HashedElement(i, h, HashList.length[h])]
    #print('HashList.__init__(): {} elements '.format(len(self.elements)))
  def __len__(self):
    return len(self.elements)
  def __contains__(self, e):
    return e in self.elements
  def __getitem__(self, k):
    return self.elements[k]


#### Diff functions ########################

def compactLongestCommonSubsequence(fr, to, compact=True, length=len):
  ''' Return the longest common subsequence (not contiguous like substring) between 2 lists `fr` & `to` with the least contiguous substrings. The result is a list of matches (fr_i, to_j, w) where 
    (fr_i, to_j) = index to (fr, to),
    w = number of matching elements.
    - The length of each element in the lists are given by function `length()`
    - `compact`=False to disable match compacting functionality for faster computation
    - Ref: https://en.wikipedia.org/wiki/Longest_common_subsequence_problem#Code_for_the_dynamic_programming_solution
  '''
  lcs = [] # list of matches (fr_i, to_j, w) where w = number of matching elements in list `fr`
  # matrix[i][j] of prefix-LCS pointers (int(length), bool(^del),bool(<ins))
  #   match = (length+, True,True)
  #   plcs[i+1][j+1] <- fr[i] to[j]
  plcs = [[(0,False,False)]+[(0,False,True) for j in range(len(to))]] # top margin (<<<<<)
  plcs += [[(0,True,False)] for i in range(len(fr))] # left margin (^)
  matxt = {} # the matrix output as text
  def indx(i,j): return '{}_{}'.format(i,j)
  def match(i,j): return i > 0 and j > 0 and fr[i-1]==to[j-1]
  for i in range(len(fr)+1): 
    for j in range(len(to)+1): 
      matxt[indx(i,j)] = '  '
  # compute plcs[] using dynamic programming
  for i in range(len(fr)): 
    for j in range(len(to)): 
      if match(i+1,j+1): 
        plcs[i+1] += [(plcs[i][j][0]+length(fr[i]), True,True)]
        matxt[indx(i+1,j+1)] = '& '
      else:
        ml = max(plcs[i][j+1][0],plcs[i+1][j][0])
        plcs[i+1] += [(ml, ml==plcs[i][j+1][0],ml==plcs[i+1][j][0])]

  # retrieve the default LCS
  i = len(fr); j = len(to); w = 0
  for ij in range(len(fr)+1+len(to)+1):
    (ml, bdel,bins) = plcs[i][j]
    if match(i,j): w += 1; matxt[indx(i,j)] = '&='
    elif w: lcs += [(i,j, w)]; w = 0; matxt[indx(i,j)] = ' \\'
    if match(i,j): (i,j) = (i-1,j-1)
    elif bdel: i -= 1
    elif bins: j -= 1
  lcs = lcs[::-1]

  # back track the whole graph of LCSs, very costly, just for debug
  '''passed = [[False for j in range(len(to)+1)] for i in range(len(fr)+1)]
  def backtrack(mi,mj, l):
    nonlocal lcs
    q = [] # the queue used by depth-first search
    (mml, _,_) = plcs[mi][mj]
    #print('{}{} '.format((i,j),plcs[mi][mj]),end='')
    if (mi,mj)==(0,0): # sum up the LCS
      if not l: return
      ls = []; ml = 0; (i,j) = l[0]; w = 0
      #print('== ',end='')
      for k in range(len(l)+1): 
        #print('{}{}'.format(fr[l[k][0]], l[k]),end=' ')
        if k==len(l) or k>0 and (l[k][0]-1, l[k][1]-1) != l[k-1]: 
          m = (i,j, w); ls += [m]; 
          for wi in range(w): ml += length(fr[i+wi])
          #print('[{}]{}'.format(fr[i:i+w], m),end=' ')
          if fr[i:i+w] != to[j:j+w]: print('longestCommonSubsequence ERROR: fr[i:i+w] != to[j:j+w]: {} != {} @ {} '.format(fr[i:i+w],to[j:j+w], m))
          if k < len(l): (i,j, w) = (l[k][0],l[k][1], 1)
        else: w += 1
      #print(); 
      if ml != plcs[-1][-1][0]: print('longestCommonSubsequence ERROR: ml({}) != plcs.ml({}) '.format(ml,plcs[-1][-1][0]))
      if len(ls) < len(lcs): # update the compact LCS
        print('<<< {} < {} '.format(len(ls), len(lcs)))
        lcs = ls
      return
    # the first pseudo cell (-1,-1) --> (len(fr),len(to)) must be handled 
    #   specially to gather all cells at the same level with (len(fr),len(to))
    if match(mi,mj) and (mi,mj)!=(-1,-1): # main process
      if matxt[indx(mi,mj)] != '&=': matxt[indx(mi,mj)] = '&*'
      # dequeue(mi,mj)
      mml -= length(fr[mi-1]); l = [(mi-1,mj-1)]+l; 
      # enqueue(mi-1,mj-1)
      q = [(mi-1,mj-1)] 
      for ip in range(mi): # reset passed[:mi-1][:mj-1] which was tainted by previous sibling branches
        for jp in range(mj):
          passed[ip][jp] = False
    else: # enqueue(i,j)
      q = [(mi,mj) if (mi,mj)!=(-1,-1) else (len(fr),len(to))] 
    #print('l({}){},  q = {} '.format(mml,l,q))
    # depth-first search all cells in the domain of ml==mml
    while q:
      (i,j) = q.pop(); (ml, bdel,bins) = plcs[i][j]
      #print('q = {} --> plcs{}={} '.format(q,(i,j),plcs[i][j]))
      if ml < mml: # out of level mml
        passed[i][j] = False # retract for the next level
        continue
      else: 
        if passed[i][j]: print('*** RESTEP to {} !!! (error in DFS)'.format((i,j)))
        passed[i][j] = True
      if bdel and not passed[i-1][j]: q += [(i-1,j)]
      if bins and not passed[i][j-1]: q += [(i,j-1)]
      if (i,j)==(0,0) or match(i,j) and ml==mml: # back track (i,j)
        backtrack(i,j, l)
  if compact: backtrack(-1,-1, [])'''

  # decremental-depth-first search the whole graph of LCSs
  # the top pseudo cell (-1,-1) is added above (len(fr),len(to)) 
  #   to gather all cells at the same level with (len(fr),len(to))
  glcs = {indx(-1,-1):[]} # the graph (flow network) of LCSs
  if compact:
    for i in range(len(fr)+1):
      for j in range(len(to)+1):
        glcs[indx(i,j)] = []
    passed = [[False for j in range(len(to)+1)] for i in range(len(fr)+1)]
    qm = [(-1,-1)] # the queue of matching cells in plcs[]
    while qm:
      mml = -1
      (mi,mj) = qm.pop() # qm.dequeue(mi,mj)
      (mml, _,_) = plcs[mi][mj]
      if (mi,mj)==(0,0): continue # a full LCS reached  
      ql = [] # the queue of same-level cells in plcs[]
      (pi,pj) = (-1,-1) # the little sibling of the parent, AKA. little parent
      if match(mi,mj) and (mi,mj)!=(-1,-1): # process the match(mi,mj)
        if matxt[indx(mi,mj)] != '&=': matxt[indx(mi,mj)] = '&*'
        mml -= length(fr[mi-1])
        if glcs[indx(mi,mj)]: # get little parent
          (pi,pj) = glcs[indx(mi,mj)][0] 
          glcs[indx(mi,mj)] = [] # reset for children
        # ql.enqueue(mi-1,mj-1)
        ql = [(mi-1,mj-1)] 
        #print('mml({}){}[{}]: ql = {}, qm = {}'.format(mml,(mi,mj),fr[mi-1], ql,qm))
      else: # ql.enqueue(mi,mj)
        ql = [(mi,mj) if (mi,mj)!=(-1,-1) else (len(fr),len(to))] 
        #print('mml({}){}: ql = {}, qm = {}'.format(mml,(mi,mj), ql,qm))
      
      # breadth-first search all cells in the domain of same-level ml==mml
      indent = '{m: >{mlw}}'.format(m='',mlw=5+len(str(ml)))
      (si,sj) = (-1,-1) # big sibling 
      if passed[ql[0][0]][ql[0][1]]: print('*** RESTEP to {} !!! (error in DFS)'.format(ql[0]))
      while ql:
        (i,j) = ql.pop(0); (ml, bdel,bins) = plcs[i][j] # ql.dequeue(i,j)
        #print('  ql = {} --> plcs{}={} '.format(ql,(i,j),plcs[i][j]))
        if ml < mml: continue # out of level mml
        if bdel and not passed[i-1][j]: ql += [(i-1,j)]; passed[i-1][j] = True
        if bins and not passed[i][j-1]: ql += [(i,j-1)]; passed[i][j-1] = True
        if (i,j)==(0,0) or match(i,j) and ml==mml: # register match(i,j)
          qm += [(i,j)] # qm.enqueue(i,j)
          glcs[indx(mi,mj)] += [(i,j)] # parent(mi,mj) --> child(i,j)
          if (si,sj)!=(-1,-1): glcs[indx(si,sj)] = [(i,j)] # big sibling(si,sj) --> little sibling(i,j)
          #print('{}{} --> {}[{}] '.format(indent,(mi,mj), (i,j), fr[i-1] if i else ''))
          (si,sj) = (i,j) # update sibling
      if (pi,pj)!=(-1,-1): # subsume all children of the little parent
        glcs[indx(mi,mj)] += glcs[indx(pi,pj)] # big parent(mi,mj) --> [children of little parent(si,sj)]
        #print('{}{} =={}--> {} '.format(indent,(mi,mj),(pi,pj), glcs[indx(pi,pj)]))
        if glcs[indx(pi,pj)] and (si,sj)!=(-1,-1): 
          glcs[indx(si,sj)] = [glcs[indx(pi,pj)][0]] # smallest sibling of (mi,mj) --> biggest sibling of (pi,pj)
    lenglcs = 0
    for ij in glcs: lenglcs += len(glcs[ij])
    print('**** The flow network computed: len(gLCS) = {}'.format(lenglcs))

  # back track glcs[] to find the compact LCS, very costly, just for debug
  '''def backtrack(mi,mj, ml):
    nonlocal lcs
    (pi,pj,w) = ml[0]; l = ml
    if (mi,mj)==(0,0): # sum up the LCS
      mll = 0
      for m in ml:
        (pi,pj,w) = m
        for wi in range(w): mll += length(fr[pi+wi])
        if fr[pi:pi+w] != to[pj:pj+w]: print('longestCommonSubsequence ERROR: fr[i:i+w] != to[j:j+w]: {} != {} @ {} '.format(fr[pi:pi+w],to[pj:pj+w], m))
        #print('[{}]{} '.format(fr[pi:pi+w],m),end='')
      #print()
      if mll != plcs[-1][-1][0]: print('longestCommonSubsequence ERROR: ml({}) != plcs.ml({}) '.format(mll,plcs[-1][-1][0]))
      if len(ml) < len(lcs): # update the compact LCS
        print('<<< {} < {} '.format(len(ml), len(lcs)))
        lcs = ml
    for (i,j) in glcs[indx(mi,mj)]: # recursive over all children
      if (i,j)==(0,0): l = ml
      elif (mi,mj)==(-1,-1) or (i,j)==(pi,pj): 
        l = [(i-1,j-1,w+1)] + ml[1:]
      else: l = [(i-1,j-1,1)] + ml
      backtrack(i,j, l)
  if compact: backtrack(-1,-1, [(-1,-1, 0)])'''

  # breadth-first search glcs[] for the compact LCS, still very costly! So it's just a game!
  # the queue of matches (i,j, w,n), where 
  #   w = size of the last contiguous match, n = number of contiguous matches
  if compact:
    qm = [(-1,-1, 0,0)]; mmn = 0
    flcs = {} # the reverse graph of glcs[], indx:(i,j, n), for constructing LCS   
    while qm:
      (mi,mj, mw,mn) = qm[0] # get the parent, which will be dequeued or extended
      if mn > mmn: mmn = mn; print('mn = {}, len(qm) = {} '.format(mn,len(qm)))
      #print('{} --> {} '.format(qm[0],glcs[indx(qm[0][0],qm[0][1])]))
      if (mi,mj)==(0,0):  # a full LCS reached  
        print('mn = {}, mw = {}, len(qm) = {}: '.format(mn,mw,len(qm)),end='')
        lcs = []; ml = 0 # the compact LCS
        (pi,pj) = (mi,mj); (ci,cj, w) = (-1,-1, 0)
        (i,j, n) = m = flcs[indx(mi,mj)]
        while (i,j)!=(-1,-1):
          if fr[i-1]!=to[j-1]: print('longestCommonSubsequence ERROR: fr[i] != to[j]: {} != {} @ {} '.format(fr[i-1],to[j-1], (i-1,j-1)))
          ml += length(fr[i-1])
          if (i,j)==(pi+1,pj+1) and (pi,pj)!=(0,0): # extend lcs[-1]
            w += 1; lcs[-1] = (ci,cj, w)
          else: # new contiguous match
            if (pi,pj)!=(0,0): print('[{}]{} '.format(fr[ci:ci+w],lcs[-1]),end='')
            (ci,cj, w) = (i-1,j-1, 1)
            lcs += [(ci,cj, w)]
          (pi,pj) = (i,j)
          (i,j, n) = m = flcs[indx(i,j)]
        if lcs: print('[{}]{} '.format(fr[ci:ci+w],lcs[-1]),end='')
        print()
        if ml != plcs[-1][-1][0]: print('longestCommonSubsequence ERROR: ml({}) != plcs.ml({}) '.format(ml,plcs[-1][-1][0]))
        break
      extended = False # == `extend`: whether the parent is extended by a contiguous child match
      for (i,j) in glcs[indx(mi,mj)]:
        w = mw; n = mn; extend = False
        if (mi,mj)==(-1,-1): # the first match(es)
          w = 1; n = 1
        elif (i,j)==(0,0): # the last contiguous match
          w = 0
        elif (i,j)!=(mi-1,mj-1): # new contiguous match
          n += 1; w = 1
        else: # extend the previous contiguous match
          w += 1; extend = extended = True
        if extend: qm[0] = (i,j,w,n) # extend the parent
        else: qm += [(i,j,w,n)] # qm.enqueue(child)
        # update flcs[]
        if indx(i,j) not in flcs or n < flcs[indx(i,j)][2]:
          flcs[indx(i,j)] = (mi,mj, n)
      if not extended: 
        #print('{}-- '.format(qm[0]))
        qm.pop(0) # qm.dequeue(parent)
      #else: print('{}++ '.format(qm[0]))
  

  #DEBUG: check result
  (ml, _,_) = plcs[-1][-1]; sl = 0
  for (i,_,w) in lcs: 
    for m in fr[i:i+w]: sl += length(m)
  if ml!=sl: print('longestCommonSubsequence check ERROR: max_len[{}] != sum_len[{}] '.format(ml,sl))
  #print('longestCommonSubsequence result: count = {}, ml = {} '.format(len(lcs),ml))
  
  #DEBUG: print maxtrix matxt[]
  '''def e2(n):
    s = str(n % 100)
    if len(s)<2 or s[-1]!='0': s = ' '+s[-1]
    return s
  ms = ''
  for i in range(len(fr)+1): 
    for j in range(len(to)+1): 
      if i==0 and j==0: c = '\\ '
      elif j==0: c = fr[i-1][0]+' '
      elif i==0: c = to[j-1][0]+' '
      else: c = matxt[indx(i,j)]
      #if c=='  ': c = ' {}'.format(plcs[i][j][0] % 10) # print `ml`
      if c[0]==' ': # print ^del <ins
        if plcs[i][j][1] and plcs[i][j][2]: c = '+'+c[1]
        elif plcs[i][j][1]: c = '^'+c[1]
        elif plcs[i][j][2]: c = '<'+c[1]
      ms += c
    ms += e2(i)+'\n'
  for j in range(len(to)+1): 
    ms += e2(j)
  ms += '\n'
  print(ms)'''
    
  lcs += [(len(fr),len(to), 0)] # the last pseudo-match
  return lcs

def pLCS(fr, to, frjb=0, frje=None, tojb=0, toje=None, length=len):
  '''Return the bottom line of matrix[][] of prefix-LCS lengths
    - The length of each element in the lists are given by function `length()`
    - Ref: https://en.wikipedia.org/wiki/Longest_common_subsequence_problem#Code_for_the_dynamic_programming_solution
  '''
  if frje is None: frje = len(fr)
  if toje is None: toje = len(to)
  # plcs[j] := matrix[i][j] <- fr[i] to[j]; uplcs[j] := matrix[i-1][j]
  uplcs = plcs = {}
  for j in range(tojb,toje+1):  # top margin (<<<<<) for uplcs[], left margin (^) for j==tojb-1
    uplcs[j-1] = plcs[j-1] = 0
  # compute plcs[] using dynamic programming on matrix[i][j]
  for i in range(frjb,frje): 
    for j in range(tojb,toje): 
      if fr[i]==to[j]: # matrix[i][j] <- matrix[i-1][j-1] + length
        plcs[j] = uplcs[j-1] + length(fr[i])
      else: # matrix[i][j] <- max(matrix[i-1][j],matrix[i][j-1])
        plcs[j] = max(uplcs[j],plcs[j-1])
    uplcs,plcs = plcs,uplcs
  return plcs

def longestCommonSubsequence(fr, to):
  ''' Return the longest common subsequence (not contiguous like substring) between 2 lists `fr` & `to`e as a list of matches (fr_i, to_j, w) where
    (fr_i, to_j) = index to (fr, to), 
    w = number of matching elements.
    - The length of each element in the lists are given by function `length()`
    - This function implements the recursive divide and conquer algorithm by Hirschberg: https://en.wikipedia.org/wiki/Hirschberg%27s_algorithm
  '''
  lcs = [] # list of matches (fr_i, to_j, w) where w = number of matching elements in list `fr`
  return lcs

def longestMatch1(fr,to, frjb=0, frje=None, tojb=0, toje=None):
  '''Return the longest common substring between 2 lists `fr` & `to`e as a tuple (fr_i, to_j, w) where
    fr[fr_i:fr_i+w] == to[to_j:to_j+w]
  '''
  if frje is None: frje = len(fr)
  if toje is None: toje = len(to)
  (li,lj, lw) = (frjb,tojb, 0)
  uml = {} # the longest matches in the previous line (i-1)
  for i in range(frjb,frje):
    ml = {} # the longest matches in this line (i)
    for j in range(tojb,toje):
      if fr[i]==to[j]:
        w = ml[j] = uml.get(j-1, 0) + 1
        if w > lw: (li,lj, lw) = (i-w+1,j-w+1, w)
    uml = ml
  return (li, lj, lw)

def longestMatch(fr,to, frjb=0, frje=None, tojb=0, toje=None):
  '''Return the longest common substring between 2 lists `fr` & `to`e as a tuple (fr_i, to_j, w) where
    fr[fr_i:fr_i+w] == to[to_j:to_j+w]
  '''
  if frje is None: frje = len(fr)
  if toje is None: toje = len(to)
  (li,lj, lw,ll) = (frjb,tojb, 0,0)
  # ml[j] := matrix[i][j] <- fr[i] to[j] (w, len); uml[j] := matrix[i-1][j]
  uml = {}
  # compute (li, lj, lw) using dynamic programming on matrix[i][j]
  for i in range(frjb,frje):
    ml = {} 
    for j in range(tojb,toje):
      if fr[i]==to[j]:
        (pw,pl) = uml.get(j-1, (0,0))
        (w,l) = ml[j] = (pw + 1, pl + len(fr[i]))
        if l > ll: (li,lj, lw,ll) = (i-w+1,j-w+1, w,l)
      #else: ml[j] = (0,0) # this reduces performance a lot!
    uml = ml
  return (li,lj, lw)

def gestaltPatternMatches(fr, to):
  sm = difflib.SequenceMatcher(None, fr,to, autojunk=False)
  q = [(0, len(fr), 0, len(to))] # the queue of (frjb,frje, tojb,toje) for recursive longestMatch()
  matches = [] # list of (i,j, w)
  while q:
    (frjb,frje, tojb,toje) = q.pop()
    (i,j, w) = m = sm.find_longest_match(frjb, frje, tojb, toje) # hash-optimized, much faster!
    #(i,j, w) = m = longestMatch(fr,to, frjb,frje, tojb,toje)
    #print('longestMatch({} --> {}) = [{}] '.format(fr[frjb:frje],to[tojb:toje], fr[i:i+w]))
    if not w: continue
    matches.append(m)
    q += [(frjb, i, tojb, j)]
    q += [(i+w, frje, j+w, toje)]
  matches.sort() # sort by i

  #DEBUG: check result
  sl = 0
  for (i,_,w) in matches: 
    for m in fr[i:i+w]: sl += len(m)
  #print('gestaltPatternMatches result: count = {}, ml = {} '.format(len(matches),sl))
  
  matches += [(len(fr),len(to), 0)] # the last pseudo-match
  return matches

def modTag(fr, to):
  tag = ''
  if not fr and not to: tag=''
  elif not to: tag='delete'
  elif not fr: tag='insert'
  else:        tag='replace'
  return tag

def errorMods(mods, fr, to):
  '''Check the list of mods (fr --[(tag, dels,inss, frj,toj)]--> to) for any error.
    Return the list of error(s).
  '''
  errs = []
  for (tag, dels,inss, frj,toj) in mods:
    frs = fr[frj: frj+len(dels)]
    tos = to[toj: toj+len(inss)]
    fra = addr(fr[:frj],1,1)
    toa = addr(to[:toj],1,1)
    if tag != modTag(dels,inss): errs+=['Wrong tag @ {} {}: "{}" for del({}) --> ins({})'.format(frj,fra, tag, len(dels),len(inss))]
    if frs != dels: errs+=['Mismatched del @ {} {}: del:[[[{}]]] <<<>>> frs:[[[{}]]]'.format(frj,fra, dels,frs)]
    if tos != inss: errs+=['Mismatched ins @ {} {}: ins:[[[{}]]] <<<>>> tos:[[[{}]]]'.format(toj,toa, inss,tos)]
  return errs

def applyMods(mods, s, fri0=1,toi0=1, frj0=0,toj0=0, reverse=False, sorted=True, freeAddress=False):
  '''Return the string `to` resulting from applying the list of modifications `mods[]` to the string `s`.
    Each mod is a 5-tuple `(tag, dels,inss, frj,toj)` meaning `s[frj:frj+len(dels)] => to[toj:toj+len(inss)]`.
    - The optional (fri0,toi0, frj0,toj0) can be provided to specified the position (line#, char#) of `s` in the orig text, which will be used in hunk headers.
    - When `reverse==True`, `mods[]` is treated as an inverse function.
    - When `sorted==False`, `mods[]` will sorted before being applied.
    - When `freeAddress==True`, the to-address `toj` won't be checked.
    - If `s` doesn't match some mod[i], a `ValueError('Mismatched mod')` will be raised.
  '''
  if not sorted: mods.sort(key=lambda m: m[3]) # sort by frj
  (frk,tok) = (1,0) if reverse else (0,1)
  oj = 0; fr = s; to = ''
  for mod in mods:
    frs = mod[1+frk]; tos = mod[1+tok]
    frj = mod[3+frk]-frj0; toj = mod[3+tok]-toj0
    if frs != fr[frj:frj+len(frs)]: 
      fra = addr(fr,fri0,1)
      raise ValueError('Mismatched mod @ {} {} @ original: "{}" != "{}"'.format(frj+frj0,fra, frs,fr[frj:frj+len(frs)]))
    to += fr[oj:frj] # append the match
    if not freeAddress and len(to) != toj:
      fra = addr(fr,fri0,1); toa = addr(to,toi0,1)
      raise ValueError('Mismatched mod @ {} {}: mismatched address @ modified text: {} != {} {} '.format(frj+frj0,fra, toj+toj0,len(to)+toj0,toa))
    to += tos # append the mod
    oj = frj + len(frs)
  to += fr[oj:]
  return to

def wordDiff(fr, to, frj0=0, toj0=0, junk_match=JunkWordMatch, bitty_match=0.1, get_matches=gestaltPatternMatches):
  ''' Return a list of mods[i] = (tag, dels,inss, frj,toj) 
    where fr[frj:frj+len(dels)] => to[toj:toj+len(inss)]
    - `frj0` and `toj0` are offsets of the `fr` and `to` text
    - `junk_match(m)` is a function determining if a match string `m` should be discarded so that it won't break the long mods into fragmentary mods.
    - `bitty_match` is the max ratio of a match's str-length to the str-length of the surrounding 2 mods where that match can be ignored because being "too small".
    - `get_matches(fr,to)`: the matching funtion returning a list of matches (i,j, w)
      + gestaltPatternMatches(): gestalt pattern matching (GPM)
      + longestCommonSubsequence(): compact longest common subsequence (CLCS)
  '''
  frw = splitWords(fr); tow = splitWords(to); #print('    fr = {}\n--> to = {}'.format(frw,tow))
  #(i,j,n) = longestMatch(frw,tow)
  #print('===Longest match='+str(frw[i:i+n]))
  '''matches[] contains matches in [match0, mod0, match1, mod1, ..., mod$, match$='']
    ==> At each match, we put its previous mod(frs,tos, frjb[,frje], tojb[,toje]) to mods[]
    The last mod$ is guaranteed by the pseudo last match$=''.
  '''
  frjb = frje = tojb = toje = 0
  frwjb=frwje = towjb=towje = 0
  mods = []; matches = get_matches(frw,tow)
  for i in range(len(matches)):
    (frwje, towje, ws) = matches[i]
    # update (frje,toje) <- (frwje,towje)
    frsw = len(''.join(frw[frwjb:frwje]))
    tosw = len(''.join(tow[towjb:towje]))
    (frje,toje) = (frjb+frsw, tojb+tosw)
    frs = fr[frjb:frje]; tos = to[tojb:toje]
    # skip junk & bitty matches between mods. Warn: this also skip the EOL of whole-line mod!
    junk = ws and junk_match(''.join(frw[frwje:frwje+ws]))
    modlen = frsw + tosw; modplen=0 # length of the mod before and after this match
    #print('matches[{i}] = {m}, ml={ml}, {fs} => {ts} << {ms}'.format(i=i,m=matches[i], ml=modlen, fs=frw[frwjb:frwje],ts=tow[towjb:towje],ms=frw[frwje:frwje+ws]))
    if ws: # not the last match$
      matchp = matches[i+1]
      modplen += len(''.join(frw[frwje+ws:matchp[0]]))
      modplen += len(''.join(tow[towje+ws:matchp[1]]))
      #print('matches[{i}+1] = {m}, ml={ml}, {fs} => {ts} << {ms}'.format(i=i,m=matchp, ml=modplen, fs=frw[frwje+ws:matchp[0]],ts=tow[towje+ws:matchp[1]],ms=frw[matchp[0]:matchp[0]+matchp[2]]))
    bitty = ws and (ws/(modlen+modplen) < bitty_match)
    if modlen and modplen and (junk or bitty): 
      #print('>>>> modlen={} and modplen={} and (junk={} or bitty={})'.format(modlen,modplen, junk,bitty))
      continue
    wholelinefix = ws and frs and fr[frje-1]!='\n' and fr[frje]=='\n' and (frjb==0 or fr[frjb-1]=='\n' or frs.find('\n')>=0)
    if wholelinefix: 
      #print('<< wholelinefix: {fs} => {ts} '.format(fs=frs,ts=tos))
      frs += '\n'; tos += '\n'
      if fr[frjb]=='\n' and tos=='\n': # The whole-line deletion is complicated!
        frs = frs[1:]; tos = tos[1:]
        frjb += 1; tojb += 1
        
    # record the mod --> mods[]
    if frs or tos:
      tag = modTag(frs,tos)
      mods += [(tag, frs,tos, frjb+frj0,tojb+toj0)]
      #print('  {} [{}] ===> [{}]'.format(tag, frs,tos))
    # jump over the match
    (frwjb, towjb) = (frwje+ws, towje+ws)
    frjb = frje + len(''.join(frw[frwje:frwjb]))
    tojb = toje + len(''.join(tow[towje:towjb]))
    #print('  ==['+fr[frje:frjb]+']==')

  ''' DEBUG: verify results using applyMods()
  #fr = fr[:191]+'R'+fr[192:]
  tto = applyMods(mods, fr)
  if tto != to: print('wordDiff verification FAILED: tto != to: len: {} ~ {}'.format(len(tto),len(to)))
  tfr = applyMods(mods, to, reverse=True)
  if tfr != fr: print('wordDiff verification FAILED: tfr != fr: len: {} ~ {}'.format(len(tfr),len(fr)))
  '''
  ''' DEBUG: verify results using mods2Diff()
  diffs,_,tto = mods2Diff(mods, fr)
  pp.pprint(['wordDiff: DIFF #######\n',diffs])
  '''
  return mods

def diff(fr, to, byword=True, wordDiffOpts={'get_matches':gestaltPatternMatches, 'junk_match':JunkWordMatch, 'bitty_match':0.1}):
  '''Return a list of mods[i] = (tag, dels,inss, frj,toj) 
    where fr[frj:frj+len(dels)] => to[toj:toj+len(inss)]
    modify[i] = (tag, dels,inss, frj,toj) where from[frj:frj+len(dels)] => to[toj:toj+len(inss)]
    and each item in delete/insert is ('...', fr_addr,to_addr) and replace is ('...','...', fr_addr,to_addr) where addr = (str_i, line,column)
    - If byword==True, mods are in word level, otherwise, they are in line level.
      Note: For performance, the line diff is always taken first.
    - `wordDiffOpts` are optional params to `wordDiff()`: get_matches, junk_match, bitty_match
    - Return empty list if there's no diff
  '''
  get_matches = wordDiffOpts['get_matches']
  # first, compute line-level diff
  frl = fr.splitlines(True); tol = to.splitlines(True)
  frjb = frje = tojb = toje = 0
  frljb=frlje = toljb=tolje = 0
  lmods = []
  matches = get_matches(frl,tol)
  #matches = get_matches(HashList(frl),HashList(tol)) # much slower than the unhashed!!! :O
  for i in range(len(matches)):
    (frlje, tolje, ls) = matches[i]
    # update (frje,toje) <- (frlje,tolje)
    frsw = len(''.join(frl[frljb:frlje]))
    tosw = len(''.join(tol[toljb:tolje]))
    (frje,toje) = (frjb+frsw, tojb+tosw)
    frs = fr[frjb:frje]; tos = to[tojb:toje]
    if frs or tos: # record the mod --> lmods[]
      tag = modTag(frs,tos)
      lmods += [(tag, frs,tos, frjb,tojb)]
      #print('  {} [{}] ===> [{}]'.format(tag, frs,tos))
    # jump over the match
    (frljb, toljb) = (frlje+ls, tolje+ls)
    frjb = frje + len(''.join(frl[frlje:frljb]))
    tojb = toje + len(''.join(tol[tolje:toljb]))
    #print('  ==['+fr[frje:frjb]+']==')
  ''' DEBUG: verify results using mods2Diff()
  pp.pprint(['diff LINE-MODs\n', lmods])
  diffs,_,tto = mods2Diff(lmods, fr, byword=False)
  if tto != to: print('diff verification FAILED: tto != to: len: {} ~ {}'.format(len(tto),len(to)))
  pp.pprint(['diff: LINE-DIFF #######\n',diffs])
  diffs,_,tfr = mods2Diff(lmods, to, reverse=True, byword=False)
  if tfr != fr: print('diff verification FAILED: tfr != fr: len: {} ~ {}'.format(len(tfr),len(fr)))
  '''
  #print('line-diff: {} mods'.format(len(lmods)))
  if not byword: return lmods
  
  # then, compute word-level diff
  mods = []
  for mod in lmods:
    (tag, frls,tols, frlj,tolj) = mod
    if tag!='replace': mods+=[mod]
    else: mods += wordDiff(frls,tols, frlj,tolj, **wordDiffOpts)

  ''' DEBUG: verify results using mods2Diff()
  pp.pprint(['diff WORD-MODs\n', mods])
  diffs,_,tto = mods2Diff(mods, fr, byword=True)
  if tto != to: print('diff verification FAILED: tto != to: len: {} ~ {}'.format(len(tto),len(to)))
  pp.pprint(['diff: WORD-DIFF #######\n',diffs])
  diffs,_,tfr = mods2Diff(mods, to, reverse=True, byword=True)
  if tfr != fr: print('diff verification FAILED: tfr != fr: len: {} ~ {}'.format(len(tfr),len(fr)))
  '''
  #print('word-diff: {} mods'.format(len(mods)))
  return mods

#### Diff Hunk functions ########################

def parseDiffHeader(diffs):
  '''Return the diff-type and the list of file(s)'''
  header = r'^((diff --'+CONST.DiffTypePat+').*\n)'
  cmdhdr = phdr = difftype = ''; fs = []
  m = re.match(header, diffs)
  if not m: return False
  phdr = m.group(1); cmdhdr = m.group(2); difftype = m.group(3)
  phdr = phdr[len(cmdhdr):]
  fs = shlex.split(phdr)
  return (difftype, fs)

def makeDiffHeader(difftype, fs):
  '''Return the diff header with command "diff --$difftype $fs" and file list "--- fs[0]"..."+++ fs[-1]"'''
  hdr = 'diff --{}'.format(difftype)
  if not fs: return hdr
  hdr += ' {} {}\n'.format(quote(fs[0]),quote(fs[-1]))
  for f in fs[:-1]: hdr += '--- {}\n'.format(quote(f))
  hdr += '+++ {}\n'.format(quote(fs[-1]))
  return hdr

def parseHunkHeader(hunk):
  '''Return 4 numbers and a string (from_line,from_size, to_line,to_size, opt)
    or () if parsing failed.
    If the `opt` is a word-diff address, the tuple (from_j,to_j) will be return instead of a string.
    This function deals with the convention of special size:
    - "empty size" when size==1
    - line is offset by 1 when size==0.
  '''
  pat = re.compile(r'^@@ -(\d+)(,\d+)? \+(\d+)(,\d+)? @@(.*)$', flags=re.MULTILINE)
  m = pat.match(hunk)
  if not m: return ()
  fl = int(m.group(1)); tl = int(m.group(3))
  fs = m.group(2); ts = m.group(4); opt = m.group(5).strip()
  # Uni-diff convention
  fs = int(fs[1:]) if fs else 1
  ts = int(ts[1:]) if ts else 1
  if fs==0: fl+=1
  if ts==0: tl+=1
  # Word-diff address
  pat = re.compile(r'^--(\d+) \+\+(\d+)$')
  m = pat.match(opt)
  if m: opt = (int(m.group(1)), int(m.group(2)))
  return (fl,fs, tl,ts, opt)

def makeHunkHeader(frl,frs, tol,tos, opt=''):
  '''Return a string of hunk header from 4 numbers, and with an optional string or tuple (from_j,to_j)
    This function deals with the convention of special size:
    - "empty size" when size==1
    - line is offset by 1 when size==0.
  '''
  # Uni-diff convention
  frs = str(frs); tos = str(tos)
  frl = int(frl)-1 if frs=='0' else frl
  tol = int(tol)-1 if tos=='0' else tol
  frs = '' if frs=='1' else ','+frs
  tos = '' if tos=='1' else ','+tos
  # Word-diff address
  if type(opt) is tuple:
    (frj,toj) = opt; opt = '--{} ++{}'.format(frj,toj)
  return '@@ -{}{} +{}{} @@ {}\n'.format(frl,frs, tol,tos, opt)

def mods2Diff(mods, s, fri0=1,toi0=1, frj0=0,toj0=0, byword=True, context_lines=0, reverse=False, sorted=True):
  '''Return `(diffs[], fr, to)` where `diffs[]` expresses the list of modifications `mods[]` to the string `s` in word-diff format: `fr` --`diffs`--> `to`. 
    - `diffs[]` is a list of diff hunks with unified hunk header.
    - The optional (fri0,toi0, frj0,toj0) can be provided to specified the position (line#, char#) of `s` in the orig text, which will be used in hunk headers.
    - When `byword==False`, the output will be in unidiff format, and all mods must be in line-unit
      or a ValueError('Invalid line-diff') will be raised.
    - See `applyMods()` for info about params `mods[]`, `reverse`, `sorted`.
  '''
  if not sorted: mods.sort(key=lambda m: m[3]) # sort by frj
  (frk,tok) = (1,0) if reverse else (0,1)

  '''The flows:
    Data flow:
      diffs[] <-- handleHunk() <--> diff <-- flushModl() <-- modl[] <-- mod in wmods[] <--...
                                      ^-- (process full-line mod) <------'
                                      ^-- (process line-diff mod) <------.
                                      ...<-- wmods[] <-- splitMod() <-- mod in mods[]
      (fr,to) <---------------------------------- (apply mod + match) <--'
    Control flow:
      1st loop (mod in mods[]): compute (fr,to) and (wmods[] if byword else diffs[])
      2nd loop (mod in wmods[]): compute diffs[] for word-diff
      Handling modl[]: modl += [mod] for same-line mods, else flushModl() --> diff
      Pushing to `diff`: handleHunk(); diff += ...; (frss,toss) = (...)
      handleHunk(): extendHunk() when gap <= context_lines, else flushHunk() --> diffs[]
      Finally, flushHunk(lastHunk=True) --> diffs[]
  '''

  frl = s.splitlines(True) # frl[0:] == orig_ln[fri0:];  s[frj] == orig[frj+frj0]
  frl+=[''] # the last empty line is for the insertion at the end
  (frli,toli, frlj,tolj) = (0,0, 0,0); fra = (0,1); toa = (0,1)  # frl[frli:fra[0]] == dels of current hunk
  diff = ''; diffs = []; frss = toss = 0 # frss = number of lines of current hunk (`diff`)
  def prepend(pre,ls): # prepend `pre` to each line in `ls[]` then return the joined string
    s = pre.join(ls)
    if s: s = pre + s
    return s
  def extendHunk(pre, fra,toa, firstHunk=False): # using orig (matching) lines to extend `diff` to the current address
    nonlocal diff, frli,frss,frlj, toli,toss,tolj
    #print('>> extendHunk: fr@{}, to@{}'.format(fra, toa))
    li = max(0,fra[0]-context_lines) if firstHunk else frli+frss
    ctx = frl[li: fra[0]]
    diff += prepend(pre,ctx)
    frss += len(ctx); toss += len(ctx)
    if firstHunk: 
      frli = fra[0]-frss;  toli = toa[0]-toss
      frlj = tolj = len(''.join(frl[:frli]));
    #print('>> extendHunk: li={}, @{}\n'.format(li, [(frli,frlj,frss), (toli,tolj,toss)]))
  def flushHunk(pre, fra=(),toa=(), frj=-1,toj=-1): # flush `diff`, as a hunk, into `diffs[]`
    nonlocal diff, diffs, frli,frss,frlj, toli,toss,tolj
    #print('>> flushHunk: fr@{}, to@{}'.format(fra, toa))
    if not diff: return
    ctx = frl[frli+frss: frli+frss + context_lines]
    diff += prepend(pre,ctx)
    frss += len(ctx); toss += len(ctx)
    diffs += [makeHunkHeader(frli+fri0,frss, toli+toi0,toss, (frlj+frj0,tolj+toj0)) + diff]
    #print('>> flushHunk.old: @{} {} '.format([(frli,frlj,frss), (toli,tolj,toss)],'LAST' if not fra else ''))
    if not fra: return # last hunk
    frli = fra[0]-context_lines; frss = context_lines
    toli = toa[0]-context_lines; toss = context_lines
    ctx = ''.join(frl[frli:fra[0]])+frl[fra[0]][:fra[1]-1]
    frlj = frj-len(ctx); tolj = toj-len(ctx)
    diff = prepend(pre,frl[frli:fra[0]])
    #print('>> flushHunk.new: @{}\n'.format([(frli,frlj,frss), (toli,tolj,toss)]))
  def handleHunk(pre, fra=(),toa=(), frj=-1,toj=-1):
    nonlocal diff, diffs, frli,frss,frlj, toli,toss,tolj
    #print('>> handleHunk: @{}, fr@{}, to@{}'.format([(frli,frlj,frss), (toli,tolj,toss)], fra,toa))
    if not fra: flushHunk(pre) # last hunk
    elif not diff: extendHunk(pre, fra,toa, True)
    elif fra[0] > frli + frss + context_lines*2: flushHunk(pre, fra,toa, frj,toj)
    else: extendHunk(pre, fra,toa)

  def tos2Diff(tos):
    return ('> ' if tos else '') + tos.replace('\n','\n#> ')

  modl = [] # the current line of word-diff mods (frs,tos, frj,toj, fra,toa)
  # s[frj] == orig[frj+frj0];  s[frj] ~ frl[fra[0]]
  def flushModl(fra=(), toa=(), frj=-1, toj=-1):
    nonlocal modl, diff
    # handle the last hunk, referencing the first mod in modl[]
    nonlocal diffs, frli,frss,frlj, toli,toss,tolj
    #pp.pprint(modl)
    if modl: (_,_, frj,toj, fra,toa) = modl[0]
    if fra and toa: handleHunk('   ', fra,toa, frj,toj)
    if not modl: return
    # compute diff (frctx+frmrk + tomod)
    ln = frl[modl[0][4][0]]
    frctx = '-! '+ln #; print(frctx)
    frmrk = '-?'; tomod = ''
    (frs,tos, frj,toj, fra,toa) = modl[0]
    if not frs and tos and fra[1]==1 and tos[-1]=='\n':
      fra = (fra[0], 0) # whole-line insert
      modl[0] = (frs,tos, frj,toj, fra,toa)
    for (frs,tos, frj,toj, fra,toa) in modl:
      mrk = CONST.Mod2Mark[modTag(frs,tos)]; mrkl = len(frs) if frs else 1
      #print('s: >{w}s:{m}>{l} frmrk=[{frmrk}]'.format(w=fra[1]-len(frmrk)+2, m=mrk, l=mrkl, frmrk=frmrk))
      frmrk += '{s: >{w}}{s:{m}>{l}}'.format(s='', w=fra[1]-len(frmrk)+2, m=mrk, l=mrkl)
      if not frs: frs = mrk
      else: frs = ' '+frs+('#' if frs[-1]=='\n' else ''); 
      tomod += '#<{}>--{}\n'.format(frs, tos2Diff(tos))
      toss += tos.count('\n') - frs.count('\n')
    # the line tail
    if frctx[-1]!='\n': eolmrk = '!NO_EOL!'; frctx+='\n'; ln+='\n'
    else: eolmrk = '$'
    tailw = len(ln)-len(frmrk)+2+1; 
    #print('s: >{w}{em} frmrk=[{frmrk}]'.format(w=tailw, em=eolmrk, frmrk=frmrk))
    frmrk += '{s: >{w}}{em}\n'.format(s='', w=tailw, em=eolmrk)
    modl = [] # flush modl[]
    diff += frctx+frmrk + tomod
    frss += 1; toss += 1
    #print('>> flushModl: @{}\n'.format([frli,frss, toli,toss]))
  
  wmods = [] # word-diff mods with multi-line mods split to single lines (frs,tos, frj,toj, fra,toa)
  def splitMod(frsl,tosl, frj,toj, fra,toa): # split mod and store result to wmods[]
    nonlocal wmods
    frta = tota = ()
    if len(frsl) > 1: 
      if fra[1] > 1: # head line
        frs = frsl[0]; tos = tosl[0] if tosl else ''
        wmods += [(frs,tos, frj,toj, fra,toa)]; #pp.pprint(['--HEAD--',frs,tos, frj,toj, fra,toa])
        frsl = frsl[1:]; tosl = tosl[1:]
        frj += len(frs); toj += len(tos)
        fra = (fra[0]+1, 1); toa = (toa[0]+(1 if tosl else 0), 1)
      if frsl[-1][-1]!='\n': # tail line
        frts = frsl[-1]; tots = tosl[-1] if tosl else ''
        frsl = frsl[:-1]; tosl = tosl[:-1]
        frta = (fra[0]+len(frsl), 1); tota = (toa[0]+len(tosl), 1)
        frtj = frj+len(''.join(frsl)); totj = toj+len(''.join(tosl))
    if frsl or tosl: # mod body line(s)
      frs = ''.join(frsl); tos = ''.join(tosl)
      wmods += [(frs,tos, frj,toj, fra,toa)]; #pp.pprint(['--body--',frs,tos, frj,toj, fra,toa])
    if frta: wmods += [(frts,tots, frtj,totj, frta,tota)]; #pp.pprint(['--TAIL--',frts,tots, frtj,totj, frta,tota])
  
  oj = 0; fr = to = ''
  for mod in mods:
    frs = mod[1+frk]; tos = mod[1+tok]
    frj = mod[3+frk]-frj0; toj = mod[3+tok]-toj0
    fr += s[oj:frj]; to += s[oj:frj] # append the match
    fra = addr(fr,0,1); toa = addr(to,0,1)
    if frs != s[frj:frj+len(frs)]: 
      fra = (fra[0]+fri0,fra[1])
      raise ValueError('Mismatched mod @ {} {} @ original: "{}" != "{}"'.format(frj+frj0,fra, frs,s[frj:frj+len(frs)]))
    if len(to) != toj:
      fra = (fra[0]+fri0,fra[1]); toa = (toa[0]+toi0,toa[1])
      raise ValueError('Mismatched mod @ {} {}: mismatched address @ modified text: {} != {} {} '.format(frj+frj0,fra, toj+toj0,len(to)+toj0,toa))
    fr += frs; to += tos # append the diff
    oj = frj + len(frs) # update the last pos
    frsl = frs.splitlines(True); tosl = tos.splitlines(True)
    if not byword:
      if not( fra[1]==toa[1]==1
        and (len(frs)==0 or frs[-1]=='\n') and (len(tos)==0 or tos[-1]=='\n')
      ): raise ValueError('Invalid line-diff @ {}: "{}" -> "{}"'.format(fra, frs,tos))
      handleHunk(' ', fra,toa, frj,toj)
      diff += prepend('-',frsl)
      diff += prepend('+',tosl)
      frss += len(frsl); toss += len(tosl)
      continue
    # split multi-line word-diff:
    splitMod(frsl,tosl, frj,toj, fra,toa)
  fr += s[oj:]; to += s[oj:]
  if not byword: 
    flushHunk(' ')
    return (diffs, fr, to)
  
  # word-diff:
  for mod in wmods:
    #print('wmod = {} '.format(mod))
    (frs,tos, frj,toj, fra,toa) = mod
    if fra[1]==1 and (frs and frs[-1]=='\n'): # full-line mod
      flushModl(fra,toa, frj,toj) # flush modl[]
      handleHunk('   ', fra,toa, frj,toj)
      diff += '-'+CONST.Mod2Mark[modTag(frs,tos)]+' ' + frs[:-1].replace('\n','\n-< ')+'\n'
      diff += '#<$>--'+tos2Diff(tos)+'\n'
      frss += frs.count('\n'); toss += tos.count('\n')
      #print('>> full-line mod: @{}\n'.format([frli,frss, toli,toss]))
    elif not modl or(  # empty modl[] <- none-full-line mods
      fra[0]==modl[0][4][0]): # none-empty modl[] <- same-line mod
      modl += [mod]
    elif mod: # next-line mod
      # flush modl[]
      flushModl(fra,toa, frj,toj)
      modl = [mod]
  flushModl() # flush the remaining modl[]
  flushHunk('   ')  # flush the last hunk
  
  return (diffs, fr, to)

def unidiff2mods(hunk, frj=0, toj=0, byword=True, sort=True, wordDiffOpts={'get_matches':gestaltPatternMatches, 'junk_match':JunkWordMatch, 'bitty_match':0.1}):
  '''Return {'header':(...), 'from':'...', 'to':'...', modify:[...], 
      'delete':[...], 'insert':[...], 'replace':[...]}
    where header = (from_line,from_size, to_line,to_size, opt)
    modify[i] = (tag, dels,inss, frj,toj) where from[frj:frj+len(dels)] => to[toj:toj+len(inss)]
    and each item in delete/insert is ('...', fr_addr,to_addr) and replace is ('...','...', fr_addr,to_addr) where addr = (str_i, line,column)
    - (frj,toj) is the char-address of this `hunk`.
    - If byword==True, modify/delete/insert/replace are in word level, otherwise, they are in line level.
    - If sort==True then the (word-level) modify[] will be sorted in positional order.
  '''
  res = {'header':(), 'from':'', 'to':'', 'modify':[], 'delete':[], 'insert':[], 'replace':[]}
  ls = hunk.splitlines(True)
  if not ls: return None
  res['header'] = parseHunkHeader(ls[0])
  if not res['header']: 
    print('unidiff2mods ERROR: ill-formed header "{}" '.format(ls[0]))
    return None
  ls = list(filter(lambda x: x[0] in r' \-+', ls))
  i = 0; fri = res['header'][0]; toi = res['header'][2]
  while i<len(ls):
    while i<len(ls) and ls[i][0]==' ':
      ln = ls[i][1:]
      res['from'] += ln; frj += len(ln) 
      res['to']   += ln; toj += len(ln)
      i+=1; fri+=1; toi+=1
    dels = ''; dd = 0
    while i<len(ls) and ls[i][0] in ['-','\\']:
      if ls[i].find(r'\ No newline at end of file')==0:
        dels = dels[:-1]
        i+=1; break
      elif ls[i][0]=='\\': print('unidiff2mods Error @ line {}: Unrecognized escape "{}"'.format(i+1,ls[i]))
      dels += ls[i][1:]
      i+=1; dd+=1
    res['from'] += dels
    inss = ''; di = 0
    while i<len(ls) and ls[i][0] in ['+','\\']: 
      if ls[i].find(r'\ No newline at end of file')==0:
        inss = inss[:-1]
        i+=1; break
      elif ls[i][0]=='\\': print('unidiff2mods Error @ line {}: Unrecognized escape "{}"'.format(i+1,ls[i]))
      inss += ls[i][1:]
      i+=1; di+=1
    res['to'] += inss
    tag = 'equal'
    if not dels and not inss: continue
    fra = (frj, fri,1); toa = (toj, toi,1)
    if not inss: res['delete'] += [(dels, fra,toa)]; tag = 'delete'
    elif not dels: res['insert'] += [(inss, fra,toa)]; tag = 'insert'
    else: res['replace'] += [(dels,inss, fra,toa)]; tag = 'replace'
    res['modify'] += [(tag, dels,inss, frj,toj)]
    fri+=dd; toi+=di; frj += len(dels); toj += len(inss)
  ''' DEBUG: verify results using mods2Diff()
  pp.pprint(['unidiff2mods LINE-MODs\n', res['modify']])
  diffs,_,tto = mods2Diff(res['modify'], res['from'], byword=False)
  if tto != res['to']: print('unidiff2mods verification FAILED: tto != res[to]: len: {} ~ {}'.format(len(tto),len(res['to'])))
  pp.pprint(['unidiff2mods: LINE-DIFF #######\n',diffs])
  diffs,_,tfr = mods2Diff(res['modify'], res['to'], reverse=True, byword=False)
  if tfr != res['from']: print('unidiff2mods verification FAILED: tfr != res[from]: len: {} ~ {}'.format(len(tfr),len(res['from'])))
  '''
  if not byword: return res
  
  # process word-level diff
  reps = res['replace'].copy(); res['replace'] = []
  res['modify'] = list(filter(lambda x: x[0]!='replace', res['modify'])) 
  for rep in reps:
    #print('Replace::::::::::::::')
    (fr,to, (frj,fri,_), (toj,toi,_)) = rep
    for (tag, frs,tos, frjb,tojb) in wordDiff(fr,to, **wordDiffOpts):
      fra = (frj+frjb, *addr(fr[:frjb], fri,1))
      toa = (toj+tojb, *addr(to[:tojb], toi,1))
      if   tag=='delete': res['delete'] += [(frs, fra,toa)]
      elif tag=='insert': res['insert'] += [(tos, fra,toa)]
      else:              res['replace'] += [(frs,tos, fra,toa)]
      res['modify'] += [(tag, frs,tos, fra[0],toa[0])]
  if not sort: return res

  # sort modifications
  res['modify'].sort(key=lambda m: m[3]) # sort by frj
  res['delete'].sort(key=lambda d: d[1]) # sort by fra
  res['insert'].sort(key=lambda i: i[1]) # sort by fra
  res['replace'].sort(key=lambda r: r[2]) # sort by fra

  ''' DEBUG: verify results using mods2Diff()
  diffs,_,tto = mods2Diff(res['modify'], res['from'])
  if tto != res['to']: print('unidiff2mods verification FAILED: tto != res[to]: len: {} ~ {}'.format(len(tto),len(res['to'])))
  pp.pprint(['unidiff2mods: WORD-DIFF #######\n',diffs])
  '''
  return res

def worddiff2mods(hunk, junk_match=WordSeparatorMatch):
  '''Return {'header':(...), 'from':'...', 'to':'...', modify:[...], 
      'delete':[...], 'insert':[...], 'replace':[...]}
    where header = (from_line,from_size, to_line,to_size, opt)
    modify[i] = (tag, dels,inss, frj,toj) where from[frj:frj+len(dels)] => to[toj:toj+len(inss)]
    and each item in delete/insert is ('...', fr_addr,to_addr) and replace is ('...','...', fr_addr,to_addr) where addr = (str_i, line,column)
  '''
  res = {'header':(), 'from':'', 'to':'', 'modify':[], 'delete':[], 'insert':[], 'replace':[]}
  ls = hunk.splitlines(True)
  if not ls: return None
  res['header'] = parseHunkHeader(ls[0])
  if not res['header'] or type(res['header'][4]) is not tuple: 
    print('worddiff2mods ERROR: ill-formed word-diff header "{}" '.format(ls[0]))
    return None
  ls = list(filter(lambda x: x[0] in ' -#', ls))
  fri0 = res['header'][0]; toi0 = res['header'][2]
  frj0 = res['header'][4][0]; toj0 = res['header'][4][1]
  (fri,toi) = (fri0,toi0); (frj,toj) = (frj0,toj0)
  i = 0
  def mergeMod(dels,inss):
    nonlocal toj
    if not res['modify']: return False
    (ptag, pdels,pinss, pfrj,ptoj) = pmod = res['modify'][-1]
    if ptag=='insert' and dels==inss: return False # don't merge junks into insertion, because it'll change 'insert' --> 'replace' and make those junks ambiguous between "before" and "after" the insertion
    #print('Merge mod @ {}: [{}] + [{}] --> [{}] + [{}] '.format((mfj,mfi,mj), pdels,dels,pinss,inss))
    dels = pdels+dels; inss = pinss+inss; tag = modTag(dels,inss)
    res['modify'][-1] = (tag, dels,inss, pfrj,ptoj); toj = ptoj+len(inss)
    return True
  
  # process hunk --> res['modify']
  while i<len(ls):
    while i<len(ls) and ls[i][0:3]=='   ':
      ln = ls[i][3:]
      res['from'] += ln; frj+=len(ln) 
      res['to']   += ln; toj+=len(ln)
      i+=1; fri+=1; toi+=1
  
    # collect dels into modl[]
    modl = [] # [(tag, dels,frj,fra(i,j))]
    while i<len(ls) and ls[i][0]=='-':
      #print('ls[{}]:[{}] '.format(i+1,ls[i]))
      dels = ''; di = 0
      if ls[i][0:2] in ['--','-#']: 
        tag = 'delete' if ls[i][1]=='-' else 'replace'
        dels+=ls[i][3:]; di+=1; i+=1
        while i<len(ls) and ls[i][0:2]=='-<': 
          dels+=ls[i][3:]; di+=1; i+=1
        modl+=[(tag,dels,frj,fri,1)]
        res['from']+=dels; frj+=len(dels); fri+=di
      elif ls[i][0:2]=='-!': 
        if ls[i+1][0:2]=='-?': 
          ln = ls[i][2:]; ex = ls[i+1][2:]; i+=2; j = 0
          #print('ls[{}]:ex[{}] '.format(i,ex))
          while j<len(ex) and ex[j] not in '$\n':
            mrk = ex[j]
            tag = 'equal' if mrk==' ' else 'insert' if mrk=='^' else 'delete' if mrk=='-' else 'replace' if mrk=='#' else 'comment' if mrk=='!' else ''
            if not tag: print('worddiff2mods Error: line {}: unrecognized mod marker "{}"'.format(i, mrk))
            jb = j if j else 1; j+=1
            if mrk in '^ ': # insert then equal
              if tag=='insert': modl+=[(tag,'',frj,fri, jb)]
              if ex[j]!='!':
                tag = 'equal'
                while j<len(ex) and ex[j]==' ': j+=1                
                dels = ln[jb:j]
                if dels: modl+=[(tag,dels,frj,fri,jb)]; frj+=len(dels)
            elif mrk=='!': # comment
              cmnt = ''
              while j<len(ex) and ex[j] not in '$\n': 
                if ex[j]=='!': j+=1; break
                cmnt+=ex[j]; j+=1
              if cmnt=='NO_EOL':
                ln = ln[:-1]
              print('worddiff2mods Comment: line {}: {} '.format(i, cmnt))
              continue
            else: # delete/replace
              while j<len(ex) and ex[j]==mrk: j+=1
              dels = ln[jb:j]; modl+=[(tag,dels,frj,fri,jb)]; frj+=len(dels)
        else: print('worddiff2mods Error: line {}: mix-mod line without explanation line ({})'.format(i+1, ls[i]))
        res['from']+=ln[1:]; fri+=1
      else: print('worddiff2mods Error: line {}: unrecognized line mod marker "{}"'.format(i+1, ls[i][0:2]))
    #pp.pprint(modl)
    
    # process inss corresponding to mods in modl[]
    omod = ()
    for mod in modl:
      (tag,dels, mfj,mfi,mj) = mod
      #DEBUG check address
      mfa = addr(res['from'][:mfj-frj0], fri0,1)
      if mfa!=(mfi,mj):
        print('worddiff2mods Error: mfa{} != {} <<<[{}] '.format(mfa,(mfi,mj),res['from'][:mfj-frj0]))
      #print('  -->{} @ line {} '.format(mod,i+1))
      if tag=='equal': # skip the match, or merge junk match with the pevious mod
        res['to']+=dels; merged = False
        if omod and omod[0]!='equal' and junk_match(dels): merged = mergeMod(dels,dels)
        if not merged: toj+=len(dels)
        omod = mod; continue
      frs = ' '+dels
      if not dels: frs='^'
      elif mj==1 and dels[-1]=='\n': frs='$'
      frs = '#<'+frs+('>' if frs[-1]!='\n' else '')
      j = len(frs)
      if ls[i][0:j] != frs: print('worddiff2mods Error: line {}: mismatched dels "{}" != "{}"'.format(i+1, ln[0:j],frs))
      if frs[-1]=='\n': i+=1; j = 2
      if i>=len(ls) or ls[i][j:j+2] != '--': print('worddiff2mods Error: line {}: ill formed dels: missing "--"'.format(i+1))
      else: j+=2
      if tag=='delete': 
        if ls[i][j] != '\n': print('worddiff2mods Error: line {}: ill formed deletion: --{} '.format(i+1,ls[i][j]))
        inss = ''; i+=1
      else:
        j+=2; inss = ls[i][j:-1]; i+=1
        while i<len(ls) and ls[i][0:3]=='#> ': 
          inss+='\n'+ls[i][3:-1]; i+=1
      res['to']+=inss
      # register this mod, or merge with the previous mod
      merged = False
      if res['modify']:
        (ptag, pdels,pinss, pfrj,ptoj) = pmod = res['modify'][-1]
        if bool(pfrj+len(pdels)==mfj) != bool(ptoj+len(pinss)==toj):
          print('worddiff2mods Error: mismatched mod address {} + {} - {} != {} + {} - {}: [{}]-->[{}] '.format(pfrj,len(pdels),mfj, ptoj,len(pinss),toj, pdels,pinss))
        if pfrj+len(pdels)==mfj: merged = mergeMod(dels,inss)
      if not merged: res['modify']+=[(tag, dels,inss, mfj,toj)]; toj+=len(inss)
      omod = mod
    #pp.pprint(res)
    #if i>10: break

  # process res['modify'] --> res['delete','insert','replace']
  for mod in res['modify']:
    (tag, dels,inss, frj,toj) = mod
    fra = (frj, *addr(res['from'][:frj-frj0], fri0,1))
    toa = (toj, *addr(res['to'][:toj-toj0], toi0,1))
    if   tag=='delete': res['delete']+=[(dels, fra,toa)]
    elif tag=='insert': res['insert']+=[(inss, fra,toa)]
    else:              res['replace']+=[(dels,inss, fra,toa)]
    
  return res

def splitHunks(diffs, header = r'^(@@ -\d+(?:,\d+)? \+\d+(?:,\d+)? @@.*)$'):
  '''Split a diff file into individual hunks, where the #0 hunk is the diff header
  '''
  hunkpat = re.compile(header, flags=re.MULTILINE)
  hss = hunkpat.split(diffs)
  # process the diff header
  phdr = ''
  for hl in hss[0].splitlines(True): # filter out extended header lines
    if re.match(r'^(diff --|--- |\+\+\+ )', hl): phdr += hl
  hs = [phdr]
  # collect the pairs of (hunk header + hunk body)
  for i in range(len(hss)//2): hs.append(hss[1+i*2]+hss[1+i*2+1])
  return hs

def splitPatch(patch, byhunk=False, pre=1, header = r'diff --'+CONST.DiffTypePat):
  '''Split a multiple-file patch (string) into single-file diffs indexed by orig file path
    and optionally further into individual hunks
    - `pre` is the number of prefix level(s) to be stripped off from the file name
  '''
  headerr = header+r'[^\n]*\n'
  ps = {}; phdr = f = ''
  for p in re.split('^('+headerr+')', patch, flags=re.MULTILINE):
    #print('splitPatch<<<[[[{}]]]\n  phdr=[{}]'.format(p,phdr))
    if not p.strip(): continue # skip the first empty match before diff header
    if re.fullmatch(CONST.DiffTypePat, p): continue # skip the diff-type match
    m = re.fullmatch(headerr, p) # catch headerr --> phdr
    if m: phdr = p; continue
    # process diff header to get the file name := the last file path - pre
    (dt,fs) = parseDiffHeader(phdr)
    if fs: 
      fl = fs[-1].split('/'); f = '/'.join(fl[pre:])
    else: f = 'file#{}'.format(len(ps)+1)
    p = phdr + p # restore the diff header 

    if not byhunk: ps[f] = p
    else: ps[f] = splitHunks(p)
  return ps

def diffFile(frfn, tofn, context_lines=1, byword=True, wordDiffOpts={'get_matches':gestaltPatternMatches, 'junk_match':JunkWordMatch, 'bitty_match':0.1}):
  '''Return the full text of a diff file diffing from 2 files with names `frfn` & `tofn`
    - Return empty string if there's no diff
  '''
  difftype = 'worddiff' if byword else 'unidiff'
  header = makeDiffHeader(difftype, [frfn,tofn])
  with fopen(frfn) as f: fr = f.read()
  with fopen(tofn) as f: to = f.read()
  mods = diff(fr,to, byword=byword, wordDiffOpts=wordDiffOpts)#; pp.pprint(mods)
  if not mods: return ''
  hunks,_,_ = mods2Diff(mods, fr, byword=byword, context_lines=context_lines)
  return header + ''.join(hunks)
  
def applyDiff(hunks, s, reverse=False, byword=True, wordDiffOpts={'get_matches':gestaltPatternMatches, 'junk_match':JunkWordMatch, 'bitty_match':0.1}):
  '''Return the string `to` resulting from applying the diff `hunks[]` to the string `s`.
    When `reverse==True`, `hunk` is treated as an inverse function.
    If `s` doesn't match some mod in `hunks[]`, a `ValueError('Mismatched mod')` will be raised.
  '''
  (frk,tok) = (1,0) if reverse else (0,1)
  fr = s; to = ''
  frl = s.splitlines(True); tol = []
  oi = 0
  for hunk in hunks:
    hdr = parseHunkHeader(hunk)
    if not hdr: continue
    (fri,frn, toi,ton, opt) = (hdr[frk*2+0]-1,hdr[frk*2+1], hdr[tok*2+0]-1,hdr[tok*2+1], hdr[4])
    tol+=frl[oi:fri]; to+=''.join(frl[oi:fri]) # append the match
    frj = len(''.join(frl[:fri])); toj = len(to)
    if type(opt) is tuple and (opt[frk],opt[tok]) != (frj,toj):
      raise ValueError('Mismatched hunk @ {}: mismatched address {} != {} '.format(fri, (opt[frk],opt[tok]), (frj,toj)))
    if byword: mods = worddiff2mods(hunk)  
    else: mods = unidiff2mods(hunk, frj,toj, byword, wordDiffOpts)
    frs = mods['from']; tos = mods['to']
    if reverse: frs,tos = tos,frs
    frss = ''.join(frl[fri:fri+frn])
    if frs != frss: raise ValueError('Mismatched hunk @ {}: length {} != {} '.format(fri, len(frs),len(frss)))
    #print('Hunk {} --> [[[{}]]] '.format((fri,frn, toi,ton, opt),tos))
    to+=tos; tol+=tos.splitlines(True) # append the mod
    oi = fri+frn
  to+=''.join(frl[oi:])
  return to

def mergeDiff(txt, d1, d2, d1type='diff', d2type='diff', otype = 'hunks', byword=True, wordDiffOpts={'get_matches':gestaltPatternMatches, 'junk_match':JunkWordMatch, 'bitty_match':0.1}):
  '''Merge txt + d1 + d2 to (mtxt, md, conflict, ids), where
    - `mtxt` and `md` is merged text and diff, 
    - `conflict` = (cd1, cd2) contains the remaining mods in `d1`, `d2`
    - `ids` is the list of idential mods between d1 and d2
    - d{1,2}type in ['txt', 'diff', 'hunks', 'mods'] is the type of `d1`, `d2`
    - otype in ['hunks', 'mods'] is the type of `md`, `cd1`, `cd2`, and `ids`
    Diff relation:
      ┌--[d1]--> d1txt -----------↘┌--[cd1]--> md1txt 
      txt -----------[md ⊃ ids]--> mtxt
      └--[d2]--> d2txt -----------↗└--[cd2]--> md2txt
  '''
  import pprint
  pp = pprint.PrettyPrinter(sort_dicts=False, indent=2, width=120)
  #print('\nd1 = '); pp.pprint(d1)
  #print('\nd2 = '); pp.pprint(d2)
  mtxt = ''; md = [] # merged text and diff
  conflict = (); cd1 = []; cd2 = []; md1txt = md2txt = '' # conflict diff and text
  ids = [] # identical diff
  junk_match = wordDiffOpts['junk_match']
  def getMods(d,t): # mods <-- hunks <-- diff <-- txt
    mods = []
    if t=='txt': mods = diff(txt, d, byword, wordDiffOpts)
    elif t!='mods': # extract mods
      if t=='diff': # extract hunks
        d = splitHunks(d)[1:]
      for hunk in d:
        df = worddiff2mods(hunk, junk_match) if byword else unidiff2mods(hunk, wordDiffOpts=wordDiffOpts)
        mods += df['modify']
    return mods
  d1 = getMods(d1,d1type); d2 = getMods(d2,d2type)
  #print('\nd1mods = '); pp.pprint(d1)
  #print('\nd2mods = '); pp.pprint(d2)
  d1txt = applyMods(d1, txt, freeAddress=False); d2txt = applyMods(d2, txt, freeAddress=False)
  # ^-- apply (d1,d2) to check for their applicablility so that we don't need to check (frj,toj) any more
  #print('\nd1txt = [[[{}]]]'.format(d1txt))
  #print('\nd2txt = [[[{}]]]'.format(d2txt))

  '''
    Data flow:
      d1 = [.........d1[i](*,frj,toj)...]      ┌---------------------> (cd1,md1txt) 
      |               ↑ ↑      ↑               |[t='conflict']
      ├--> mmods[...(dx,i,t, frj)...] --[txt]--├[t='discrete','id']--> (md,ids,mtxt)
      |               ↓ ↓      ↓..........^    |[t='conflict']
      d2 = [.........d2[i](*,frj,toj)...]      └---------------------> (cd2,md2txt)
    where:
               ┌----------------------> cd1[(*,frj,toj)] --> md1txt
               |                                 ↓   └.........^
      --[txt]--├--> (md,ids)[(*,frj,toj)] --> mtxt
           ^......................┘   └........^ ↑   ┌.........⌄
               └----------------------> cd2[(*,frj,toj)] --> md2txt
  '''
  mmods = [] # := d1 + d2 = [(t,frj,dx,dxm)] where t in ['discrete','id','conflict'], dx in ['d1','d2'], dxm = mod in dx[]
  for dxm in d1: mmods+=[('',dxm[3],'d1',dxm)]
  for dxm in d2: mmods+=[('',dxm[3],'d2',dxm)]
  mmods.sort(key=lambda m: m[1]) # sort by frj
  om = (); ofrje = -1; odx = ''
  for mi in range(len(mmods)): # find conflicts & ids vs discrete to fill in mmods[(t,*)]
    (t,frj,dx,dxm) = mmods[mi]
    (tag, frs,tos, frj,toj) = dxm
    if om[:-1]==dxm[:-1]: t = 'id'; mmods[mi-1] = ('',*mmods[mi-1][1:])
    elif ofrje < 0 or odx==dx or frj > ofrje and not junk_match(txt[ofrje:frj]): t = 'discrete' # only temporarily, in relation to the prev. mod! Can be 'id' or 'conflict' in relation to the next mod  
    else: t = 'conflict'; mmods[mi-1] = (t,*mmods[mi-1][1:])
    mmods[mi] = (t,frj,dx,dxm)
    if ofrje < frj + len(frs): ofrje = frj + len(frs); om = dxm; odx = dx
  #print('\nmmods = '); pp.pprint(mmods)
  for (t,frj,dx,dxm) in mmods: # split mmods[] --> (cd1,cd2), (md,ids), whose (frj,toj) will be updated later
    if not t: continue
    elif t=='conflict': 
      if dx=='d1': cd1+=[dxm]
      else: cd2+=[dxm]
    else:
      md+=[dxm]
      if t=='id': ids+=[dxm]
  #print('\nmmods:md = '); pp.pprint(md)
  #print('\nmmods:ids = '); pp.pprint(ids)
  #print('\nmmods:cd1 = '); pp.pprint(cd1)
  #print('\nmmods:cd2 = '); pp.pprint(cd2)

  '''
    merged:[ match ][  mod  ][             match                    ][  mod  ][ match
    txt  :..oj......frj:[frs]|oj.....................................frj:[frs]|oj....
    mtxt :.........toj':[tos]|omj...................................toj':[tos]|omj...
    conflict d1:             [--------[cd1  mod]--------------------]          
    txt  :..oj......frj:[frs]|oj.......frj:[frs]|oj..................frj:[frs]|oj....
    mtxt :.........toj':[tos]|omj.....frj":[frs]|omj................toj':[tos]|omj...
    d1txt:............................toj":[tos].....................................
    mtxt :.........toj':[tos]|omj.........frj":[frs]|omj............toj':[tos]|omj...
    d2txt:................................toj":[tos].................................
    conflict d2:             [------------[cd2  mod]----------------]            
  '''
  md+=[('','','', len(txt),-1)] # the tail-end pseudo mod
  oj = omj = 0; i1 = i2 = 0
  for i in range(len(md)): # process 'discrete','id' (toj' ..> mtxt) and 'conflict' (mtxt <.. frj")
    (tag, frs,tos, frj,toj) = md[i]
    mtxt += txt[oj:frj] # append the match
    toj = len(mtxt); md[i] = (*md[i][:4],toj) # update toj' ..> mtxt
    while i1 < len(cd1) and cd1[i1][3] < frj: # update mtxt <.. frj"
      cd1[i1] = (*cd1[i1][:3], omj+cd1[i1][3]-oj,-1); i1+=1 
    while i2 < len(cd2) and cd2[i2][3] < frj: # update mtxt <.. frj"
      cd2[i2] = (*cd2[i2][:3], omj+cd2[i2][3]-oj,-1); i2+=1 
    mtxt += tos # append the mod
    oj = frj + len(frs); omj = toj + len(tos)
  md = md[:-1] # remove the tail-end pseudo mod
  #print('\nmtxt = [[[{}]]]'.format(mtxt))
  #print('\nmd = '); pp.pprint(md)
  #print('\nids = '); pp.pprint(ids)
  #print('\ncd1 pre = '); pp.pprint(cd1)
  #print('\ncd2 pre = '); pp.pprint(cd2)

  def processCD(cdx):
    omj = 0; cdxtxt = ''; cdxn = 'cd1' if cdx==cd1 else 'cd2'
    for i in range(len(cdx)): # process 'conflict' (cdx: toj" ..> cdxtxt)
      (tag, frs,tos, frj,toj) = cdx[i]
      cdxtxt += mtxt[omj:frj] # append the match
      if frs != mtxt[frj:frj+len(frs)]: 
        fra = addr(mtxt[:frj],1,1)
        raise ValueError('Mismatched mod @ {} {}: original text of {}: [{}] <<<>>> [{}]'.format(frj,fra, cdxn, frs,mtxt[omj:frj]))
      toj = len(cdxtxt); cdx[i] = (*cdx[i][:4],toj) # update toj ..> cdxtxt
      if toj != len(cdxtxt):
        fra = addr(mtxt[:frj],1,1); toa = addr(cdxtxt,1,1)
        raise ValueError('Mismatched mod @ {} {}: mismatched address of modified text: {} != {} {}'.format(frj,fra, toj,len(cdxtxt),toa))
      cdxtxt += tos # append the mod
      omj = frj + len(frs)
    cdxtxt += mtxt[omj:] # append the tail match
    return cdxtxt
  md1txt = processCD(cd1); md2txt = processCD(cd2)
  if otype=='hunks':
    md = mods2Diff(md, txt, byword=byword, context_lines=0)[0]
    cd1 = mods2Diff(cd1, mtxt, byword=byword, context_lines=0)[0]
    cd2 = mods2Diff(cd2, mtxt, byword=byword, context_lines=0)[0]
    #CANNOT! ids = mods2Diff(ids, txt, byword=byword, context_lines=0)[0] # ids is not a complete diff
  #print('\ncd1 = '); pp.pprint(cd1)
  #print('\ncd2 = '); pp.pprint(cd2)
  #print('\nmd1txt = [[[{}]]]'.format(md1txt))
  #print('\nmd2txt = [[[{}]]]'.format(md2txt))

  if cd1 or cd2: conflict = (cd1,cd2) 
  return (mtxt, md, conflict, ids)

#### Testing functions ########################

def test_diffAlgos():
  '''
    ### Neat example with LCS = CLCS = GPM = unique CLS!
    #fr   = 'word.diff.lib'
    #to   = 'word-level.difference.library'
    #LCS  = 'word      .diff      .lib    '
    ### Head overlaps Tail:
    #fr   = 'register.something'
    #to   = 'register.custom.integer.something'
    #LCS  = 'regi       s      t  er.something'
    #CLCS = 'regist               er.something'
    #GPM  = 'regist               er.something'
    #diff = 'register.               something' #Git == BusyBox
    ### CLCS = GPM:
    #fr   = 'string.matching.algorithm'
    #to   = 'longest.substring.in.gestalt.pattern.matching'
    #LCS  = '           str    in g              .matching'
    #CLCS = '           string                   .matching'
    #GPM  = '           string                   .matching'
    #diff = '           string.in.    al       r    t h   ' #Git, GNU's diffutils
    #diff = '     st      ring.in.    al       r    t h   ' #BusyBox
    ### CLCS better than GPM (GPM ~ LCS!)
    #fr   = 'microcosm'
    #to   = "microwave.background.of.the.cosmos.in.microcomputer's.memory"
    #LCS  = '                                      microco       s   m   '
    #CLCS = 'micro                       cosm                            ' # == Git
    #GPM  = '                                      microco       s m     '
    #diff = 'micro       c   o             sm                            ' #BusyBox
    ### CLCS and CLS better than GPM
    #fr   = 'microcosm-macrocosm'
    #to   = "microwave.background.of.the.cosmos.in.microcomputer's.memory"
    #LCS  = 'mi          c  r     o      cosm      m croco       s   m   '
    #CLCS = 'micro                       cosm      m croco       s   m   ' # == Git
    #GPM  = '                                      microco       s m m r ' #Python
    #diff = 'micro       c   o             sm      m croco       s m     ' #BusyBox (Hunt–Szymanski algorithm)
    #diff = 'micro                                                       ' #WinDiff
  '''
  #     012345678901234567890123456789012345678901234567890123456789
  #fr   = 'm i c r o c o s m - m a c r o c o s m '
  #to   = "m i c r o w a v e . b a c k g r o u n d . o f . t h e . c o s m o s . i n . m i c r o c o m p u t e r ' s . m e m o r y "
  fr   = 'register.something'
  to   = 'register.custom.integer.something'
  #fr   = 's t r i n g . m a t c h i n g . a l g o r i t h m '
  #to   = "l o n g e s t . s u b s t r i n g . i n . g e s t a l t . p a t t e r n . m a t c h i n g "
  #     01234567890123456789012345678901234567890123456789012345678901
  (frl,tol) = (fr,to)
  matches = longestCommonSubsequence(frl,tol); print('longestCommonSubsequence:')
  for m in matches:
    (i,j,w) = m
    print('  [{}]\n==[{}] {}'.format(frl[i:i+w],tol[j:j+w], m))
  matches = gestaltPatternMatches(frl,tol); print('gestaltPatternMatches:')
  for m in matches:
    (i,j,w) = m
    print('  [{}]\n==[{}] {}'.format(frl[i:i+w],tol[j:j+w], m))

def test_wordDiff_mods2Diff():
  #fn = 'test/difflib-algorithm-test'
  fn = 'test/difflib-hunk-test'
  with fopen(fn+'.txt') as f: txt = f.read()
  with fopen(fn+'-diffed.txt') as f: diffed = f.read()
  ls = txt.splitlines(True); fri = 3; frj = len(''.join(ls[:fri-1]))
  mods = wordDiff(txt[frj:],diffed[frj:], frj,frj, junk_match=WordSeparatorMatch, bitty_match=0.0,
    get_matches=gestaltPatternMatches) # WordSeparatorMatch JunkWordMatch, 0.1, 
  print('mods = wordDiff(gestaltPatternMatches, {fn}.txt, {fn}-diffed.txt): '.format(fn=fn)); pp.pprint(mods)

  diffhdr = makeDiffHeader('worddiff',[fn+'.txt',fn+'-diffed.txt'])
  diffs,_,_ = mods2Diff(mods, txt[frj:], fri,fri, frj,frj, byword=True, context_lines=1)
  f = fopen(fn+'.word.diff','w')
  f.write(diffhdr + ''.join(diffs))
  print('\nSuccessfully wrote Gestalt word-diff to "{}.word.diff"\n'.format(fn))

  mods = wordDiff(txt[frj:],diffed[frj:], frj,frj, junk_match=WordSeparatorMatch, bitty_match=0.0,
    get_matches=longestCommonSubsequence) # WordSeparatorMatch JunkWordMatch, 0.1, 
  print('mods = wordDiff(longestCommonSubsequence, {fn}.txt, {fn}-diffed.txt): '.format(fn=fn)); pp.pprint(mods)

  diffs,_,_ = mods2Diff(mods, txt[frj:], fri,fri, frj,frj, byword=True, context_lines=1)
  f = fopen(fn+'.LCS.word.diff','w')
  f.write(diffhdr + ''.join(diffs))
  print('\nSuccessfully wrote LCS word-diff to "{}.LCS.word.diff"\n'.format(fn))

def test_unidiff2mods_mods2Diff():
  fn = 'test/difflib-hunk-test'
  with fopen(fn+'.diff') as f: diff = f.read()
  with fopen(fn+'.txt') as f: txt = f.read(); frl = txt.splitlines(True)
  with fopen(fn+'-diffed.txt') as f: diffed = f.read(); tol = diffed.splitlines(True)
  hs = splitHunks(diff)
  diffhdr = hs[0]; hn = 1; hunk = hs[hn]
  (fri,frn, toi,ton, opt) = parseHunkHeader(hunk)
  (frj,toj) = (len(''.join(frl[:fri-1])),len(''.join(tol[:toi-1])))
  (frs,tos) = (''.join(frl[fri-1:fri-1+frn]),''.join(tol[toi-1:toi-1+ton]))
  mods = unidiff2mods(hunk, frj,toj, byword=True, wordDiffOpts={"junk_match":WordSeparatorMatch, "bitty_match":0.0, 'get_matches':gestaltPatternMatches})
  print('mods = unidiff2mods({}/[hunk #{}]): '.format(fn,hn)); pp.pprint(mods)
  print('Header = {} {} '.format(mods['header'],(frj,toj)))
  if mods['from'] != frs: print('unidiff2mods ERROR: mismatched original text {} ~ {} '.format(len(mods['from']),len(frs)))
  if mods['to'] != tos: print('unidiff2mods ERROR: mismatched modified text {} ~ {} '.format(len(mods['to']),len(tos)))
  errs = errorMods(mods['modify'], txt,diffed)
  if errs: print('unidiff2mods ERROR: list of error mods:'); pp.pprint(errs)

  diffs,_,_ = mods2Diff(mods['modify'], frs, fri,toi, frj,toj, byword=True, context_lines=1)
  f = fopen(fn+'.diff.word.diff','w'); diffhdr = makeDiffHeader('worddiff',[fn+'.txt',fn+'-diffed.txt'])
  f.write(diffhdr + ''.join(diffs))
  print('\nSuccessfully wrote word-diff to "{}.diff.word.diff"'.format(fn))

def test_worddiff2mods_applyMods():
  fn = 'test/difflib-hunk-test'; dfn = fn+'.word.diff'
  with fopen(dfn) as f: diff = f.read()
  with fopen(fn+'.txt') as f: txt = f.read(); frl = txt.splitlines(True)
  with fopen(fn+'-diffed.txt') as f: diffed = f.read(); tol = diffed.splitlines(True)
  '''fn = 'chrome/common/chrome_paths_mac.mm'; dfn = 'test.patch'
  with fopen(dfn) as f: diff = f.read()
  with fopen('original/'+fn) as f: txt = f.read(); frl = txt.splitlines(True)
  with fopen('patched/'+fn) as f: diffed = f.read(); tol = diffed.splitlines(True)
  '''
  hs = splitHunks(diff)
  hn = 2; hunk = hs[hn]
  mods = worddiff2mods(hunk); (fri,frn, toi,ton, (frj,toj)) = (mods['header'])
  print('mods = worddiff2mods({}/[hunk #{}]): '.format(dfn,hn)); pp.pprint(mods)
  print('Header = {} {} '.format(mods['header'],(frj,toj)))
  (frs,tos) = (''.join(frl[fri-1:fri-1+frn]),''.join(tol[toi-1:toi-1+ton]))
  if mods['from'] != frs: print('worddiff2mods ERROR: mismatched original text {} ~ {} '.format(len(mods['from']),len(frs)))
  if mods['to'] != tos: print('worddiff2mods ERROR: mismatched modified text {} ~ {} '.format(len(mods['to']),len(tos)))
  errs = errorMods(mods['modify'], txt,diffed)
  if errs: print('worddiff2mods ERROR: list of error mods:'); pp.pprint(errs)

  ttos = applyMods(mods['modify'], frs, fri,toi, frj,toj)
  if ttos != tos: print('applyMods ERROR: mismatched modified text {} ~ {} '.format(len(ttos),len(tos)))
  tfrs = applyMods(mods['modify'], tos, toi,fri, toj,frj, reverse=True)
  if tfrs != frs: print('applyMods ERROR: mismatched original text {} ~ {} '.format(len(tfrs),len(frs)))
  f = fopen(dfn+'.from.txt','w'); f.write(mods['from'])
  f = fopen(dfn+'.to.txt','w'); f.write(mods['to'])
  print('\nWrote original & modified text to "{fn}.from.txt" and "{fn}.to.txt"'.format(fn=dfn))

def test_wordDiffFile(frf,tof):
  # WARN: overflow for long texts!
  with fopen(frf) as f: txt = f.read()
  with fopen(tof) as f: diffed = f.read()
  mods = wordDiff(txt, diffed, junk_match=WordSeparatorMatch, bitty_match=0.0,
    get_matches=longestCommonSubsequence) # WordSeparatorMatch JunkWordMatch, 0.1, gestaltPatternMatches
  #print('mods = wordDiff({}, {}): '.format(frf,tof)); pp.pprint(mods)
  print('diff({}, {}): {} mods, size = {} '.format(frf,tof, len(mods),sys.getsizeof(mods)))

  fn = 'test/difflib-file-result.diff'; diffhdr = makeDiffHeader('worddiff',[frf,tof])
  diffs,_,_ = mods2Diff(mods, txt, byword=True, context_lines=1)
  f = fopen(fn,'w')
  f.write(diffhdr+''.join(diffs))
  print('\nSuccessfully wrote to {} \n'.format(fn))

def test_diffFile(frf,tof):
  fn = 'test/difflib-file-result.diff'
  df = diffFile(frf,tof, context_lines=1, byword=True, get_matches=gestaltPatternMatches, wordDiffOpts={
    'junk_match':WordSeparatorMatch, 'bitty_match':0.0}) # WordSeparatorMatch JunkWordMatch, gestaltPatternMatches longestCommonSubsequence
  print('diff({}, {}): {} mods, size = {} ({} chars) '.format(frf,tof, df.count('\n#<'),sys.getsizeof(df),len(df)))
  f = fopen(fn,'w')
  f.write(df)
  print('\nSuccessfully wrote to {} \n'.format(fn))

def test_applyDiff(frf,tof):
  fn = 'test/difflib-file-result.diff'
  with fopen(fn) as f: diff = f.read()
  with fopen(frf) as f: txt = f.read(); frl = txt.splitlines(True)
  with fopen(tof) as f: diffed = f.read(); tol = diffed.splitlines(True)
  hs = splitHunks(diff)
  tdiffed = applyDiff(hs, txt)
  if tdiffed != diffed: print('applyDiff ERROR: mismatched modified text {} <> {}: '.format(len(diffed),len(tdiffed)))#; pp.pprint(tdiffed)
  else: print('applyDiff OK: txt({}) --> diffed({})'.format(len(txt),len(tdiffed)))
  ttxt = applyDiff(hs, diffed, reverse=True)
  if ttxt != txt: print('applyDiff ERROR: mismatched original text {} <> {} '.format(len(txt),len(ttxt)))
  else: print('applyDiff reverse OK: diffed({}) --> txt({})'.format(len(diffed),len(ttxt)))

def test_mergeDiff():
  #fn = 'test/patchlib-test'
  #with fopen(fn+'.txt') as f: txt = f.read()
  #with fopen(fn+'-patched.txt') as f: patched = f.read()
  #with fopen(fn+'-diffed.txt') as f: diffed = f.read()
  fn = 'components/variations/service/BUILD.gn'
  with fopen('original/'+fn) as f: txt = f.read()
  with fopen('patched/'+fn) as f: patched = f.read()
  with fopen('../chromium/src/'+fn) as f: diffed = f.read()
  fn = 'test/patchlib-test-BUILD.gn'
  (mtxt,md,conflict,ids) = merge = mergeDiff(txt, patched,diffed, 'txt','txt','mods', byword=True, wordDiffOpts={'get_matches':gestaltPatternMatches, 'junk_match':WordSeparatorMatch, 'bitty_match':0.0})
  print('mergeDiff({}.txt,-diffed.txt,-patched.txt) = '.format(fn)); pp.pprint(merge)

  (mtxt,md,conflict,ids) = merge = mergeDiff(txt, patched,diffed, 'txt','txt','hunks', byword=True, wordDiffOpts={'get_matches':gestaltPatternMatches, 'junk_match':WordSeparatorMatch, 'bitty_match':0.0})
  diffhdr = makeDiffHeader('worddiff',[fn+'.txt',fn+'-patched.txt',fn+'-diffed.txt',fn+'.merged.txt'])
  with fopen(fn+'.merged.txt','w') as f: f.write(mtxt)
  with fopen(fn+'.merged.patch','w') as f: f.write(diffhdr+''.join(md))
  diffhdr = makeDiffHeader('worddiff',[fn+'.txt',fn+'-patched.txt',fn+'-diffed.txt',fn+'.merged.conflict.txt'])
  with fopen(fn+'.conflict-patch.diff','w') as f: f.write(diffhdr+''.join(conflict[0]))
  with fopen(fn+'.conflict-diff.diff','w') as f: f.write(diffhdr+''.join(conflict[1]))
  print('\nResults have been written to '+fn+'.{{merged.{txt,patch}},conflict-{patch,diff}.diff}')

def test_splitPatch():
  fn = 'test.patch'
  with fopen(fn) as f: patch = f.read()
  ps = splitPatch(patch,True)
  print('splitPatch({}):'.format(fn))
  for f in ps:
    print('>>[{}]:'.format(f))
    for i in range(len(ps[f])):
      if not i: print('>>diff header>>[[{}]]'.format(ps[f][0]))
      else: print('  >>hunk #{}:\n{}'.format(i,ps[f][i]))

def main(args):
  #print(args)
  #test_diffAlgos()
  #test_wordDiff_mods2Diff()
  #test_unidiff2mods_mods2Diff()
  test_worddiff2mods_applyMods()
  #test_wordDiffFile(*args.argv)
  #test_diffFile(*args.argv)
  #test_applyDiff(*args.argv)
  #test_mergeDiff()
  #test_splitPatch()
  
if __name__ == "__main__": 
  import argparse
  import sys
  import pprint
  pp = pprint.PrettyPrinter(sort_dicts=False, indent=2, width=120)

  parser = argparse.ArgumentParser(formatter_class=argparse.ArgumentDefaultsHelpFormatter,
    description='Test the module "patchlib"')
  parser.add_argument('argv', nargs='*', default=['test/difflib-hunk-test.txt','test/difflib-hunk-test-diffed.txt'])
  #parser.add_argument('argv', nargs='*', default=['original/chrome/app/chromium_strings.grd','patched/chrome/app/chromium_strings.grd']) # chrome/app/generated_resources.grd chrome/browser/ui/android/strings/android_chrome_strings.grd chrome/app/chromium_strings.grd
  main(parser.parse_args())
  print()