''' author: samtenka
    change: 2022-08-24
    create: 2022-08-20
    descrp: an experiment in formal verification of
            dijkstra style reasoning about programs
    jargon:
            conc            conclusion
            hypo            hypothesis
            
            lft             left   (of a binary coproduct)
            rht             right  (of a binary coproduct)
            fst             first  (of a binary product)
            snd             second (of a binary product)
            bom             bottom type
            top             top type
    to use: run `python3 deduce.py` to generate and print a proof tree of an
            example exercise formatted like the example below.  Press `<enter>`
            when prompted to go to the next example exercise.

             proof goal          available hypotheses
             __________          __________________  
            /          \        /                  \ 
            (a+b)->(b&c)  from  a->b  ,  (d&c)+(e&c)                (A)
            |  b&c  from  (d&c)+(e&c)  ,  a->b  ,  a+b              (A*)
            |  fst                                                  (A*0') 
            |  |  b  from  a->b  ,  a+b  ,  (d&c)+(e&c)             (A*0)
            |  |  slice a->b                                        (A*0*')        
            |  |  |  a  from  a+b  ,  a->b  ,  (d&c)+(e&c)          (A*0*)           
            |  |  |  split a+b                                      (A*0*")           
            ...
            |  |  |  ~                                              (A*0*x)           
            |  |  split a+b                                         (A*0**)         
            ...
            |  |  ^                                                 (A*0.) 
            |  snd                                                  (A*1')     
            |  |  c  from  (d&c)+(e&c)  ,  b  ,  a+b  ,  a->b       (A*1)      
            |  |  split (d&c)+(e&c)                                 (A*1")     
            |  |  case d&c                                          (A*10')    
            |  |  |  c  from  c  ,  d  ,  a->b  ,  a+b  ,  b        (A*10)     
            |  |  |  ^                                              (A*10.)    
            |  |  case e&c                                          (A*11')    
            |  |  |  c  from  c  ,  e  ,  a->b  ,  a+b  ,  b        (A*11)     
            |  |  |  ^                                              (A*11.)    
            |  |  ^                                                 (A*1.)     
            |  ^                                                    (A*.)      
            ^                                                       (A.)       
                                                                 
            Here, lines like (A), (A*), (A*0), (A*0*), (A*0**), (A*1), (A*10),
            (A*11) show intermediate tasks of form (proof goal, list of
            available hypotheses).  Lines like (A*0'), (A*0*'), (A*0*"),
            (A*1'), (A*1"), (A*10'), (A*11') annotate how the succeeding
            task(s) were gotten from the previous ones.  Lines like (A*0*x) /
            (A*0.), (A*10.), (A*11.), (A*1.), (A*.), (A.) indicate the
            unsuccessful / successful proof of their corresponding pair.
'''

#==============================================================================
#=  0  SET UP  ================================================================
#==============================================================================

#~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
#~  0.0  Imports  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

from itertools import chain

#~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
#~  0.1  Configuration Parameters  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

# disable if colorblind 
FULLCOLOR = True

#~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
#~  0.2  Pretty Printing  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

ANSI_BY_TAGS = {
  'a'       : '\033[30m' if FULLCOLOR else '\033[30;0m'   , # gray   
  'r'       : '\033[31m' if FULLCOLOR else '\033[33;0m'   , # red    
  'e'       : '\033[32m' if FULLCOLOR else '\033[33;1m'   , # green  
  'y'       : '\033[33m' if FULLCOLOR else '\033[33;1;44m', # yellow 
  'b'       : '\033[34m' if FULLCOLOR else '\033[34;0m'   , # blue   
  'm'       : '\033[35m' if FULLCOLOR else '\033[34;1m'   , # magenta
  'c'       : '\033[36m' if FULLCOLOR else '\033[34;1;43m', # cyan   
                                                            #
  'up'      : '\033[1A'                                   , # up   
  'down'    : '\033[1B'                                   , # down 
  'right'   : '\033[1C'                                   , # right
  'left'    : '\033[1D'                                   , # left 
}

def display(s, *args):
    ''' Print the string `s` after substituting formatting arguments provided
        in `*args` and interpreting ansi commands.  For example:

            place = '<c>world'
            display('<y>hello {}<r>', place)
            display('still on same line')

        causes 'hello worldstill on same line' to be printed, the 'hello' in
        yellow, the 'world' in cyan, and the remaining text in red.  Note that
        `display` does not implicitly print a newline.
    '''
    s = s.format(*args)
    for k,v in ANSI_BY_TAGS.items():
        s = s.replace('<'+k+'>', v)
    print(s, end='')

#==============================================================================
#=  1  SYNTAX  ================================================================
#==============================================================================

#~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
#~  1.0  Syntax Tree  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

class Tree:
    def __init__(self, tag, kids=[]):
        self.tag = tag
        self.kids = kids

    def nb_kids(self):
        return len(self.kids)

    def matches(self, pattern):
        if self.tag != pattern.tag: return False 
        if self.nb_kids() != pattern.nb_kids(): return False 
        for ks, kp in zip(self.kids, pattern.kids):
            if not ks.matches(kp): return False
        return True

    def as_str(self, prefix=''):
        if not self.kids: return self.tag[1:]
        a, b = self.kids
        aa = a.display() if not a.kids else ('('+a.display()+')')
        bb = b.display() if not b.kids else ('('+b.display()+')')
        return aa+self.tag+bb

    def display_multiline(self, prefix=''):
        return prefix+self.tag+'\n' + ''.join(
            k.display_multiline(prefix+'   ')+'\n'
            for k in self.kids
        )

#~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
#~  1.1  Parse Strings Into Trees  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

def is_atom(tree):
    return tree.tag[:1] == ':'

class LogicParser:
    def __init__(s, toks):
        s.toks = toks
        s.idx = 0 

    def at_end(s):
        return not (s.idx < len(s.toks)) 

    def peek(s):
        assert not s.at_end() 
        return s.toks[s.idx]

    def match(s, cc):
        for c in cc:
            assert s.peek() == c 
            s.idx += 1

    def atom(s):
        c = s.peek()
        assert c.isalpha()
        s.match(c)
        return Tree(':'+c, [])

    def expr(s):
        head = s.disj()
        if not s.at_end() and s.peek() == '-':
            s.match('->')
            tail = s.expr()
            return Tree('->', [head, tail]) 
        return head

    def disj(s):
        head = s.conj()
        if not s.at_end() and s.peek() == '+':
            s.match('+')
            tail = s.disj()
            return Tree('+', [head, tail]) 
        return head

    def conj(s):
        head = s.fact()
        if not s.at_end() and s.peek() == '&':  
            s.match('&')
            tail = s.conj()
            return Tree('&', [head, tail]) 
        return head

    def fact(s):
        if s.peek().isalpha(): return s.atom()
        elif s.peek()=='(':
            s.match('(')
            r = s.expr()
            s.match(')')
            return r

#==============================================================================
#=  2. DEDUCTION ALGORITHM  ===================================================
#==============================================================================

#~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
#~  2.0  Heuristics  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

def atom_counts(tree):
    if is_atom(tree):  return {tree.tag:1} 
    a, b = tree.kids
    aa = atom_counts(a)
    bb = atom_counts(b)
    cc = {}
    wa, wb = (1.0, 1.0) if tree.tag=='&' else (0.5, 0.5) if tree.tag=='+' else (0.25, 0.75) if tree.tag=='->' else None  
    #for k,v in chain(aa.items(), bb.items()):
    #    if k not in cc: cc[k]=0
    #    cc[k] += v
    for k,v in aa.items():
        if k not in cc: cc[k]=0
        cc[k] += wa*v
    for k,v in bb.items():
        if k not in cc: cc[k]=0
        cc[k] += wb*v
    return cc

def count_overlap(aa, bb): 
    t=0
    keys = set(chain(aa.keys(), bb.keys()))
    return float(sum(
        (aa[k] if k in aa else 0)*
        (bb[k] if k in bb else 0) for k in keys))/len(keys)

#~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
#~  2.1  Display Helpers  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

def display_judgement(tree, givens):
    return ('<y>'+tree.display()+'<b>'+ '  from  ' +
            '  ,  '.join('<c>'+g.display()+'<b>' for g in givens))

YES = '<e>^<b>\n' 
NO  = '<r>~<b>\n'

#~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
#~  2.2  Prover Proper  ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~

class Prover:
    def __init__(s):
        pass

    def can_prove(s, tree, givens, tab='', energy=10):
        if energy<=0: return False

        # TODO: //scheduler//
        #   so that if initially promising path seems very unpromising after
        #   much search (but not yet out of energy), can put on pause and try
        #   others (initially unpromising but now looking better) first

        # TODO: //introduce infinitely many (but numerically downweighted) hypotheses//
        #       such as (Q + (Q->0)) --- excluded middle --- for arbitrary Q?
        # ? weak use here of patterns (placeholder blanks for universal quant)

        # 0. break open conjunctions in hypothesis!  
        cs = [g for g in givens if g.tag=='&']
        givens = [g for g in givens if g.tag!='&']
        for g in cs: 
            fst, snd = g.kids
            givens.append(fst)
            givens.append(snd)
        # 1. sort:
        act = atom_counts(tree)
        idxs = sorted([(count_overlap(act, atom_counts(g)), i) for i,g in enumerate(givens)], reverse=True)
        givens = [givens[i] for _,i in idxs]
        # 2. remove duplicates
        # TODO
        # 3. print
        display('{}{}\n', tab, display_judgement(tree,givens))

        newtab = tab + '|  '
        en = energy-1

        def easies():
            if is_atom(tree):
                for g in givens:
                    if is_atom(g) and g.tag==tree.tag: return (display(tab+YES), True)[1]
                return False
            elif tree.tag == '->': # abstraction
                hypo, conc = tree.kids
                if s.can_prove(conc, [hypo]+givens, newtab, en): return (display(tab+YES), True)[1]
            elif tree.tag == '+':
                lft, rht = tree.kids
                display('{}try lft\n', tab)
                if s.can_prove(lft, givens, newtab, en): return (display(tab+YES), True)[1]
                display('{}try rht\n', tab)
                if s.can_prove(rht, givens, newtab, en): return (display(tab+YES), True)[1]
                return False
            elif tree.tag == '&':
                fst, snd = tree.kids
                display('{}fst\n', tab)
                if not s.can_prove(fst, givens, newtab, en): return False
                display('{}snd\n', tab)
                if not s.can_prove(snd, givens+[fst], newtab, en): return False
                return (display(tab+YES), True)[1]

        if easies(): return True

        # solved slice (i.e., evaluation)
        gs = [g for g in givens if g.tag=='->' and
                                   g.kids[1].matches(tree)]  # evaluation
        en = energy - (1 if len(gs)==1 else 2)
        for g in gs:
            display('{}slice {}\n', tab, g.display())
            hypo, conc = g.kids
            if s.can_prove(hypo, givens, newtab, en): return (display(tab+YES), True)[1]

        # split on 
        igs = [(i,g) for i,g in enumerate(givens) if g.tag=='+']
        for i,g in igs:
            display('{}split {}\n', tab, g.display())
            lft, rht = g.kids 
            gg = givens[:i] + givens[i+1:]
            act = atom_counts(tree) 
            for b, nm in [(lft, 'lft'), (rht, 'rht')]:
                display('{}case {}\n', tab, b.display())
                acb = atom_counts(b)
                en = int(energy * 2.0/3) if count_overlap(act, acb) > 0.75 else int(energy * 1.0/3) 
                if not s.can_prove(tree, [b]+gg, newtab, en): break
            else:
                return (display(tab+YES), True)[1]

        return (display(tab+NO), False)[1]


def tree_from_str(ss):
    return LogicParser(ss).expr()

#==============================================================================
#=  3. MAIN LOOP  =============================================================
#==============================================================================

if __name__=='__main__':
    example_problems= [
        ('(a+b)->(b&c)', ['(d&c)+(e&c)', 'a->b']),  # proof
        ('a->F', ['((a->F)->F)->F']),               # proof 
        ('a', ['(a->F)->F']),                       # no (intuitionstic) proof 
    ]
    for conc, hypos in example_problems: 
        cc = tree_from_str(conc)
        hhs = [tree_from_str(hh) for hh in hypos]
        P = Prover()
        print(P.can_prove(cc, hhs))
        display('<r>enter to continue...'); input()
