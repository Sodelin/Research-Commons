#!/usr/bin/env python3
"""Strict synthetic Boolean/QF_LRA gate; independent input binding then Ethos.
This parser is NOT formally verified. It deliberately rejects unsupported syntax.
"""
from fractions import Fraction
from collections import Counter
import pathlib, re, sys, json, subprocess, time, resource, os
R=pathlib.Path(__file__).resolve().parents[1]

def sexps(text):
    text=re.sub(r';[^\n]*','',text)
    if re.search(r'["|]',text):raise ValueError('quoted symbols/strings outside pilot grammar')
    toks=re.findall(r'[()]|[^\s()]+',text); i=0
    def one():
        nonlocal i
        if i>=len(toks):raise ValueError('unexpected EOF')
        t=toks[i];i+=1
        if t==')':raise ValueError('unexpected close')
        if t!='(':return t
        a=[]
        while i<len(toks) and toks[i]!=')':a.append(one())
        if i>=len(toks):raise ValueError('unclosed sexp')
        i+=1;return a
    out=[]
    while i<len(toks):out.append(one())
    return out

def declarations(cmds):
    ds={}
    for c in cmds:
        if c[0]=='declare-const':
            if len(c)!=3 or c[2] not in ['Real','Bool'] or c[1] in ds:raise ValueError('unsupported/duplicate declaration')
            ds[c[1]]=c[2]
    return ds

def canonical(t,decl,aliases,active=frozenset()):
    if isinstance(t,str):
        if t in aliases:
            if t in active:raise ValueError('cyclic proof alias')
            return canonical(aliases[t],decl,aliases,active|{t})
        if t in ['true','false']:return ('Bool',t)
        if t in decl:return ('Var',t,decl[t])
        try:return ('Num',str(Fraction(t)))
        except (ValueError,ZeroDivisionError):raise ValueError('unknown atom '+t)
    if not t:raise ValueError('empty expression')
    op=t[0]; args=[canonical(x,decl,aliases,active) for x in t[1:]]
    if op not in ['and','or','not','=>','=','+','-','*','/','<','<=','>','>=']:raise ValueError('unsupported term operator '+op)
    if op=='/' and not (len(args)==2 and all(a[0]=='Num' for a in args) and Fraction(args[1][1])!=0):raise ValueError('only constant nonzero rational division supported')
    if op=='*' and sum(a[0]!='Num' for a in args)>1:raise ValueError('nonlinear multiplication outside fragment')
    if op in ['+','-','*','/'] and all(a[0]=='Num' for a in args):
        f=[Fraction(a[1]) for a in args]
        if op=='+':v=sum(f,Fraction())
        elif op=='-':v=-f[0] if len(f)==1 else f[0]-sum(f[1:])
        elif op=='*':
            v=Fraction(1)
            for n in f:v*=n
        else:v=f[0]/f[1]
        return ('Num',str(v))
    return (op,*args)

def bind(original,certificate):
    src=sexps(original);proof=sexps(certificate)
    allowedsrc={'set-logic','declare-const','assert','check-sat'}
    if any(c[0] not in allowedsrc for c in src):raise ValueError('input command outside pilot grammar')
    logic=[c[1] for c in src if c[0]=='set-logic']
    if logic not in [['QF_LRA'],['QF_UF']]:raise ValueError('unsupported logic')
    if sum(c[0]=='check-sat' for c in src)!=1 or src[-1]!=['check-sat']:raise ValueError('require one final nonincremental query')
    sd=declarations(src);pd=declarations(proof)
    if sd!=pd:raise ValueError('proof/input declaration mismatch')
    aliases={}
    for c in proof:
        if c[0]=='define':
            if len(c)!=4 or c[2]!=[] or c[1] in aliases:raise ValueError('unsupported/duplicate alias')
            aliases[c[1]]=c[3]
        elif c[0] not in ['declare-const','assume','step']:raise ValueError('proof command outside pilot grammar')
    actual=[canonical(c[2],sd,aliases) for c in proof if c[0]=='assume']
    expected=[canonical(c[1],sd,{}) for c in src if c[0]=='assert']
    if Counter(map(repr,actual))!=Counter(map(repr,expected)):raise ValueError('proof/input assumption mismatch')
    if any(':rule' in c and c[c.index(':rule')+1]=='trust' for c in proof if c[0]=='step'):raise ValueError('trust rule rejected')
    return dict(logic=logic[0],declarations=sd,expanded_assumptions=actual,assertion_count=len(expected),binding='exact multiset after alias expansion and exact constant rational normalization')

def main():
    inp=pathlib.Path(sys.argv[1]);pf=pathlib.Path(sys.argv[2]);t=time.monotonic()
    try:
        receipt=bind(inp.read_text(),pf.read_text())
    except (ValueError,IndexError,TypeError,RecursionError) as e:
        print(json.dumps(dict(status='BINDING_REJECTED',reason=str(e),elapsed_s=time.monotonic()-t)));return 1
    def render(t):
        return '('+' '.join(render(x) for x in t)+')' if isinstance(t,list) else t
    proofcmds=sexps(pf.read_text())
    body='\n'.join(render(c) for c in proofcmds if c[0]!='declare-const')+'\n'
    wrapped=R/'proofs'/f'{inp.stem}-{pf.stem}-ethos-bound.cpc'
    wrapped.write_text(f'(include \"{R}/vendor/cvc5-cvc5-1.4.1/proofs/eo/cpc/Cpc.eo\")\n(reference \"{inp.resolve()}\")\n'+body)
    cmd=[str(R/'ethos'),'--require-proof-of-false','--normalize-num',str(wrapped)]
    def limit():
        resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3))
    p=subprocess.run(cmd,stdout=subprocess.PIPE,stderr=subprocess.PIPE,timeout=20,preexec_fn=limit)
    receipt.update(status='CHECKED_CERTIFICATE' if p.returncode==0 and p.stdout==b'correct\n' else 'CHECKER_REJECTED',checker_command=cmd,checker_exit_code=p.returncode,checker_stdout=p.stdout.decode(),checker_stderr=p.stderr.decode(),elapsed_s=time.monotonic()-t)
    print(json.dumps(receipt));return 0 if receipt['status']=='CHECKED_CERTIFICATE' else 1
if __name__=='__main__':sys.exit(main())
