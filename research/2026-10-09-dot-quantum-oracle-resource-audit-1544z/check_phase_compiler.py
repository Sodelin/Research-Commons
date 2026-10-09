"""Exact bounded oracle-macro audit; not a full theorem/skeleton compiler."""
import sympy as s
from collections import defaultdict
from pathlib import Path
import json
I=s.I; rt=s.sqrt(2); z=(1+I)/rt
H=s.Matrix([[1,1],[1,-1]])/rt
T=s.diag(1,z); Z=s.diag(1,-1); X=s.Matrix([[0,1],[1,0]])
def simp(x): return s.simplify(s.expand_complex(x))
def mat_simp(A): return A.applyfunc(simp)
# Chronological symbols. Product equals (T^2 H)^6 Z=iZ.
phase=['T']*4+['H','T','T']*6
G={'I':s.eye(2),'H':H,'T':T,'Td':T.conjugate().T}
P=s.eye(2)
for a in phase: P=mat_simp(G[a]*P)
assert P==I*Z and simp(P.det())==1
# Verify the exact controlled-H conjugating matrix from paper Sec. 7.2.
D0=mat_simp((T**2*H)*T*(T**2*H).conjugate().T)
assert mat_simp(D0*Z*D0.conjugate().T)==H
# Symbols I,H,T,Tdagger encoded 00,01,10,11 (little-endian symbol bits).
code={'I':0,'H':1,'T':2,'Td':3}
# Wires: y=0, target=1, phase=2, symbol=3,4, address-y=5,
# address-word=6, address-position=7..11, address-symbol-bit=12.
N=13
counts={'oracle_calls':0,'positions':0,'scratch_checks':0}
def collect(items):
    d=defaultdict(lambda:s.Integer(0))
    for k,v in items: d[k]+=v
    return {k:simp(v) for k,v in d.items() if simp(v)!=0}
def perm(st,f): return collect((f(k),v) for k,v in st.items())
def flip(st,b): return perm(st,lambda k:k^(1<<b))
def cnot(st,c,t): return perm(st,lambda k:k^(((k>>c)&1)<<t))
def oracle(st,target):
    def go(k):
        y=(k>>5)&1; w=(k>>6)&1; p=(k>>7)&31; b=(k>>12)&1
        symbol=phase[p] if y and w and p<len(phase) else 'I'
        return k^(((code[symbol]>>b)&1)<<target)
    counts['oracle_calls']+=1
    return perm(st,go)
def select(st,target):
    out=[]
    for k,a in st.items():
        c=((k>>3)&1)+2*((k>>4)&1)
        M=G[['I','H','T','Td'][c]]; old=(k>>target)&1
        for new in (0,1):
            out.append(((k&~(1<<target))|(new<<target),a*M[new,old]))
    return collect(out)
def compiler(y,t,omit_phase=False):
    st={(y|(t<<1)):s.Integer(1)}
    for word in (0,1):
        for p in range(len(phase)):
            st=cnot(st,0,5)
            if word: st=flip(st,6)
            for b in range(5):
                if (p>>b)&1: st=flip(st,7+b)
            st=oracle(st,3); st=flip(st,12); st=oracle(st,4); st=flip(st,12)
            if not (omit_phase and word==1): st=select(st,1 if word==0 else 2)
            st=oracle(st,3); st=flip(st,12); st=oracle(st,4); st=flip(st,12)
            for b in range(5):
                if (p>>b)&1: st=flip(st,7+b)
            if word: st=flip(st,6)
            st=cnot(st,0,5)
            assert all(k>>3==0 for k in st), 'Lookup/address scratch not restored'
            counts['scratch_checks']+=1; counts['positions']+=1
    return st
for y in (0,1):
    for t in (0,1):
        assert compiler(y,t)=={y|(t<<1):I if y else s.Integer(1)}
        assert compiler(y,t,True)=={y|(t<<1):s.Integer(1)}
# All four basis columns prove exact clean-workspace equality on arbitrary input,
# including any entangled reference, by linearity.
# Negative control: discard relative i phase. On y=+, output trace distance sqrt(2).
v=s.Matrix([1,I])/rt; u=s.Matrix([1,1])/rt
rho=mat_simp(v*v.conjugate().T-u*u.conjugate().T)
assert mat_simp(rho*rho)==s.eye(2)/2
# Basis-law equality can coexist with maximal diamond distance: I versus Z.
plus=s.Matrix([1,1])/rt; minus=Z*plus
assert simp((plus.conjugate().T*minus)[0])==0
# Nonnegative square-root lift of an all-half stochastic matrix is not isometric.
A=s.ones(2)/rt
assert mat_simp(A.conjugate().T*A)==s.ones(2)
report={'status':'PASS','sympy_version':s.__version__,'word_length':len(phase),
        'word_chronological':phase,'phase_word_matrix':'diag(i,-i)',
        'determinant':1,'tested_input_basis_columns':4,'test_variants':2,
        'simulator_wires':N,'lookup_calls_per_variant_per_column':8*len(phase),
        'clean_phase_scratch_at_end':True,'clean_lookup_address_scratch_each_position':True,
        'full_clean_isometry_error':'0 (all four columns, exact)',
        'omitted_phase_channel_distance':'sqrt(2), derived exactly',
        'I_versus_Z_channel_distance':2,'stochastic_sqrt_Gram':'all-ones 2x2',
        'controlled_H_decomposition':'exact symbolic PASS','counts_over_all_runs':counts,
        'scope':'Supplied-word finite oracle-macro simulation and symbolic identities only; no full synthesis generator, ETR implementation, hardware, or Lean run.'}
print(json.dumps(report,indent=2))
