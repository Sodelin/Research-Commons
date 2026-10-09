"""Bounded exact checks of the source forest graph and sparse-location permutation."""
from itertools import combinations
from math import comb, factorial
from fractions import Fraction
from collections import defaultdict
import json

def minimum(t): return t if isinstance(t,int) else min(minimum(t[0]),minimum(t[1]))
def node(a,b): return (a,b) if minimum(a)<minimum(b) else (b,a)
def forest(ts): return tuple(sorted(ts,key=minimum))
def merges(F):
    for a,b in combinations(range(len(F)),2):
        yield forest([F[x] for x in range(len(F)) if x not in (a,b)]+[node(F[a],F[b])])
def splits(F):
    for a,t in enumerate(F):
        if not isinstance(t,int): yield forest(list(F[:a]+F[a+1:])+list(t))
def tokens_tree(t,m):
    if isinstance(t,int): return [t]
    return [m+1]+tokens_tree(t[0],m)+tokens_tree(t[1],m)+[m+2]
def encode(F,m):
    xs=[]
    for i,t in enumerate(F):
        if i: xs.append(m+3)
        xs+=tokens_tree(t,m)
    assert len(xs)<=3*m-2
    w=(m+3).bit_length(); xs += [0]*(3*m-len(xs))
    out=0
    for x in xs: out=(out<<w)|x
    return out

def padded_image(actual,d):
    A=set(actual); x=0
    while len(A)<d:
        if x not in A: A.add(x)
        x+=1
    return sorted(A)
def location(image,l):
    d=len(image)
    if l<d: return image[l]
    x=l-d
    for v in image:
        if v<=x: x+=1
        else: break
    return x
def inverse(image,c):
    if c in image: return image.index(c)
    return len(image)+c-sum(v<c for v in image)

def hook_product(t):
    if isinstance(t,int): return (1,1)
    a,ha=hook_product(t[0]); b,hb=hook_product(t[1])
    return a+b,ha*hb*(a+b-1)
def history_formula(F,m):
    d=1
    for t in F: d*=hook_product(t)[1]
    h=Fraction(factorial(m-len(F)),d)
    assert h.denominator==1
    return h.numerator
def count_prob(m,r,x):
    pref=1
    for j in range(r+1,m+1): pref*=comb(j,2)
    out=Fraction(0)
    for j in range(r,m+1):
        den=1
        for l in range(r,m+1):
            if l!=j: den*=comb(l,2)-comb(j,2)
        out+=x**comb(j,2)/den
    return pref*out
expected=[1,2,7,37,266,2431]
rows=[]
for m in range(1,7):
    todo=[tuple(range(1,m+1))]; seen=set(todo)
    for F in todo:
        for G in merges(F):
            if G not in seen: seen.add(G);todo.append(G)
    assert len(seen)==expected[m-1]
    codes={F:encode(F,m) for F in seen}; assert len(set(codes.values()))==len(seen)
    reverse=defaultdict(set)
    for F in seen:
        outs=list(merges(F)); assert len(outs)==comb(len(F),2)==len(set(outs))
        for G in outs: reverse[G].add(F)
    for F in seen: assert set(splits(F))==reverse[F]
    histories=defaultdict(int); histories[tuple(range(1,m+1))]=1
    for F in sorted(seen,key=lambda F:-len(F)):
        for G in merges(F): histories[G]+=histories[F]
    assert all(histories[F]==history_formula(F,m) for F in seen)
    root_probs={r:count_prob(m,r,Fraction(1,2)) for r in range(1,m+1)}
    mass=Fraction(0)
    for F in seen:
        den=1
        for j in range(len(F)+1,m+1): den*=comb(j,2)
        prob=root_probs[len(F)]*Fraction(histories[F],den)
        assert prob>0
        mass+=prob
    assert mass==1
    if m==1:
        rows.append({'m':1,'forests':len(seen),'zero_generator':True}); continue
    lam=comb(m,2);d=lam+1;q=3*m*(m+3).bit_length();N=1<<(q+1)
    maxsupport=0;checks=0
    for F in seen:
        for layer in (0,1):
            neighbors=list(merges(F)) if layer==0 else list(splits(F))
            if len(F)>=2: neighbors.append(F)
            actual=[((1-layer)<<q)|codes[G] for G in neighbors]
            assert len(actual)==len(set(actual))<=d
            maxsupport=max(maxsupport,len(actual))
            image=padded_image(actual,d)
            assert len(image)==d and set(actual)<=set(image)
            # Check both directions on support slots, boundary positions and their images.
            probes=set(range(d+3))|{N-1}|set(image)
            for l in probes:
                if l<N:
                    c=location(image,l); assert 0<=c<N and inverse(image,c)==l
                    checks+=1
            for c in probes:
                if c<N: assert location(image,inverse(image,c))==c
    # Matrix row sum zero is lambda_k positive offdiagonals plus -lambda_k.
    assert all(len(list(merges(F)))-comb(len(F),2)==0 for F in seen)
    rows.append({'m':m,'forests':len(seen),'q_encoding':q,'layered_qubits':q+1,
                 'sparsity_bound':d,'max_actual_support':maxsupport,
                 'location_inverse_probes':checks,'forward_reverse_and_row_sums':'PASS','hook_histories':'PASS','exact_probability_sum_at_x_half':str(mass)})
print(json.dumps({'status':'PASS','scope':'Exact finite graph and sparse-access checks m<=6; no Hamiltonian simulator, quantum circuit, compiler benchmark or complexity experiment.', 'cases':rows},indent=2))
