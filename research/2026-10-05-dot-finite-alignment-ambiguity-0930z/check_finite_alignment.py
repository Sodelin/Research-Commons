#!/usr/bin/env python3
"""Exact finite controls for the equal-rate joint-forest alignment candidate."""
from fractions import Fraction as Q
from itertools import product, combinations
from math import comb, factorial, prod
from pathlib import Path
import json
import sympy as s

def prep_exponents(colors,rates):
    sizes=[3*2**i for i in range(len(colors))]
    counts={p:sum(w for w,a in zip(sizes,colors) if a==p) for p in range(len(rates))}
    q=[];starts=[]
    for i,(a,w) in enumerate(zip(colors,sizes)):
        starts.append(len(q))
        for _ in range(w-1):
            before=sum(comb(k,2)*rates[p] for p,k in counts.items())
            counts[a]-=1
            after=sum(comb(k,2)*rates[p] for p,k in counts.items())
            q.append(before-after)
    return tuple(q),starts,sizes

def decode(q,starts,sizes):
    marked=[];done=set()
    for i,k in enumerate(starts):
        if i in done:continue
        rate=q[k]-q[k+1];assert rate>0
        pop_count=Q(q[k],rate)+1;assert pop_count.denominator==1
        value=int(pop_count)//3;assert int(pop_count)%3==0
        group=tuple(j for j in range(len(sizes)) if (value>>j)&1)
        assert sum(sizes[j] for j in group)==pop_count and i in group and not (set(group)&done)
        assert all(q[starts[j]]-q[starts[j]+1]==rate for j in group)
        done.update(group);marked.append((group,rate))
    assert len(done)==len(sizes)
    return tuple(marked)

decode_checks=0
for rates in ([1,1,1],[1,1,2],[1,2,4]):
    for m in range(1,6):
        byq={}
        for colors in product(range(3),repeat=m):
            q,starts,sizes=prep_exponents(colors,rates)
            true=tuple(sorted([(tuple(i for i,a in enumerate(colors) if a==p),rates[p]) for p in set(colors)],key=lambda z:z[0][0]))
            assert decode(q,starts,sizes)==true
            if q in byq:assert byq[q]==true
            byq[q]=true;decode_checks+=1

def parts(n):
    if n==0:return [()]
    out=[]
    for pi in parts(n-1):
        out.append(pi+((n-1,),))
        for i,B in enumerate(pi):out.append(pi[:i]+(B+(n-1,),)+pi[i+1:])
    return out

def color_partition(z):
    return tuple(sorted([tuple(i for i,a in enumerate(z) if a==p) for p in set(z)],key=lambda B:B[0]))

def target_limit(z,rs,target):
    # Independent path expansion for artificial constant-epoch forest process.
    init=tuple((i,) for i in range(len(z)));answer=Q(0)
    def population(B):return z[B[0]]
    def exitrate(pi):
        ps=[population(B) for B in pi]
        return sum(comb(ps.count(a),2)*rs[a] for a in range(len(rs)))
    def recurse(pi,qs,weight):
        nonlocal answer
        q=exitrate(pi);qs=qs+[q]
        if pi==target:
            # Limit of sum exp(-q_i*t)/prod_{j!=i}(q_j-q_i).
            if q==0:answer+=weight/prod(v for v in qs[:-1])
            return
        if len(pi)<=len(target):return
        for i,j in combinations(range(len(pi)),2):
            B,C=pi[i],pi[j]
            if population(B)!=population(C):continue
            union=tuple(sorted(B+C))
            if not any(set(union)<=set(T) for T in target):continue
            nxt=tuple(sorted([pi[k] for k in range(len(pi)) if k not in(i,j)]+[union],key=lambda B:B[0]))
            recurse(nxt,qs,weight*rs[population(B)])
    recurse(init,[],Q(1));return answer

terminal_checks=0
rs=[1,1,2]
for z in product(range(3),repeat=4):
    for pi in parts(4):
        assert target_limit(z,rs,pi)==int(pi==color_partition(z));terminal_checks+=1

# One fixed symmetric old preparation gives the same weights1/2,1/2 for all
# future tests. An arbitrary large panel can provide all selected anchors;
# future restriction leaves these old-permutation mixture weights unchanged.
G=[[Q(3,10),Q(1,10),Q(7,20),Q(1,4)],
   [Q(1,10),Q(3,10),Q(1,4),Q(7,20)]]
H=[[G[1][0],G[1][1],G[0][2],G[0][3]],
   [G[0][0],G[0][1],G[1][2],G[1][3]]]
r=[1,2,3,4]

def marked_law(A,inputs):
    law={}
    for flip in (0,1):
        for z in product(range(len(r)),repeat=len(inputs)):
            weight=Q(1,2)*prod(A[i^flip][a] for i,a in zip(inputs,z))
            pi=color_partition(z)
            mark=tuple(r[z[B[0]]] if len(B)>=2 else None for B in pi)
            key=(pi,mark);law[key]=law.get(key,0)+weight
    assert sum(law.values())==1
    return law

def product_from_marks(A,groups):
    inputs=tuple(i for inds,power in groups for i in inds)
    index_groups=[];start=0
    for inds,power in groups:index_groups.append((tuple(range(start,start+len(inds))),power));start+=len(inds)
    value=Q(0)
    for (pi,marks),w in marked_law(A,inputs).items():
        z=Q(1)
        for labels,power in index_groups:
            containing=[j for j,B in enumerate(pi) if set(labels)<=set(B)]
            if not containing:z=Q(0);break
            j=containing[0];assert marks[j] is not None;z*=marks[j]**power
        value+=w*z
    return value

def T(A,inds,power,flip):return sum(r[a]**power*prod(A[i^flip][a] for i in inds) for a in range(len(r)))
products=[ [((0,0),1)], [((0,1),2)], [((0,0,1),3)],
           [((0,0),1),((0,0),1)], [((0,1),2),((1,1),1)],
           [((0,0),1),((1,1,0),2)] ]
product_checks=0
for A in (G,H):
    for groups in products:
        observed=product_from_marks(A,groups)
        expected=sum(Q(1,2)*prod(T(A,inds,power,flip) for inds,power in groups) for flip in(0,1))
        assert observed==expected;product_checks+=1

# Complete single-group feature means agree for this source-valid column-swap
# example, while a joint marked-partition product separates the alignments.
for m in range(2,6):
    for inds in product(range(2),repeat=m):
        for power in range(m-1,m+2):
            assert sum(T(G,inds,power,f) for f in(0,1))==sum(T(H,inds,power,f) for f in(0,1))
variance_difference=product_from_marks(G,[((0,0),1),((0,0),1)])-product_from_marks(H,[((0,0),1),((0,0),1)])
assert variance_difference==Q(3,625)

# Positive two-atom recovery of a feature coordinate from fixed-mixture products.
z=[T(G,(0,0),1,f) for f in(0,1)]
mom=[sum(Q(1,2)*a**k for a in z) for k in range(5)]
C=s.Matrix([[mom[0],mom[1]],[mom[1],mom[2]]]).inv()*s.Matrix([-mom[2],-mom[3]])
u=s.symbols('u');roots=s.roots(u*u+C[1]*u+C[0]);assert set(roots)==set(map(s.Rational,z))
assert all(v==1 for v in roots.values())

# Recover repeated rate marks from an artificial terminal two-block forest.
# Each terminal block has two labels, so its first wait has rate r itself.
markrates=[1,1,2,2]
markweights={}
for flip in (0,1):
 for a,b in product(range(4),repeat=2):
  if a==b:continue
  mark=(markrates[a],markrates[b])
  w=Q(1,2)*G[flip][a]**2*G[1^flip][b]**2
  markweights[mark]=markweights.get(mark,0)+w
u,v=s.symbols('u v')
survival=sum(s.Rational(w)*s.exp(-a*u-b*v) for (a,b),w in markweights.items())
rate_mom={}
for degree in range(9):
 for i in range(degree+1):
  j=degree-i
  rate_mom[i,j]=s.simplify((-1)**degree*s.diff(survival,u,i,v,j).subs({u:0,v:0}))
  assert rate_mom[i,j]==sum(w*a**i*b**j for (a,b),w in markweights.items())
projected=[sum(comb(k,i)*3**(k-i)*rate_mom[i,k-i] for i in range(k+1)) for k in range(9)]
Hankel=s.Matrix(4,4,lambda i,j:projected[i+j]);assert Hankel.det()!=0
coef=Hankel.inv()*s.Matrix([-projected[4+i] for i in range(4)])
zsym=s.symbols('z');roots2=s.roots(zsym**4+sum(coef[i]*zsym**i for i in range(4)))
assert len(roots2)==4
zs=list(roots2);V=s.Matrix(4,4,lambda i,j:zs[j]**i)
ws=V.inv()*s.Matrix(projected[:4]);coords=[]
for axis in (0,1):
 obs=[]
 for k in range(4):
  obs.append(sum(comb(k,i)*3**(k-i)*rate_mom[i+int(axis==0),k-i+int(axis==1)] for i in range(k+1)))
 vals=V.inv()*s.Matrix(obs);coords.append([vals[i]/ws[i] for i in range(4)])
recovered_marks={(int(coords[0][i]),int(coords[1][i])):ws[i] for i in range(4)}
assert all(recovered_marks[key]==w for key,w in markweights.items())

bound_examples={}
for P in(1,2,3):
 B=factorial(P);K=2*B*(2*P+2);M=P*K;N=3*(2**M-1)
 assert all(K>=2*factorial(p)*(2*P+2) for p in range(1,P+1))
 bound_examples[str(P)]={'K':K,'M':M,'N':str(N)}
result={'status':'PASS','arithmetic':'Fraction and exact SymPy polynomial recovery',
'superincreasing_partition_rate_decode_checks':decode_checks,
'artificial_constant_epoch_terminal_partition_checks':terminal_checks,
'fixed_mixture_marked_partition_product_checks':product_checks,
'joint_product_separates_columnwise_alignment_by':str(variance_difference),
'positive_two_atom_feature_recovery':True,'joint_rate_mark_derivative_checks':len(rate_mom),'joint_rate_mark_atoms_recovered':len(recovered_marks),'sample_bound_examples':bound_examples,
'limits':'Finite controls for specific gates; not proof of universal alias count, optimal sampling, finite-data inference, novelty or Lean verification.'}
text=json.dumps(result,indent=2)+'\n';Path(__file__).with_name('CONTROL-RESULTS.json').write_text(text);print(text,end='')
