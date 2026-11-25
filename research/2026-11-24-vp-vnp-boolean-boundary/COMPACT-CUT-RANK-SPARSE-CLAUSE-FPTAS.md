# Deterministic FPTAS for low-activity clause rank, even at exponentially small density

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof and exact finite replay. Uses the [Barvinok and Patel–Regts zero-free interpolation approach](https://arxiv.org/abs/1607.01167); the concrete polynomial and sufficient radius are derived here. No Lean verification. The constant-activity cutoff is a sufficient condition, not an optimal threshold.

A clause is a labeled constraint in a supplied CNF, and H is its clause overlap graph (two labels adjacent if they share any variable). Let its maximum degree be Delta and D=max(1,Delta). For independent selection of clause labels, put p_i=Pr(select i) and a_i=p_i/(1-p_i). If all rational a_i are nonnegative and at most 1/(16D(D+1)), the probability of selecting a satisfiable subformula has a deterministic relative FPTAS, for fixed Delta and polynomial-size rational weights. It is valid for arbitrary signs, cycles and any number of unit clauses in this regime. Testing feasibility of a subset of k connected clauses by checking assignments requires only 2^O(k) time when the clause widths are bounded; bounded width is therefore assumed for the runtime assertion. The nonvanishing statement itself needs only the overlap bound.

In particular, binary clauses of occurrence at most three have Delta<=4. In the weighted compressed-core rank model of the [pruning note](COMPACT-CUT-RANK-RELATIVE-PATH-OBSTRUCTION.md), all clause blocks of length t_i>=9 meet the condition, since their odds are 1/(2^t_i-1) and 511>=320. Multiply the normalized feasibility approximation by the exact total multiplicity and any free factor to approximate that rank. This applies when the compressed weighted core is supplied, or recovered by the previously proved exact compression; it is not an unweighted occurrence-three FPTAS.

## Direct nonvanishing proof

For any allowed set A of labels define
```
Z_A(z)=sum_{S subset A, S satisfiable} z^|S| prod_{i in S} a_i.
```
On disjoint components of H[S], feasibility factors because the variable sets are disjoint. Equivalently, Z_A sums collections of nonempty, feasible connected subsets (polymers) that do not touch one another in H. Separate the terms in Z_A according to whether a given v in A is used. If used, its connected component gamma is a feasible connected subset of A containing v, and the remaining labels lie outside the closed neighborhood of gamma. Hence
```
Z_A=Z_{A-v}+sum_gamma z^|gamma| (prod_{i in gamma} a_i) Z_{A minus N_H[gamma]}.
```
Put delta=1/(D+1). Induct on |A| that for every |z|<=2 the ratios Z_A/Z_{A-v} are defined and within delta of 1. The empty polynomial is 1. By the smaller-set induction and telescoping successive deletions from A-v, the last quotient after division by Z_{A-v} is bounded by (1-delta)^(-(D+1)|gamma|). For D>=1, (1+1/D)^(D+1)<=4: the function (x+1)log(1+1/x) has derivative log(1+1/x)-1/x<0. So each summand is at most b^|gamma|, with b=8 max_i a_i. There are at most D^(2(k-1)) connected k-sets containing v, by encoding a deterministic depth-first spanning-tree traversal of 2(k-1) edge steps from v. The sum is at most b/(1-D²b), and D²b<=D/(2(D+1))<1/2. Thus it is at most 2b<=1/(D(D+1))<=delta. The ratios cannot be zero since delta<=1/2. This proves uniform nonvanishing in the closed disk of radius 2.

## Connected coefficients and relative error

Let L_A denote the formal logarithm of Z_A at zero, with constant term zero, and write c_k(A)=[z^k]L_A. For S nonempty let
```
u_k(S)=sum_{A subset S} (-1)^(|S|-|A|) c_k(A).
```
Möbius inversion gives c_k(full)=sum_S u_k(S). The term vanishes for |S|>k: in the multivariate logarithm each monomial uses at most k labels at total degree k and restriction to A sets other activities to zero, so inversion retains exactly full support S. The term also vanishes if H[S] is disconnected, since for every subset of S, the polynomial factors across those components and its logarithm is additive. Thus only connected S of size <=k need be visited.

For m clauses and cutoff K all needed sets can be enumerated in m exp(O_D(K)) time by the same depth-first-walk upper bound, with duplicate vertex sets removed. For each visited S, enumerate A subset S, then feasible subsets of A, by direct assignments to the variables appearing there; with bounded width this is exp(O(K)). Formal logarithm coefficients through K follow by formal division of Z'_A by Z_A. Arithmetic can be rational: a common denominator for polynomial coefficients is the product of the given rational denominators, and through order K the derivative-log denominator divides its K-th power. Division by k adds only polynomial bit cost. The finite Möbius sums and coefficient sizes have polynomial bit lengths for the cutoff below.

Since all roots r_j of the full polynomial have |r_j|>2 and Z(0)=1, factorization gives log Z(1)= -sum_{k>=1} sum_j r_j^(-k)/k on the branch through zero. With at most m roots, the tail beyond K is at most m 2^(-K). Take K=ceil(log_2(8 max(1,m)/epsilon)) for 0<epsilon<=1. Exponentiation with additive log error at most epsilon/8 costs polynomial precision: for nonnegative activities log Z(1) lies between zero and sum_i log(1+a_i), which is O(m). Divide the result by the exactly known prod_i(1+a_i), or use the exact multiplicity prefactor for weighted rank. The factors cancel from the relative error. Total time is polynomial in input length and 1/epsilon for fixed maximum degree and width, even if the feasibility probability is exponentially small. For instance, disjoint incompatible unit pairs at common nonzero p have density (1-p²)^(m/2).

## Exact finite check and limit

The following replay uses integer formal weights, not a numerical root finder, and checks 542 coefficient identities on 120 seeded CNFs. It tests the connected-support calculation in a regime where complex convergence is irrelevant. It does not prove the disk bound or benchmark the algorithm.
```js
let seed=99731,checks=0;
const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>11)%n;};
const pop=x=>{let k=0;for(;x;x&=x-1)k++;return k;};
for(let run=0;run<120;run++){
 const F=Array.from({length:1+rnd(8)},()=>Array.from({length:1+rnd(2)},()=> (1+rnd(5))*(rnd(2)?1:-1)));
 const m=F.length,full=(1<<m)-1;
 const adj=F.map((C,i)=>F.reduce((mask,D,j)=>i!==j&&C.some(x=>D.some(y=>Math.abs(x)===Math.abs(y)))?mask|(1<<j):mask,0));
 const conn=S=>{let T=S&-S;for(let i=0;i<m;i++)for(let j=0;j<m;j++)if(T>>j&1)T|=adj[j]&S;return T===S;};
 const w=F.map(()=>BigInt(1+rnd(3)));
 const cover=Array.from({length:32},(_,x)=>F.reduce((mask,C,i)=>C.some(l=>Boolean(x>>(Math.abs(l)-1)&1)===(l>0))?mask|(1<<i):mask,0));
 const logs=[];
 for(let A=0;A<=full;A++){
  const p=Array(m+1).fill(0n);
  for(let S=A;;S=(S-1)&A){
   if(cover.some(T=>(S&T)===S)){let a=1n;for(let i=0;i<m;i++)if(S>>i&1)a*=w[i];p[pop(S)]+=a;}
   if(!S)break;
  }
  const e=[0n];
  for(let k=1;k<=m;k++){let v=BigInt(k)*p[k];for(let j=1;j<k;j++)v-=p[k-j]*e[j];e[k]=v;}
  logs.push(e);
 }
 for(let k=1;k<=m;k++){
  let total=0n;
  for(let S=1;S<=full;S++){
   let term=0n;for(let A=S;;A=(A-1)&S){term+=(pop(S^A)%2?-1n:1n)*logs[A][k];if(!A)break;}
   if(!conn(S)||pop(S)>k){if(term!==0n)throw Error("support");}
   else total+=term;
  }
  if(total!==logs[full][k])throw Error("coefficient");checks++;
 }
}
console.log(checks);
```

The overlap graph built from fair clauses has a_i=1, far outside this disk argument. Neither exact hardness nor the private-port obstruction proves what happens there; a zero-free region at fair activity, an alternate relative approximation algorithm, or an approximation-hardness reduction for that class remains open here.
