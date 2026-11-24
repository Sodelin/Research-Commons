# A relative compact-rank approximation controlled by incidence matching

2026-11-24. Research Commons / Dot. Hand argument and exact finite checks, no Lean verification. This is a tractable parameter regime, not a general bounded-occurrence approximation algorithm.

For the [mixed-gate cut](MIXED-GATE-CUT-RANK.md), R is the number of labeled clause subsets of F admitting a common satisfying assignment. Write m for the number of clauses and d=m−nu for the clause deficit of a maximum clause-to-variable matching of size nu. The graph is the unsigned incidence graph; use its signs only for the verification step.

## Relative, not just additive, estimation

Every subset of the matched clauses is satisfiable: set each matched variable to satisfy its own clause. The matched variables are distinct, so their other appearances do not interfere with that certificate. Thus for uniform independent sampling of subsets of all m labeled clauses, the success probability p=R/2^m is at least 2^(-d). Multiplicative Chernoff then gives relative error at most eps with failure at most delta from O(2^d eps^(-2) log(1/delta)) trials, for 0<eps≤1. The estimator is the empirical success fraction times 2^m, represented rationally.

At width two each trial uses ordinary deterministic 2-SAT. At arbitrary width use [Szeider's maximum-deficiency SAT algorithm](https://eccc.weizmann.ac.il/report/2003/002/), which takes O(2^k poly(input)) at maximum deficiency k. That parameter equals the matching deficit by Hall's theorem, using the standard device of adding dummy variables adjacent to all clauses. For a sampled subset S, retain the matched edges for its matched clauses. Hence d(S) is at most the number Z of sampled clauses not covered by the original matching. In particular d(S)≤d, and for uniform samples E 2^(d(S))≤E 2^Z=(3/2)^d. The resulting running time for arbitrary width is O(3^d poly(input) eps^(-2) log(1/delta)) in expectation, or O(4^d poly(input) eps^(-2) log(1/delta)) as a worst-case bound. Both are polynomial when d=O(log input), regardless of matrix dimensions. Width two has the better 2^d sampling cost without this extra verifier factor.

The same experiment yields an exact uniform sample from jointly satisfiable clause subsets by rejecting failures: conditional on acceptance, each feasible subset has the same probability. Its expected time costs at most a factor 2^d times the expected one-draw cost. This samples feasible subsets, not satisfying assignments.

## When the cap of three is meaningful

If each variable occurs at most three times and clauses have widths at most three, write T=Σ_C(3−width(C)). For any subset Q of clauses, the incidence edge count is at least 3|Q|−T and at most 3|N(Q)|. Therefore |Q|−|N(Q)|≤floor(T/3), and maximizing gives d≤floor(T/3). In particular if every clause has exactly three distinct variables, rank is always maximal under this occurrence cap, independent of the signs. If the shortage T is logarithmic, the relative approximation above remains polynomial. The [exact-hardness construction at degree three](WIDTH-TWO-EXACT-RANK.md) uses many shorter clauses; it does not imply hardness on the almost-full-width subclass. Unbounded matching deficit is not addressed.

## Exact finite sanity check

The replay enumerates clause subsets and assignments in 600 bounded random fixtures and checks the Hall-based rank lower bound, largest subformula deficit, short-clause estimate, and expected per-sample cost majorant. It is not a verification of the imported SAT algorithm or the probability tail bound.

```js
let seed=76111, checks=0;
const rand=m=>(seed=(Math.imul(seed,1664525)+1013904223)>>>0,(seed>>>10)%m);
const match=(F,n)=>{
 const b=new Int16Array(n).fill(-1);
 const add=(j,seen)=>{
   for(const l of F[j]){
    const v=Math.abs(l)-1;if(seen.has(v))continue;seen.add(v);
    if(b[v]<0||add(b[v],seen)){b[v]=j;return true;}
   }return false;
 };
 F.forEach((_,j)=>add(j,new Set()));
 return new Set([...b].filter(j=>j>=0));
};
for(let t=0;t<600;t++){
 const n=1+rand(6),m=rand(9),deg=new Int16Array(n),F=[];
 for(let i=0;i<m;i++){
  const C=[];
  for(let j=0;j<rand(4);j++){
   const v=rand(n);if(deg[v]>=3||C.some(l=>Math.abs(l)===v+1))continue;
   deg[v]++;C.push((rand(2)?1:-1)*(v+1));
  }F.push(C);
 }
 const M=match(F,n),d=m-M.size, T=F.reduce((a,c)=>a+3-c.length,0);
 let R=0,sum=0, md=0;
 for(let s=0;s<1<<m;s++){
   const S=F.filter((_,i)=>s>>i&1);
   const ds=S.length-match(S,n).size;
   md=Math.max(md,ds);sum+=2**ds;
   for(let a=0;a<1<<n;a++)if(S.every(c=>c.some(l=>((a>>(Math.abs(l)-1))&1)===+(l>0)))){R++;break;}
 }
 if(R<2**(m-d)||md!==d||d>Math.floor(T/3)||sum*2**d>2**m*3**d)throw Error('failed');
 checks++;
}
console.log({checks});
```
