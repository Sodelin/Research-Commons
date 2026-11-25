# Unrestricted compact AND/OR cut rank is SpanP-complete

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof and exact finite replay. Completeness is under polynomial-time metric reductions (one exact oracle value plus polynomial-time decoding). Clause labels are distinct even when their literal sets agree. No Lean verification or complexity-class separation.

The [mixed-gate cut-rank identity](MIXED-GATE-CUT-RANK.md) shows that the exact rank, over any field, is the number of satisfiable subsets of the labeled visibility clauses. It already shows that detecting *maximum* rank is NP-complete. Exact rank is a distinct function problem. We show that exact rank is SpanP-complete, even where each left vertex has at most three incident edges. All weights are one, and only one succinct rank instance is needed. For SpanP (counting distinct outputs of a nondeterministic polynomial-time transducer) see [Köbler, Schöning and Torán](https://doi.org/10.1007/BF00276023).

Membership: guess a subset of labels and an assignment. Output the subset if all selected clauses are true, and otherwise produce no output. Multiple witnesses produce the same output. The number of distinct outputs is the rank.

## Encode projected 3-CNF model counting into one rank

Let F be a width-at-most-three CNF with m clauses and designated variables x_1,...,x_k. Count distinct assignments of just these k variables extendible to a satisfying assignment of F; do not count the extensions. This problem is SpanP-complete: for any nondeterministic polynomial-time transducer, encode its output in fixed-length padded bits (with length indicated, if needed), and encode a valid accepting computation with those designated output bits using a polynomial-size Boolean circuit tableau. Convert the circuit to width-at-most-three clauses with gate witnesses and a forced true output; keep the designated bits, project out all other bits. Each distinct original output is represented once under the projection.

Append both unit clauses x_i and not-x_i for each i as new labels, even when an original clause has the same literals. Put M=m+2k. In a satisfying selection at most k of the new unit clauses can be selected, because both units for the same variable are inconsistent. Let c_(a,b) count the satisfying selections with a original clauses and b new units. In particular c_(m,k) is precisely the desired projected count: one unit from each pair fixes a distinct designated assignment, and the selected original formula is the whole of F.

Take L=2M+1 and B=2^L. Replace each original label by L(k+1) labeled copies and each added unit label by L copies. All copies are ordinary unweighted clauses; labels of copies are distinct. There are polynomially many new labels. A group is active when any of its copies is selected, and satisfiability depends only on the active groups. A group of t copies has 2^t-1 nonempty selections. Consequently the target rank R is exactly the following integer polynomial evaluated at B:
```
   Q(Z) = sum_(a<=m,b<=k) c_(a,b) (Z^(k+1)-1)^a (Z-1)^b,
   R = Q(B).
```
There is no need to falsely identify B^(k+1)-1 with (B-1)^(k+1). Each summand's degree is a(k+1)+b. The top possible exponent j=m(k+1)+k is reached only at (m,k); if that coefficient is zero, the degree drops. In the ordinary monomial expansion, the sum of absolute coefficients of Q is at most 2^M * 2^M: the number of selected original labeled subsets is at most 2^M, and expanding the product for any subset has coefficient L1 norm at most 2^(a+b)<=2^M. For j>=1 the contribution of all lower-degree terms to Q(B)/B^j has absolute value at most 2^(2M)/B=1/2. It is strictly less than 1/2 because the always-satisfiable empty selection has expansion norm 1, less than 2^M when j>=1. Thus rounding R/B^j to the nearest integer recovers c_(m,k), even when it is zero. For j=0 the ratio is exact. The bit lengths and the decoding are polynomial. One can also harmlessly increase L by one if a non-strict bound is preferred.

Translate the duplicated CNF to the succinct bipartite graph with a left vertex for each clause copy and a right vertex for each variable. Duplicate literals in a single clause may be removed. A tautological clause can be replaced, before duplication, by one positive unit of a fresh auxiliary variable occurring nowhere else, preserving all relevant subset satisfiability and projected counts. Empty clauses already correspond to isolated left vertices. Thus there is at most one edge per vertex pair, and left degree at most three. This establishes function hardness for the same compact rank family, not for explicit-matrix rank, and no hardness claim on bounded matching deficit. The gap between exact count and relative approximation matters: the decoding uses precise integer information, not a fixed relative accuracy oracle.

## Exact replay

600 small projected-CNF comparisons against direct witness enumeration and six separate brute force checks of the copy-group evaluation at L=1. These are tests of the encoding and decoding; the proof applies for unbounded instances. Standalone JavaScript (replace text by console.log).

```javascript
const pc=x=>{let n=0; for(;x;x&=x-1)n++;return n};
const truth=(C,x)=>C.some(l=>Boolean(x>>(Math.abs(l)-1)&1)===(l>0));
function check(F,n,k,brute){
 const G=[...F,...Array.from({length:k},(_,i)=>[[i+1],[-i-1]]).flat()];
 const m=F.length,M=G.length,L=2*M+2,B=1n<<BigInt(L),BO=B**BigInt(k+1)-1n,BU=B-1n;
 const witness=Array.from({length:1<<n},(_,x)=>G.reduce((S,C,i)=>S|(truth(C,x)?1<<i:0),0));
 const fits=S=>witness.some(R=>(S&R)===S);
 let R=0n;
 for(let S=0;S<1<<M;S++)if(fits(S)){
   const a=pc(S&((1<<m)-1)),b=pc(S>>m);
   if(b>k)throw Error("contradictory unit pairs");
   R+=BO**BigInt(a)*BU**BigInt(b);
 }
 const j=m*(k+1)+k;
 const projected=new Set();
 for(let x=0;x<1<<n;x++)if(F.every(C=>truth(C,x)))projected.add(x&((1<<k)-1));
 const K=B**BigInt(j);
 if((2n*R+K)/(2n*K)!==BigInt(projected.size))throw Error("wrong digit");
 if(brute){
   const ng=G.flatMap((_,i)=>Array(i<m?k+1:1).fill(i));
   if(ng.length>23)throw Error("oversize brute case");
   let E=0n;
   for(let S=0;S<1<<ng.length;S++){
     let g=0; for(let i=0;i<ng.length;i++)if(S>>i&1)g|=1<<ng[i];
     if(fits(g))E++;
   }
   let expected=0n;
   for(let S=0;S<1<<M;S++)if(fits(S))expected+=((2n**BigInt(k+1))-1n)**BigInt(pc(S&((1<<m)-1)));
   if(E!==expected)throw Error("duplicate evaluation mismatch");
 }
 return projected.size;
}
let seed=9123, tested=0;
const rnd=n=>((seed=(Math.imul(seed,1664525)+1013904223)>>>0)>>>9)%n;
for(let i=0;i<600;i++){
 const n=1+rnd(5),k=rnd(n+1),m=rnd(6);
 const F=Array.from({length:m},()=>Array.from({length:1+rnd(3)},()=> (rnd(2)?1:-1)*(1+rnd(n))));
 check(F,n,k,false); tested++;
}
const tiny=[[[],1,1],[[[1]],2,1],[[[2]],2,1],[[[1],[1]],2,0],[[[]],1,0],[[[1],[-1]],1,0]];
for(const [F,n,k] of tiny)check(F,n,k,true);
text({tested,explicitDuplicatedFixtures:tiny.length});
```
