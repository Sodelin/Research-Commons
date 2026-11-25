# Relative approximation forgets the long paths in the degree-three exact reduction

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof and finite integer checks; no Lean verification, general bounded-degree approximation algorithm, or class separation.

The [degree-three SpanP construction](COMPACT-CUT-RANK-SPANP-DEGREE-THREE.md) encodes the projected count in exact low-order information. This note proves a uniform relative approximation bound for its entire output family, and a multiplicative pruning rule for the more general [weighted high-occurrence core](EXACT-RANK-HIGH-OCCURRENCE-CORE.md). The conclusion concerns the reduction or a supplied core structure, not arbitrary matrices with small entries. For background on exact counting of projected assignments, see [Fichte et al.](https://arxiv.org/abs/2305.19212).

## Multiplicative pruning, even when the retained rank is tiny

In the weighted core a block of size t_i has inclusion multiplicity 1 and omission multiplicity 2^{t_i}-1. The family of jointly satisfiable selections of block labels is downward closed. Fix any set J of blocks to prune. Let A be the exact weighted count on the surviving labels (dropping all constraints in J), and F be the already extracted free factor. Then the original rank R satisfies

```
F A prod_{i in J}(2^{t_i}-1) <= R <= F A prod_{i in J} 2^{t_i}.
```

For each feasible surviving selection, omitting every J label is always feasible and contributes the lower factor. Counting all subsets of J, feasible or not, gives the upper factor. No selection that was infeasible on surviving labels can become feasible by adding constraints. Thus the upper estimate U exceeds R by at most sum_{i in J} 2^{-t_i} times U, by the elementary product bound. For 0<epsilon<=1, prune blocks with t_i >= ceil(log_2(2 max(1,m)/epsilon)), where m is the block count. Then U/(1+epsilon) <= R <= U. This relative guarantee needs no lower estimate of A other than A>0, and does not assume independence of feasibility events. After pruning, the prior exact witness-set DP need only track high-occurrence variables appearing in the surviving core constraints. With k such variables, the arithmetic is still 2^{O(2^k)} poly(input); no polynomial guarantee is asserted when k grows.

## Consequence for exact degree-three encodings

For an output of the labeled path construction, the same argument applies directly to its designated gadgets whether or not the canonical low-occurrence compression would group them differently. Prune all M paths. If T is the number of resulting clause vertices and L=2M+4 is the smallest path length parameter, then

```
(1-M 2^{-L}) 2^T <= R <= 2^T.
```

Indeed, any selection omitting at least one vertex per path is feasible, with every external assignment. Thus 2^T is a relative approximation to every output to exponentially small error in M, computable from the number of rows of the clause description. For M>=1, any inverse-polynomial-accuracy value oracle is permitted to return 2^T for all sufficiently large construction inputs. At fixed M the projected count can instead be computed directly after ignoring unused nondesignated variables. Consequently this metric encoding with one rank query cannot simply replace exact rank by polynomial relative precision in its coefficient recovery. This is not an obstruction to reductions with other queries or different graphs. In particular it puts no limit on approximating the *deficit* 2^T-R.

For an explicit near-full-rank obstruction even without paths, take the n+1 clauses x_1, (not x_i or x_{i+1}) for i=1,...,n-1, and not x_n. All together are inconsistent. Drop the first or last unit and use the all-false or all-true witness, respectively; drop the i-th implication and set x_1 through x_i true and the rest false. All proper subsets are feasible. The rank is exactly 2^{n+1}-1, on a graph of maximum degree two. Flipping the last unit yields rank 2^{n+1} at the identical clause count. Replacing every clause by its path gadget preserves minimal inconsistency: for any proper subset an omitted path vertex deactivates its original clause, and private witnesses can be chosen separately. With K disjoint copies of a minimally inconsistent T-clause example, ranks multiply, and the normalized deficit is 1-(1-2^{-T})^K <= K 2^{-T}. A constant normalized deficit from this operation alone requires exponentially many copies in T. A bounded-degree approximation hardness reduction would need to create a genuinely larger gap (or use a different encoding), not repackage the tiny exact deficit.

## Exact finite replay

The first loop checks the pruning sandwich on 512 small, deterministically generated weighted cores including empty and repeated clauses. The second checks 10 minimally inconsistent chains. These check finite integer arithmetic, not the general theorem.

```js
const sat=(F,n)=>{const H=[];for(let x=0;x<(1<<n);x++)H.push(F.reduce((s,C,i)=>s|(C.some(l=>((x>>(Math.abs(l)-1))&1)===+(l>0))?1<<i:0),0));return H;};
let seed=20261125;
const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>11)%n;};
for(let j=0;j<512;j++){
 const n=1+rnd(5),m=1+rnd(9),F=Array.from({length:m},()=>Array.from({length:rnd(5)},()=> (1+rnd(n))*(rnd(2)?1:-1))),t=Array.from({length:m},()=>1+rnd(9));
 const cut=1+rnd(10),H=sat(F,n);let R=0n,A=0n,Flo=1n,Fhi=1n;
 t.forEach(v=>{if(v>=cut){Fhi*=1n<<BigInt(v);Flo*=(1n<<BigInt(v))-1n;}});
 for(let S=0;S<1<<m;S++)if(H.some(x=>(x&S)===S)){
  let w=1n,keep=true;
  t.forEach((v,i)=>{if(v<cut&&!(S>>i&1))w*=(1n<<BigInt(v))-1n;if(v>=cut&&(S>>i&1))keep=false;});
  if(keep)A+=w;
  t.forEach((v,i)=>{if(v>=cut&&!(S>>i&1))w*=(1n<<BigInt(v))-1n;});
  R+=w;
 }
 if(R<A*Flo || R>A*Fhi)throw Error("bound");
}
for(let n=1;n<=10;n++) {
 const F=[[1],...Array.from({length:n-1},(_,i)=>[-i-1,i+2]),[-n]],H=sat(F,n);
 let count=0;for(let S=0;S<1<<F.length;S++)if(H.some(x=>(x&S)===S))count++;
 if(count!==(1<<F.length)-1)throw Error("minimal core");
}
console.log("512 weighted bounds and 10 minimal cores passed");
```
