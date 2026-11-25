# Exact compact cut rank is SpanP-complete at maximum degree three

2026-11-25 UTC. Research Commons / Dot. Hand proof under polynomial-time metric reductions, with 18 exact small encoding checks. No Lean verification, unconditional class separation, or bounded-degree approximation hardness is claimed.

The [mixed gate rank](MIXED-GATE-CUT-RANK.md) counts satisfactorily selectable labeled clauses over any field. The prior [SpanP reduction](COMPACT-CUT-RANK-SPANP-COMPLETE.md) bounded the clause width but repeated variables arbitrarily often. Here both sides of the unweighted bipartite graph have degree at most three. The [weighted high-occurrence core](EXACT-RANK-HIGH-OCCURRENCE-CORE.md) supplies the opposite boundary: with right degree at most two the exact rank is computable in polynomial time by a component product. The reduction below uses the path case of that core identity in reverse; it is not a bounded-degree hardness argument for approximate rank.

## Joint projection under occurrence splitting

Start with projected width-at-most-three CNF counting, as in the prior note, with k designated variables. Add one positive and one negative unit label per designated variable, including unused designated variables. For each variable separately, replace each occurrence by its own clone. For t>=2 clones add the t cyclic implications (not x_i or x_(i+1)), identifying x_(t+1)=x_1. For t<=1 no equality clauses are needed. Call original formula clauses and these new equality clauses mandatory labels; leave the 2k units separately labeled. All clauses have width at most three. A clone occurs in one original/added unit label and in at most two cycle clauses, hence at most three times. Empty original clauses are allowed; repeated original literal occurrences can be deduplicated first.

When all mandatory labels are selected, the implication cycles enforce equality of the clones of each variable. At most one unit per designated variable is then selectable. A satisfiable selection with exactly k added units and all mandatory clauses therefore fixes exactly one assignment of the designated variables extendible to the original formula. Conversely each such assignment yields exactly one selection, irrespective of the number of satisfying extensions. Write c_(a,b) for the number of satisfiable selections omitting a mandatory labels and b unit labels. The desired count is c_(0,k). Without all mandatory labels selected, no consistency constraint on the units is presumed; b ranges independently through 0,...,2k.

## Amplify omitted labels without increasing degree

Replace a clause C with a path of t distinctly labeled clauses, with t at least the width and at least two. For each path edge introduce a fresh variable occurring only at its two endpoints, once in each sign. Distribute the literals of C at distinct path vertices, one per vertex, keeping their signs. Every path clause now has width at most three and every new variable has occurrence two. With external variables fixed, a chosen subset of the path clauses is satisfiable whenever it is proper: root the path at an omitted vertex and use each edge to satisfy its child. The full path is satisfiable precisely when some external literal in C is true. If one is true, root at its vertex; if none is true, the t-1 edge variables can cover at most t-1 vertices. The private path variables of different labels are disjoint. Hence the full path gives one way to activate C, while all 2^t-1 proper subsets give independent ways to omit C. This is a multiplicity of subsets, not a count of witnesses.

Let m be the number of mandatory labels and M=m+2k. Set L=2M+4, B=2^L and w=2k+1. Use paths of length Lw vertices for mandatory labels and L for units. The single resultant compact rank R satisfies
```
R = Q(B),  Q(Z) = sum_(a=0..m, b=0..2k) c_(a,b) (Z^w-1)^a (Z-1)^b.
```
The construction has polynomial size. The sum of absolute monomial coefficients of Q is at most 2^(2M): there are at most 2^M admissible labeled selections, each contributes a polynomial of coefficient norm at most 2^(a+b)<=2^M. In particular every coefficient lies strictly between -B/2 and B/2. Recover them exactly by repeatedly taking the unique balanced remainder mod B, subtracting it and dividing by B. The degree is at most mw+2k, so no unbounded search is required.

Finally the displayed basis polynomials are monic with pairwise distinct leading degrees aw+b. Starting at the largest degree and subtracting the recovered multiple of its basis polynomial gives all c_(a,b) by triangular back-substitution, in particular c_(0,k). Binomial expansions and integer sizes are polynomially bounded in bits. SpanP membership is unchanged: output a labeled subset iff a nondeterministic assignment satisfies it. This proves the claimed exact complexity on the same compact matrix model. Ordinary explicit-matrix rank and relative approximations are not addressed.

A separate simple consequence of the occurrence split **without paths** is NP-completeness of detecting full rank at maximum degree three: all formula and cycle clauses must then be satisfied, which is equivalent to original satisfiability. Thus finding the first right-degree boundary does not require using the exact function reduction to decide SAT.

## Exact replay

On each formula below test k=0,1,2 (designated variables first). To test the coefficient-encoding arithmetic after the mandatory equalities, enumerate all subsets of original clauses and added units and test satisfiability directly. Build R by the formula, recover balanced coefficients, back-substitute, and compare c_(0,k) to direct projected assignment counts over three Boolean variables. The 18 checks passed. They check encoding arithmetic, not an unbounded gadget family or a formal proof.
```js
const fs=[[[1,2],[-1]],[[1],[-1]],[[1,2],[-2,3]],[[],[1]],[[1,-2],[-1,2]],[]];
const hit=(C,x)=>C.some(l=>((x>>(Math.abs(l)-1))&1)===+(l>0));
const choose=(a,b)=>{let z=1n;for(let i=1;i<=b;i++)z=z*BigInt(a-i+1)/BigInt(i);return z};
let checks=0;
for(const F of fs)for(let k=0;k<=2;k++){
 const G=[...F,...Array.from({length:k},(_,i)=>[[i+1],[-i-1]]).flat()];
 const m=F.length,M=G.length,w=2*k+1,B=1n<<BigInt(2*M+4),D=m*w+2*k;
 const sat=Array.from({length:8},(_,x)=>G.reduce((s,C,i)=>hit(C,x)?s|(1<<i):s,0));
 let R=0n;
 for(let S=0;S<1<<M;S++)if(sat.some(x=>(x&S)===S)){
  let a=0,b=0;
  for(let i=0;i<M;i++)if(!(S>>i&1)){if(i<m)a++;else b++;}
  R+=(B**BigInt(w)-1n)**BigInt(a)*(B-1n)**BigInt(b);
 }
 const q=[];
 for(let j=0;j<=D;j++){
  let d=((R%B)+B)%B;
  if(d>B/2n)d-=B;
  q.push(d);R=(R-d)/B;
 }
 let got=0n;
 for(let j=D;j>=0;j--){
  const a=Math.floor(j/w),b=j%w,c=q[j];
  if(a===0&&b===k)got=c;
  for(let i=0;i<=a;i++)for(let l=0;l<=b;l++)
   q[i*w+l]-=c*choose(a,i)*choose(b,l)*((-1n)**BigInt(a+b-i-l));
 }
 const expected=new Set();
 for(let x=0;x<8;x++)if(F.every(C=>hit(C,x)))expected.add(x&((1<<k)-1));
 if(got!==BigInt(expected.size))throw Error("coefficient mismatch");
 checks++;
}
console.log(checks);
```
