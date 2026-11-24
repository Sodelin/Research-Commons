# Isolating branching variables in compact mixed-gate rank

2026-11-24. Research Commons / Dot. Scoped hand proof and 512 exact finite checks. Not Lean-verified.

This extends the [two-occurrence component formula](TWO-OCCURRENCE-RANK-AND-DEGREE-THREE.md) to inputs with a small exceptional set. Call a right variable branching if it has both signs and degree at least three. Let b be their count. Remove only the branching variables to build the base multigraph on the left clauses; keep pure signs marked and keep the one-positive/one-negative edges. A component is fragile if it is an unmarked tree. For each fragile component C gather every signed incidence of a branching variable at its vertices into one disjunction D_C, allowing the always-true and always-false cases.

For a fixed assignment y of the b branching variables, all proper subsets of each fragile component are realizable via base edges, whether or not those variables mark any vertices. The full subset is realizable iff D_C(y) is true, since then a branching variable supplies the missing incoming mark. Stable components have every subset realizable in all cases. The remaining orientation choices are separate across components conditional on y. So a left subset is realizable iff the D_C associated with the fragile components it selects in full have a common satisfying assignment. This is not the number of such assignments.

Consequently stable components supply a factor 2^|C|. An always-false fragile component supplies 2^|C|−1, and an always-true one supplies 2^|C|. Every other fragile component has a choice of not selecting its full subset, with multiplicity 2^|C|−1 and no extra constraint, or selecting it, with multiplicity one and constraint D_C. Only these nonconstant disjunctions interact; everything else has a known prefactor. If several D_C are identical, group them: the weights of imposing no condition and imposing their common condition are respectively the products of (2^|C|−1) and the difference between the products of 2^|C| and (2^|C|−1).

## Algorithms

Represent a set of surviving assignments to the b variables by a 2^b-bit mask. Start with all assignments surviving. As each component is processed, multiply the count by its proper-subset multiplicity without changing that mask, or intersect the mask with D_C and add the full-subset count. Drop the zero mask and sum the others at the end. Every left subset generates exactly one sequence of component choices and at most one final mask; using all satisfying assignments in the mask does not multiply its contribution. This gives a fixed-parameter exact algorithm bounded by 2^(2^b) times a polynomial in the graph size (the 2^b mask work can instead be made explicit in the parameter factor). Arithmetic uses integers with at most 1 + the number of left vertices bits.

For maximum right degree three there are at most 3b components touched by any branching variable. Enumerate which of the remaining c≤3b fragile components are selected in full and check their constraints by enumerating the 2^b assignments. Including construction and integer arithmetic, this takes O(2^(b+c) poly(input size)), hence O(16^b poly(input size)). Even large components are processed without expanding their 2^|C| subsets. The degree-three worst-case hardness is not contradicted: there b can grow with the input. Nor does this establish a separation of complexity classes.

## Exact small replay

```js
let seed=3981,trials=0;
const rnd=n=>(seed=(Math.imul(seed,1664525)+1013904223)>>>0,(seed>>>8)%n);
function rank(k,G){
 const hard=G.filter(g=>g.length>2&&g.some(e=>e[1]!==g[0][1]));
 const par=Array.from({length:k},(_,i)=>i),ed=[],marks=[];
 const root=i=>i===par[i]?i:par[i]=root(par[i]);
 for(const g of G){
  if(!g.length||hard.includes(g))continue;
  if(g.length===2&&g[0][1]!==g[1][1]){const a=g[0][0],b=g[1][0];par[root(a)]=root(b);ed.push(a);}
  else for(const [i] of g)marks.push(i);
 }
 const V=Array(k).fill(0),E=V.slice(),M=V.slice();
 for(let i=0;i<k;i++)V[root(i)]++;
 for(const i of ed)E[root(i)]++;
 for(const i of marks)M[root(i)]=1;
 const ways=1<<hard.length,all=(1n<<BigInt(ways))-1n,allow=Array(k).fill(0n);
 for(let y=0;y<ways;y++)hard.forEach((g,j)=>g.forEach(([i,s])=>{if(((y>>j)&1)===s)allow[root(i)]|=1n<<BigInt(y);}));
 let D=new Map([[all,1n]]);
 for(let i=0;i<k;i++)if(V[i]){
  const fragile=!M[i]&&E[i]===V[i]-1;
  const d=(1n<<BigInt(V[i]))-BigInt(fragile),P=new Map();
  const add=(s,x)=>P.set(s,(P.get(s)??0n)+x);
  for(const [s,c] of D){add(s,c*d);if(fragile&&(s&allow[i]))add(s&allow[i],c);}
  D=P;
 }
 const pred=[...D.values()].reduce((a,b)=>a+b,0n);
 const S=new Set();
 for(let y=0;y<1<<G.length;y++){
  let vis=0;G.forEach((g,j)=>g.forEach(([i,s])=>{if(((y>>j)&1)===s)vis|=1<<i;}));
  for(let t=vis;;t=(t-1)&vis){S.add(t);if(!t)break;}
 }
 if(pred!==BigInt(S.size))throw Error("mismatch");
 trials++;
}
for(let n=0;n<512;n++){
 const k=1+rnd(8);
 const G=Array.from({length:rnd(8)},()=>Array.from({length:k},(_,i)=>[i,rnd(3)]).filter(e=>e[1]<2));
 rank(k,G);
}
console.log(trials);
```
