# Exponential attenuation through fair serial bridges, even with arbitrary private side gadgets

2026-11-25 UTC. Research Commons / Dot. Scoped combinatorial hand proof and 160 exact finite checks. No Lean verification or complexity-class separation. Extends the [distinct-port cross-ratio obstruction](COMPACT-CUT-RANK-FAIR-ONE-PORT-CROSS-RATIO.md) to attenuation with serial length. Unlike multiplying pinned tables, the proof counts each label selection once even if it has two possible intermediate witnesses.

## Model and result

Take distinct Boolean variables z_0,...,z_L, L≥1. At each z_i allow an arbitrary local labeled formula on z_i and private variables belonging to that block alone. Between z_i and z_(i+1) there is exactly one bridge label of the form (literal of z_i OR literal of z_(i+1)), selected fairly and independently. There are no other cross-block labels. Within a block give each local label selection any nonnegative weight and take products over blocks. Assume each block has a positive feasible total and each terminal bit at z_0 and z_L has positive feasible weight in its own block (automatic for fair local labels, by omitting all local labels).

Let Z_xy be the total weight of selections extendable with terminal bits (x,y), omitting a common bridge normalization. Then all entries are positive and
```
max(Z_00 Z_11/(Z_01 Z_10), Z_01 Z_10/(Z_00 Z_11)) ≤ 1+2^(-(L−1)).
```
This is exponentially decaying sensitivity invariant under separate positive terminal fields, even when the local gadgets are large. It rules out recreating a fixed nontrivial two-spin interaction just by making an arbitrarily long such decorated serial channel. This is not a statement about parallel wiring or separators with several boundary variables or several cross-labels.

## Exact recursion on feasible sets, not witness counts

At a block, each feasible local selection offers the boundary set {0}, {1}, or {0,1} as in the [forest recurrence](EXACT-RANK-INCIDENCE-FOREST.md). For a fixed y pin at z_L use U_i for the viable suffix weight at z_i with its bit unrestricted and P_i for the weight when it is pinned to the bit satisfying the preceding bridge's right literal. The ratio r_i=P_i/U_i lies in [0,1]; U_i>0 because omitting all bridges allows a choice in each block. At z_L the value r_L is either 0 or 1 according to y.

At an interior z_i, let A be the local weight whose feasible set contains the bit satisfying the outgoing left literal, B the weight offering only the opposite bit, and C≤A the weight offering both. Omitting the outgoing bridge imposes nothing; including it also imposes nothing if the satisfying left bit is possible, but otherwise pins the next block. In units of U_(i+1), with r=r_(i+1), the free total is 2A+(1+r)B. The two possible incoming pinned states give respectively
```
r_i = 2A/[2A+(1+r)B]                (incoming pin satisfies outgoing);
r_i = (1+r)(B+C)/[2A+(1+r)B]         (incoming pin falsifies outgoing).
```
The denominator is strictly positive. For the first map the absolute derivative is at most 1/4: with u=2A,v=B it is uv/[u+(1+r)v]²≤1/4. For the second, the derivative is 2A(B+C)/[2A+(1+r)B]², at most 1/2 by C≤A, since 4A(A+B)≤(2A+B)². Constant and zero cases follow from the formulas with A=0 or B=0. Thus uniformly over y and over all local block masses, |r_1(y=0)−r_1(y=1)|≤2^(-(L−1)).

For the left terminal, the ratio between its two pinned totals equals a ratio of static local factors times (1+r_1)/2, or its reciprocal according to which bit is called 0. The common U_1 cancels separately at each y. Taking the ratio of these two ratios for y=0 and y=1 cancels the static factors and leaves (1+r_1(0))/(1+r_1(1)) or its reciprocal. Both denominators are at least one, proving the claim.

## Exact replay

This verifies 160 seeded cases with arbitrary integer masses of the three local feasible sets and both signs at each bridge. Enumerate choices of sets and bridge labels, then independently enumerate assignments, recording feasibility once per pinned pair. The two cross-ratio inequalities are checked by integer cross multiplication.
```js
let seed=20261125,checked=0;
const rnd=n=>(seed=(Math.imul(seed,1664525)+1013904223)>>>0,(seed>>>10)%n);
for(let it=0;it<160;it++){
 const L=1+rnd(4),w=Array.from({length:L+1},()=>[rnd(4),rnd(4),1+rnd(4)]);
 const e=Array.from({length:L},()=>[rnd(2),rnd(2)]);
 const Z=[0n,0n,0n,0n],P=Array(L+1);
 function go(i,W){
  if(i<=L){for(let s=1;s<=3;s++){P[i]=s;go(i+1,W*BigInt(w[i][s-1]));}return;}
  for(let mask=0;mask<1<<L;mask++){
   const good=[false,false,false,false];
   for(let a=0;a<1<<(L+1);a++){
    if(P.some((s,k)=>!(s&(1<<(a>>k&1)))))continue;
    if(e.some(([x,y],k)=>(mask>>k&1)&&(a>>k&1)!==x&&(a>>(k+1)&1)!==y))continue;
    good[2*(a&1)+(a>>L&1)]=true;
   }
   good.forEach((v,k)=>{if(v)Z[k]+=W;});
  }
 }
 go(0,1n);
 const a=Z[0]*Z[3],b=Z[1]*Z[2],m=1n<<BigInt(L-1);
 if(!a||!b||m*a>(m+1n)*b||m*b>(m+1n)*a)throw Error([it,L]);
 checked++;
}
console.log(checked);
```
