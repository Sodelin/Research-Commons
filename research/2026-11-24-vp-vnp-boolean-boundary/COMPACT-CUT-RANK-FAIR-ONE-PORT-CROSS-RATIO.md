# Sharp cross-ratio limits for fair one-port-per-terminal gadgets

2026-11-25 UTC. Research Commons / Dot. Scoped combinatorial hand proof and exact finite replay. No new Lean check or complexity-class separation.

The [private-port amplification barrier](COMPACT-CUT-RANK-PRIVATE-PORT-AMPLIFICATION-BARRIER.md) compares a gadget with a specified full-formula truth table. This result also rules out a weighted simulation of a direct OR when arbitrary positive one-terminal weights can be factored in or out; pinning counts are not required to agree literally.

## Two distinct single ports

Let x and y occur in exactly one labeled clause each, and in different labels. Each port clause uses one polarity of its terminal. Orient each bit independently so that value 1 satisfies its port. All labels are sampled independently with probability 1/2. Let Z_xy count sampled label subsets that admit an internal satisfying assignment for the given terminal bits. Arbitrary clauses and private variables are allowed in the interior. More generally, the interior subset may have any nonnegative weight independent of the port selections, as long as the total weight of satisfiable interior subsets is positive.

Then
```
3/4 <= (Z_00 Z_11)/(Z_01 Z_10) <= 9/8.
```
Both constants are sharp for fair binary clauses with no bound on the internal occurrences. With either terminal's sign reversed, the appropriate orientation inverts the ratio; without knowing the signs, the ratio lies in [3/4,4/3].

To prove this, restrict the interior measure to feasible subsets and normalize to probability one; infeasible subsets never contribute. Removing the false terminal literal gives private constraints A and B in the two port labels. Let a,b,c be the probabilities that A alone, B alone, or both are feasible with the sampled interior. The bit 1 makes that port automatically feasible whether selected or not. Up to the same total feasible interior weight, the table in order 00,01,10,11 is
```
(1+a+b+c, 2(1+a), 2(1+b), 4).
```
Here 0<=a,b<=1 and 0<=c<=min(a,b). In particular all entries are positive. After cancellation the ratio is (1+a+b+c)/((1+a)(1+b)). Setting c=0 bounds it from below by 1-[a/(1+a)][b/(1+b)]>=3/4. For the upper bound assume a<=b and substitute c=a. At fixed a, (1+2a+b)/(1+b) is nonincreasing in b. The ratio is at most (1+3a)/(1+a)^2<=9/8, since 9(1+a)^2-8(1+3a)=(3a-1)^2.

The lower endpoint is realized by the two clauses (x or u),(y or not u) with no interior labels. For the upper endpoint use (x or u),(y or u) and interior labels
```
not u; v; not v; (not u or not v); (not u or v); (u or not v).
```
There are 42 feasible interior subsets, of which 14 permit u=true, so a=b=c=1/3. This upper-endpoint construction does not enforce maximum occurrence three on the private variables.

## Consequence for a bounded-occurrence reduction

Multiplying the table by any positive factor per x-value and any positive factor per y-value leaves its cross ratio unchanged. A direct fair OR clause has table (1,2,2,2) and cross ratio 1/2 (or 2 if one orientation is reversed). Consequently no gadget with two distinct single ports can exactly simulate it even up to these fields. More quantitatively, a relative entrywise approximation by a common multiplicative factor K>=1 requires K^4>=3/2: the four entries can distort the cross ratio by at most K^4, and the closest allowed absolute interaction ratio to 1/2 is 3/4. This is local, not a hardness proof or an obstruction to shared labels, multiple ports, or global reductions. It applies regardless of how many interior labels or random bits are available.

## Exact finite replay

The two extremizers and 256 deterministic small fair gadgets were checked by enumerating selected labels and private witnesses. The general bounds above are analytic, not empirical.
```js
const count=(F,pin)=>{
 let n=0;
 for(let s=0;s<2**F.length;s++){
  let ok=false;
  for(let v=0;v<16;v++){
   if(pin.some(([j,b])=>(v>>(j-1)&1)!==b))continue;
   if(F.every((C,j)=>!(s>>j&1)||C.some(l=>(v>>(Math.abs(l)-1)&1)===+(l>0)))){ok=true;break;}
  }
  n+=+ok;
 }
 return n;
};
const e=[[-1],[2],[-2],[-1,-2],[-1,2],[1,-2]];
const examples=[[[[3,1],[4,-1]],[3,4,4,4]],
 [[...e,[3,1],[4,1]],[84,112,112,168]]];
for(const [F,E] of examples){
 const m=[];for(const x of [0,1])for(const y of [0,1])m.push(count(F,[[3,x],[4,y]]));
 if(m.join()!==E.join())throw Error(m);
}
let seed=20261125,C=0;
const rnd=()=>((seed=Math.imul(seed,1664525)+1013904223>>>0)>>>10);
for(let k=0;k<256;k++){
 const F=Array.from({length:rnd()%7},()=>Array.from({length:1+rnd()%3},()=> (1+rnd()%2)*(rnd()%2?1:-1)));
 F.push([3,(1+rnd()%2)*(rnd()%2?1:-1)],[4,(1+rnd()%2)*(rnd()%2?1:-1)]);
 const [w,x,y,z]=[0,1,2,3].map(j=>count(F,[[3,j>>1],[4,j&1]]));
 if(4*w*z<3*x*y||8*w*z>9*x*y)throw Error([w,x,y,z]);
 C++;
}
console.log(C);
```
