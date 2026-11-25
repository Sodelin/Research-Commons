# Exact all-fair OR obstruction for isolated degree-three four-port cores

2026-11-25 UTC. Research Commons / Dot. Exhaustive finite computation with a hand completeness argument, not a Lean verification or a complexity-class separation.

Take two local ports on x and two on y, with one active literal polarity per terminal (relabel pins so 1 satisfies both ports). Every port is a two-literal clause joining its terminal to one private literal. Ports can share private variables or even repeat a clause, with labels sampled independently and fairly. Every private variable in the gadget occurs in at least one port; the interior consists only of labeled clauses of width at most two on those variables. Each private variable occurs in at most three labels total, and all interior labels are also sampled independently and fairly. As in the [prior two-pair note](COMPACT-CUT-RANK-ALL-FAIR-OPPOSING-PRIVATE-PAIR-OBSTRUCTION.md), let Z_xy count feasible label subsets, not witnesses.

The exact minimum of Z_00 Z_11 / (Z_10 Z_01) in this model is **17/32**, attained with opposing ports on two private variables and one mixed bridge. The exact minima conditional on the number of distinct private variables are:
```
private variables    normalized port layouts   cores tested     minimum ratio
2                     28                        252              17/32
3                     12                        5,832            39/64
4                      1                        37,164           161/256
```
One variable cannot carry all four ports at degree three. In the four-distinct case the sharp witness uses all four pairwise conflict edges between the two sides; its pin table is (161,256,256,256). The direct fair OR table (1,2,2,2) has ratio 1/2, and independent positive row/column scalings cannot change it.

## Why the replay is exhaustive

Fix port label order x,x,y,y. A restricted-growth partition of four slots enumerates every incidence pattern up to private-variable renaming; reject a fourth incidence on one private variable. Independently flip each private variable so its first port is positive, and enumerate all signs of the remaining port occurrences. Swapping or renaming port labels need not be quotiented out for exhaustiveness. The only nontrivial internal clause types are signed units and signed clauses on two distinct private variables; repeated-literal clauses are equivalent to units and tautologies contribute only independent common factors. The nondecreasing multiset traversal permits repeated labeled clauses and spends one remaining degree at each incident variable. No further private variables are allowed in this result. A collection disjoint from the ports and all of these variables only multiplies the four counts by a common factor.

For each fixed multiset, a map from allowed assignment masks to multiplicities counts all selected subsets of the interior. The absent transition leaves a mask unchanged, and the present one intersects it with the truth set of the clause. Empty assignment masks can be discarded permanently. For each terminal pin, count each of the sixteen possible port subsets once if it can intersect the allowed assignment mask. This counts assignments only to test existence; it never counts multiple witnesses. All counts and products are exact integers in JavaScript's safe range: the number of private variables is at most four, and the number of labels at most twelve. The final checks include independent brute force on the two extremal examples.

## Executable replay

```javascript
function run() {
let layouts=0,instances=0,eq=0,bestN=1,bestD=1,witness=null,byVars={};
function layout(count) {
 const n=count.length,all=(1<<(1<<n))-1; // n <= 4
 const L=Array.from({length:2*n},(_,i)=>(i%2?-1:1)*(1+(i>>1)));
 const OK=l=>{let a=0;for(let u=0;u<1<<n;u++)if(Boolean(u&(1<<(Math.abs(l)-1)))===(l>0))a|=1<<u;return a};
 const W=L.map(l=>({c:[l],mask:OK(l)}));
 for(let i=0;i<L.length;i++)for(let j=i+1;j<L.length;j++)if(Math.abs(L[i])!==Math.abs(L[j]))W.push({c:[L[i],L[j]],mask:OK(L[i])|OK(L[j])});
 const cap=count.map(x=>3-x), k=[],first=new Set;
 const row=byVars[n]??={layouts:0,instances:0,N:1,D:1};
 function signs(i) {
  if(i===4){core();return;}
  const t=ports[i];
  k[i]=t+1;
  if(first.has(t)){signs(i+1);k[i]=-(t+1);signs(i+1);}
  else{first.add(t);signs(i+1);first.delete(t);}
 }
 function core(){
  layouts++;row.layouts++;
  const pm=Array.from({length:4},(_,pin)=>Array.from({length:16},(_,m)=>{
   let s=all;for(let i=0;i<4;i++)if((m>>i&1)&&!(pin>>(i>>1)&1))s&=OK(k[i]);return s;
  }));
  const cache=new Map;const weight=s=>{if(!cache.has(s))cache.set(s,pm.map(p=>p.reduce((a,b)=>a+!!(b&s),0)));return cache.get(s)};
  const g=[];
  function search(start,V){
   const z=[0,0,0,0];for(const [s,a] of V)weight(s).forEach((t,i)=>z[i]+=a*t);
   const N=z[0]*z[3],D=z[1]*z[2];
   if(!D||!N)throw Error('zero count');
   if(2*N===D)eq++;
   if(N*row.D<row.N*D){row.N=N;row.D=D}
   if(N*bestD<bestN*D){bestN=N;bestD=D;witness={ports:[...k],interior:g.map(i=>W[i].c),z};}
   instances++;row.instances++;
   for(let i=start;i<W.length;i++){
    const {c,mask}=W[i];if(c.some(l=>!cap[Math.abs(l)-1]))continue;
    for(const l of c)cap[Math.abs(l)-1]--;g.push(i);
    const A=new Map(V);for(const [a,b] of V){const s=a&mask;if(s)A.set(s,(A.get(s)??0)+b)}
    search(i,A);g.pop();for(const l of c)cap[Math.abs(l)-1]++;
   }
  }
  search(0,new Map([[all,1]]));
 }
 signs(0);
}
const ports=[],degrees=[];
function partition(i){
 if(i===4){layout(degrees);return;}
 for(let a=0;a<=degrees.length;a++){
  if(degrees[a]===3)continue;
  ports[i]=a;degrees[a]=(degrees[a]??0)+1;
  partition(i+1);if(--degrees[a]===0)degrees.pop();
 }
}
partition(0);return {layouts,instances,eq,bestN,bestD,witness,byVars};
}
const out=run();
if(out.layouts!==41||out.instances!==43248||out.eq!==0||
   32*out.bestN!==17*out.bestD) throw Error(JSON.stringify(out));
for(const [n,l,c,p,q] of [[2,28,252,17,32],[3,12,5832,39,64],[4,1,37164,161,256]]){
 const r=out.byVars[n];
 if(r.layouts!==l||r.instances!==c||r.N*q!==r.D*p)throw Error(JSON.stringify(r));
}
function direct(k,clauses) {
 const n=Math.max(...k.map(Math.abs));
 const lits=(g,v)=>g.some(l=>Boolean((v>>(Math.abs(l)-1))&1)===(l>0));
 return Array.from({length:4},(_,pin)=>{
   let z=0;
   for(let m=0;m<(1<<clauses.length);m++)for(let b=0;b<16;b++){
     if(Array.from({length:1<<n},(_,v)=>v).some(v=>
       clauses.every((g,i)=>!(m>>i&1)||lits(g,v))&&
       k.every((l,i)=>!(b>>i&1)||(pin>>(i>>1)&1)||lits([l],v)))) z++;
   }
   return z;
 });
}
for(const [k,G,expected] of [
 [[1,2,-1,-2],[[1,-2]],'17,32,32,32'],
 [[1,2,3,4],[[-1,-3],[-1,-4],[-2,-3],[-2,-4]],'161,256,256,256']
]) if(direct(k,G).join()!==expected) throw Error('direct witness');

```

This strictly isolates the remaining all-fair design question: within this four-port degree cap, a successful gadget would need new private variables not appearing at the terminals, a different terminal architecture, or a different simulation criterion. The computation does not give a lower bound for gadgets with such auxiliary variables or for general compact SAT. The earlier hand obstruction with arbitrary surroundings applies only to its special opposing two-pair incidence pattern.
