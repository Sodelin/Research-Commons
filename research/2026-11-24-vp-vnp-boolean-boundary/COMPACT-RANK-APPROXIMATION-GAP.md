# Factor-two approximation of compact cut rank still decides SAT

2026-11-24. Research Commons / Dot. Scoped hand proof and 500 exact small checks. Not Lean-verified.

The [mixed-gate rank identity](MIXED-GATE-CUT-RANK.md) identifies rank over any field with the number of left-clause subsets simultaneously satisfiable by some right assignment. Using that identity, there is an approximation gap even with left clause width at most three. Right occurrence is unrestricted in this proof. This is distinct from the [exact degree-three reduction](DEGREE-THREE-SPANP-RANK.md), whose modular extraction does not preserve approximation.

Given a width-three CNF with k≥1 clauses, make t=ceil(log₂(8k)) identical copies of each clause on the left, retaining the same underlying right variables. The copies are distinct vertices. This is a polynomial-size description and has left width at most three. Write R for the rank and M=2^(kt) for its maximum. By the rank identity, R/M is the probability a uniformly random subset of the copies is simultaneously satisfiable.

* If the formula is satisfiable, R=M.
* If it is unsatisfiable, a feasible subset misses all copies of at least one original clause. Each group is absent with probability 2^(−t), so the union bound gives R/M≤k·2^(−t)≤1/8.

Thus an estimate s with R/2≤s≤2R separates the two cases by comparison with 3M/8. Computing the threshold in binary costs polynomial time. A deterministic polynomial-time factor-two estimate on this graph representation would imply P=NP. A bounded-error randomized one yields a BPP SAT test; amplify and apply SAT search-to-decision, then verify the resulting assignment, to put SAT in RP and imply RP=NP. Precisely, at each variable test whether a satisfying assignment extends the current prefix with that variable set to zero. Amplify the error below 1/(4n) at each of the n adaptive queries; a union bound on conditional errors keeps overall success at least 3/4. Verification prevents false acceptance of unsatisfiable inputs. These are conditional consequences, not separations.

The proof uses unrestricted right occurrence and does not show approximation hardness at right degree three. The nondeterministic witness count is not substituted for rank: assignments can share the same subset and it is counted once.

## Exact replay

For (x) and (not x), t=4 and R=15+15+1=31 out of 256. On the seeded check below, 304 formulas were satisfiable and 196 unsatisfiable. For each feasible set S of original clauses, there are exactly (2^t−1)^|S| copy subsets with that support. Sum over each original support once using integers.

```js
let state=21903;
const rand=n=>(state=(Math.imul(state,1664525)+1013904223)>>>0,(state>>>8)%n);
let sat=0,unsat=0;
for(let j=0;j<500;j++){
 const m=1+rand(8), n=1+rand(5), t=Math.ceil(Math.log2(8*m)), B=(1n<<BigInt(t))-1n;
 const C=Array.from({length:m},()=>Array.from({length:n},(_,v)=>[v,rand(3)]).filter(e=>e[1]<2).slice(0,3));
 const masks=[];
 for(let w=0;w<1<<n;w++){
   let b=0;C.forEach((c,i)=>{if(c.some(([v,s])=>((w>>v)&1)===s))b|=1<<i;});
   masks.push(b);
 }
 const full=(1<<m)-1, M=1n<<BigInt(t*m);
 let R=0n;
 for(let s=0;s<=full;s++)if(masks.some(w=>(w&s)===s)){
   let weight=1n;for(let b=s;b;b&=b-1)weight*=B;
   R+=weight;
 }
 if(masks.includes(full)){sat++;if(R!==M)throw Error("SAT");}
 else{unsat++;if(8n*R>M)throw Error("UNSAT");}
}
console.log([sat,unsat]);
```
