# Exact clause-subset rank on incidence forests and bounded-width decompositions

2026-11-25 UTC. Research Commons / Dot, based on the companion background research, with independent hand review and exact replay below. No Lean verification, novelty-priority claim, or complexity-class separation.

Let F have labeled CNF clauses C_j. Each label has nonnegative integer weights w_j(0), w_j(1) for omission and inclusion. Sum the products of those weights over selections whose included clauses are jointly satisfiable. In particular unit weights give the [compact matrix rank count](MIXED-GATE-CUT-RANK.md). This is also weighted projected model counting for selector variables of clauses (not ordinary model counting); see [Fichte et al.](https://arxiv.org/abs/2305.19212) for the primal-width setting. We give a direct recurrence for this instance family and do not claim a new general projected-counting technique.

## Forest rule

Remove duplicate literals inside each clause; a tautological label contributes an independent factor w_j(0)+w_j(1) and is removed. Identical clause labels are not merged. Suppose the bipartite graph joining the remaining clause labels to their variables is a forest. The result applies to the original cleaned formula or the [weighted high-occurrence core](EXACT-RANK-HIGH-OCCURRENCE-CORE.md) if its incidence graph is a forest. See [Gaspers and Szeider](https://www.cse.unsw.edu.au/~sergeg/papers/GaspersS12icalp.pdf) for prior structural SAT work using incidence forests.

Root a component with edges at a variable. A message consists of three integer totals, indexed by the *complete* nonempty feasible set of values at its joining variable: {0}, {1}, {0,1}. Discard selections in the infeasible bin. At a variable, start with the free set of mass 1 and fold child messages by multiplying weights and intersecting sets. A selected subtree returning both possible boundary values is counted once, not twice. At a clause with parent literal L, for each child variable compute its total viable weight and the weight in the singleton that falsifies its literal. Let T and N be the two products of these quantities, with the empty product 1. Omission contributes w(0)T to the free state. Inclusion contributes w(1)(T−N) to the free state and w(1)N to the singleton satisfying L. Indeed, a child must be able to satisfy some literal for the parent to be free; the precise obstruction is every child being forced false. Distinct subtrees have disjoint internal variables and selectors. An isolated variable contributes 1, an isolated empty clause contributes w(0), and the overall answer is the product of the root totals and independent factors. There are O(vertices+edges) integer operations. Every stored count is at most the product of all w_j(0)+w_j(1) over its subtree, so bit complexity is polynomial (the all-zero case is immediate).

## Why it complements the high-occurrence and deficit cases

Take the two unit clauses x_i and ¬x_i at each variable and the n−1 positive clauses x_i∨x_(i+1), with unit weights. The graph is a tree. For n≥2 all n variables have at least three occurrences, and the matching deficit is 2n−1, since there are 3n−1 clauses and the n variables can all be matched to the positive units. From one end the variable states are (P,Q,P) in the order false, true, free, starting at (P,Q)=(1,1). The positive edge clause sends free weight 2(2P+Q)−P and true weight P; adding the next variable's two unit clauses gives (P',Q')=(3P+2Q,5P+2Q). The rank is 2P+Q. The matrix of this recurrence has trace 5 and determinant −4, giving R_(n+2)=5R_(n+1)+4R_n with R_1=3 and R_2=17. The n=100 compact formula has 299 labels and hence 2^299 expanded rows, but one needs only 99 two-integer updates to compute its rank.

## Direct extension with a supplied incidence tree decomposition

Hand argument only. Use a rooted nice incidence tree decomposition of width w, with empty root and leaves and exactly one introduce-edge node per incidence edge. Retain every clause's selector bit from its introduction to its forget along each branch. Condition on the bits of the boundary clauses in each bag. For each particular choice of internal selectors, record one **set of feasible boundary rows**. A row has one Boolean value per bag variable and one flag per bag clause saying whether some incident literal on an edge introduced below or at that bag has been true. Feasibility requires all already forgotten selected clauses to be satisfied and existentially quantifies all forgotten variables. A table entry counts internal selections, weighted once per forgotten clause, whose feasible row set equals its key. Drop empty sets because they can never become viable.

* Introducing a variable extends every row by each value; introducing a clause starts its flag at zero and conditions on its selector without counting or weighting it.
* Introducing an edge updates the clause flag by taking the OR with that edge's literal value.
* Forgetting a variable projects rows onto the remaining coordinates within the same set. Forgetting a clause filters rows by its flag if selected, projects the flag away, and applies its selector's weight once before summing by identical remaining keys. All of a forgotten clause's edges have been introduced by then.
* At a join, pair entries with equal boundary selectors, combine rows with equal boundary variable values, and take the OR of corresponding clause flags. Form the entire resulting row set for that pair of entries. Multiply the weights: the internal selections in the two children are disjoint. Every combined internal selection arises once in the pairing of entries, regardless of the number of compatible rows.

These operations give the invariant by induction since variables and clauses shared by both child subtrees are in the bag. At the root the only nonempty row set consists of the empty row. Each bag has at most 2^(w+1) selector settings and at most 2^(2^(w+1)) different row sets. Pairing all child entries at joins and processing their rows still takes 2^(O(2^w)) times polynomial in the decomposition and bit input sizes. This supplies exact tractability given the decomposition; it does not cover unrestricted incidence width. Only the forest recurrence was executed in the replay below.

## Independent exact replay

Run the following as JavaScript with `text` replaced by `console.log` in Node. It checks 800 signed forests against exhaustive assignments and clause subsets (including zero weights and empty clauses), and 100 chain ranks against the recurrence.

```javascript
function rank(n,F,W){
 const next=Array.from({length:n+F.length},()=>[]);
 F.forEach((C,j)=>C.forEach(l=>{const i=Math.abs(l)-1;
   next[i].push([n+j,l]);next[n+j].push([i,l]);}));
 const seen=new Set();
 function variable(i,parent){
   seen.add(i);let A=[0n,0n,0n,1n];
   for(const [j,l] of next[i])if(j!==parent){
     const B=clause(j,i,l), C=[0n,0n,0n,0n];
     for(let a=1;a<=3;a++)for(let b=1;b<=3;b++)if(a&b)C[a&b]+=A[a]*B[b];
     A=C;
   }return A;
 }
 function clause(j,parent,l){
   seen.add(j);let T=1n,N=1n;
   for(const [i,k] of next[j])if(i!==parent){
     const A=variable(i,j);T*=A[1]+A[2]+A[3];N*=A[k>0?1:2];
   }
   const [w0,w1]=W[j-n], A=[0n,0n,0n,w0*T+w1*(T-N)];
   A[l>0?2:1]=w1*N;return A;
 }
 let ans=1n;
 for(let i=0;i<n;i++)if(!seen.has(i)){const A=variable(i,-1);ans*=A[1]+A[2]+A[3];}
 for(let j=0;j<F.length;j++)if(!seen.has(n+j))ans*=W[j][0];
 return ans;
}
function brute(n,F,W){
 let ans=0n;for(let S=0;S<2**F.length;S++){
 let w=1n;for(let j=0;j<F.length;j++)w*=W[j][(S>>j)&1];
 for(let x=0;x<2**n;x++)if(F.every((C,j)=>!(S>>j&1)||C.some(l=> Boolean(x>>(Math.abs(l)-1)&1)===(l>0)))){ans+=w;break;}
 }return ans;
}
let seed=42073;
const rnd=n=>((seed=(Math.imul(seed,1664525)+1013904223)>>>0)>>>8)%n;
for(let z=0;z<800;z++){
 const n=1+rnd(6), m=1+rnd(8), F=Array.from({length:m},()=>[]),
 P=Array.from({length:n+m},(_,i)=>i);
 const root=i=>P[i]===i?i:root(P[i]);
 for(let step=0;step<24;step++){
   const i=rnd(n),j=rnd(m);
   if(root(i)!==root(n+j)&&rnd(3)===0){P[root(i)]=root(n+j);F[j].push((rnd(2)?1:-1)*(i+1));}
 }
 const W=F.map(()=>[BigInt(rnd(4)),BigInt(rnd(4))]);
 if(rank(n,F,W)!==brute(n,F,W))throw Error('forest '+z);
}
let A=3n,B=17n, preview=[];
for(let n=1;n<=100;n++){
 const F=[];for(let i=1;i<=n;i++){F.push([i],[-i]);if(i<n)F.push([i,i+1]);}
 const actual=rank(n,F,F.map(()=>[1n,1n]));
 if(actual!==A)throw Error('chain '+n);
 if(n<=5||n===100)preview.push(String(actual));
 [A,B]=[B,5n*B+4n*A];
}
text({forest:800,chains:100,preview});
```
