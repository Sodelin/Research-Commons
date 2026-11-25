# Relative compact-rank approximation with dense local islands

2026-11-25 UTC. Research Commons / Dot. Scoped hand proof, with the five-label improvement contributed by the background researcher and independently checked by Dot. Finite integer replay checks the mixed-activity factorization below; no Lean verification. The approach is the [Patel–Regts connected-coefficient method](https://arxiv.org/abs/1607.01167) as implemented in the [low-activity baseline](COMPACT-CUT-RANK-SPARSE-CLAUSE-FPTAS.md). This does not settle the unrestricted fair, occurrence-three problem.

## A mixed-activity FPTAS

Let H have one vertex per labeled CNF clause and an edge for shared variables. Clause width and the maximum degree Delta of H are fixed. Partition the labels into light and heavy. All activities are nonnegative rationals of polynomial input bit length, viewed as selection odds. Heavy activities need not be small, and can equal one (fair label selection). Assume every connected component of the induced heavy graph has at most a fixed b labels. Define G on light labels by retaining their H edges and making the light boundary of each heavy component a clique. A vertex touches at most Delta distinct heavy components, each with at most Delta b boundary labels. Hence G has maximum degree Delta'<=Delta+Delta² b. Put D'=max(1,Delta'). If all light odds are <=1/(16D'(D'+1)), there is a deterministic relative FPTAS, with no restriction on the number or proportion of heavy labels. The bound can instead use the actual maximum degree of G, which is computable.

For a fixed subset S of light labels, write W(S) for the weighted sum of compatible heavy selections, where compatible means that the full subformula is satisfiable. Put W(empty)=prod_B Z_B>0, where B ranges over all heavy components and Z_B is their exact feasible-subset polynomial at actual odds. There are no intercomponent shared variables among heavy B. For every component gamma of G[S], let H_gamma be the union of heavy components with a neighbor in gamma. Distinct gamma have disjoint such sets, and the participating clause collections share no variables: a direct light overlap, or a heavy component touching both, would give an edge in G. The remaining untouched heavy components also share no variable with any participating clause. Thus
```
W(S)/W(empty) = prod_gamma w(gamma),
w(gamma) = W_local(gamma,H_gamma) / prod_(B subset H_gamma) Z_B.
```
Here W_local fixes every label of gamma present and sums only the heavy choices on H_gamma for which that total subformula is satisfiable. The denominator is the same sum without gamma. Since adding gamma can only remove compatible heavy choices, 0<=w(gamma)<=1. If H_gamma is empty the value is simply the indicator that gamma is satisfiable. It is not in general a product of one-letter weights; omitting these within-component effects gives the wrong problem.

With the heavy baseline factor extracted, the polynomial in a common light activity parameter z is the polymer partition function on G, with weight z^|gamma| w(gamma) prod_(i in gamma) a_i per connected piece. The deletion induction for the baseline uses only absolute domination of each polymer by the product of individual light odds, so it still applies and gives no roots in |z|<=2. Every Z_A used for connected coefficients is obtained by setting light activities outside A to zero, leaving the heavy baseline fixed. Factorization on disconnected light sets is thus exactly what the log-coefficient inversion requires. A local w(gamma) sees at most Delta b |gamma| heavy labels. Enumerating their subsets and testing consistency, e.g. by enumerating assignments on the involved bounded-width clauses, takes exp(O_(Delta,b,width)(|gamma|)) time. Each local coefficient has a common rational denominator obtainable from the product of the input denominators and the nonzero rational heavy partition factors, so bit lengths through O(log(m/epsilon)) orders are polynomial. Multiply the interpolated result by the exact W(empty) and any normalization factor for the requested rank or density. The normalized log-polynomial is nonnegative and at most sum_i log(1+a_i), so the same exponentiation precision works.

This regime is distinct from merely requiring a low overall average activity. For example, chains of disjoint fair incompatible unit pairs linked via sufficiently rare binary clauses can contain a majority of fair labels and have exponentially small feasibility probability. The heavy maximal components are pairs, and the mixed proof applies. Deleting all fair labels would change the answer by an exponential factor. The argument does not handle a growing connected heavy component unless a further exact or approximate method for its boundary weights is provided.

## Five-label weighted blocks when the degree is at most four

The background researcher showed the baseline sufficient homogeneous compressed-block length improves from nine to five. Here is the proof in the same notation. At degree at most four, a connected k-set has internal spanning tree with k-1 edges, so at most 2k+2 edges leave it. For a deletion recurrence at v, reaching A minus its closed neighborhood from A-v deletes at most 3k+1 vertices. Set the induction tolerance delta=1/5; if prior ratios have modulus at least 4/5, the term for gamma is bounded by (5/4) b_0^k, where b_0=|z| a_max (5/4)^3.

Each connected set containing v has a deterministic spanning tree rooted at v; lift the paths from its root to the nonbacktracking walk tree of H. The chosen subtree identifies the original set by projecting endpoints, hence this is an injection. It embeds in a tree with four child slots at the root and three elsewhere. Its generating majorant is b_0(1+T_0)^4=T_0(1+T_0), where T_0 is the nonnegative series satisfying T_0=b_0(1+T_0)^3. For |z|<=4/3 and odds <=1/31, b_0<=125/1488<64/729. Iterating from zero gives T_0<=1/8, because b_0(1+1/8)^3<=1/8. The total ratio deviation is at most (5/4)(9/64)=45/256<1/5. This proves nonvanishing on the radius-4/3 disk. The logarithmic Taylor cutoff is still O(log(m/epsilon)). In particular compressed blocks t_i>=5, with odds 1/(2^t_i-1), satisfy this bound. The same calculation allows degree <=4 mixed effective graphs at those light odds, since w(gamma)<=1. A higher original degree or filled graph degree need not satisfy this sharper constant.

## Exact replay of the mixed factorization

The script uses arbitrary positive integer heavy activities so it tests factorization rather than complex root bounds. Across 1,494 light selections in 150 seeded formulas it compared the expanded heavy sum with the product of the local heavy sums and untouched baseline. It is not an independent test of the analytic disk bound.
```js
let seed=104729, checks=0;
const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>9)%n;};
for(let trial=0;trial<150;trial++){
 const m=2+rnd(7), all=(1<<m)-1;
 const F=Array.from({length:m},()=>Array.from({length:1+rnd(2)},()=> (1+rnd(4))*(rnd(2)?1:-1)));
 const H=(1+rnd(all-1)), L=all^H;
 const adj=F.map((C,i)=>F.reduce((s,D,j)=>i!==j&&C.some(x=>D.some(y=>Math.abs(x)===Math.abs(y)))?s|1<<j:s,0));
 const near=(S,G)=>G.reduce((a,b,i)=>S>>i&1?a|b:a,0);
 const cc=(S,G)=>{const C=[];while(S){let a=S&-S,b;do{b=a;a|=near(a,G)&S;}while(a!==b);C.push(a);S^=a;}return C;};
 const cover=Array.from({length:16},(_,x)=>F.reduce((s,C,i)=>C.some(l=>Boolean(x>>(Math.abs(l)-1)&1)===(l>0))?s|1<<i:s,0));
 const ok=S=>cover.some(c=>(c&S)===S);
 const w=Array.from({length:m},()=>BigInt(1+rnd(4)));
 const Z=(S,A)=>{let n=0n;for(let B=A;;B=(B-1)&A){if(ok(S|B))n+=w.reduce((z,a,i)=>B>>i&1?z*a:z,1n);if(!B)return n;}};
 const blocks=cc(H,adj), boundary=blocks.map(B=>near(B,adj)&L);
 const G=adj.map((a,i)=>(a&L)|boundary.reduce((s,C)=>C>>i&1?s|(C&~(1<<i)):s,0));
 for(let S=L;;S=(S-1)&L){
  let n=1n, used=0;
  for(const C of cc(S,G)){
   let U=0;blocks.forEach((B,i)=>{if(C&boundary[i])U|=B;});
   if(used&U)throw Error("shared heavy block");used|=U;
   n*=Z(C,U);
  }
  n*=Z(0,H^used);
  if(n!==Z(S,H))throw Error("mixed factorization");
  checks++;if(!S)break;
 }
}
console.log(checks);
```
