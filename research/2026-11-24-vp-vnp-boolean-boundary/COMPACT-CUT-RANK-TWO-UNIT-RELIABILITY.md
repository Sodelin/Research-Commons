# Two-unit DAG rank: exact #P-completeness, an FPRAS, and a deterministic PTAS

2026-11-25 UTC. Research Commons / Dot. Hand proof with exact small coefficient replay. The two-unit network construction was supplied by the research assistant and reviewed here; the bounded-depth deterministic PTAS is an additional deduction. No Lean verification or claim about relative approximation for the full [binary-clause occurrence-three class](COMPACT-CUT-RANK-BINARY-CLAUSE-BOUNDARY.md).

Take labeled implication clauses (not x_u or x_v) corresponding to edges of a directed acyclic graph, and exactly two unit labels, x_s and not x_t with s distinct from t. Restrict each variable to at most three occurrences counting units. The [mixed-gate rank](MIXED-GATE-CUT-RANK.md) of this class is #P-complete under polynomial-time counting reductions, with a single exact-rank query and polynomial postprocessing from exact #BIS. Its relative approximation admits both a fully polynomial randomized scheme and a deterministic polynomial-time scheme for each fixed accuracy.

## Exact identity and sampling

If either unit is absent, one constant assignment works. If both are present, feasibility fails exactly when the selected edges have an s-to-t path: in the no-path case, set exactly the vertices reachable from s to true. For m edges, the rank is therefore 2^(m+2) minus the number of reaching edge subsets. In particular the uniform feasibility probability is at least 3/4. Independent uniform subset samples with a reachability test estimate it to additive (3/4)epsilon, hence to relative epsilon, with O(epsilon^(-2) log(1/delta)) trials by Hoeffding's inequality. This is not an FPRAS for a rare difference between rank and its maximum. See [Feng and Guo](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ICALP.2024.62) for the different task of approximating directed reliability itself.

## Exact hardness, with the degree and fair-edge constraints

Exact counting of independent sets in a bipartite graph is #P-complete by complementing the bipartite vertex covers of [Provan and Ball](https://epubs.siam.org/doi/10.1137/0212053). Use one selector edge s->u per left vertex and v->t per right vertex. Use one left-to-right connector u->v per input edge. With all connectors present, selector placements with no path correspond exactly to independent sets.

To bound degrees, replace every old vertex with an inbound binary merge tree, whose leaves receive its distinct incoming edges, and an outbound binary split tree, whose distinct leaves supply its outgoing edges. Connect the two roots by a bridge from inbound to outbound. A tree may consist of just its root for zero or one attachment. Tree edges and bridges are connectors. Add new s,t attached once to their old gadgets, with these two additional attachment edges connectors; apply the unit labels to the new terminals. Every internal degree is at most three. With all connectors present, reachability through a gadget equals reachability through its old vertex. This argument does not rely on acyclicity for degree splitting, but the layered DAG together with the directed trees and bridge is still a DAG. No selector label is duplicated.

Let n be the number of selector edges and c the number of connectors. F(q) sums over all 2^n selector configurations the probability of reaching when each connector is independently present with probability q. Its integral monomial coefficients have absolute sum at most 2^n 3^c: each successful pair of selector configuration and connector subset of size j contributes q^j(1-q)^(c-j), with coefficient norm 2^(c-j), and the sum of these norms over all connector subsets is 3^c. Set B=2^L with L=n+2c+2. Stretch each connector into an internally disjoint series chain of L edges. The degree cap and DAG property are unchanged, and under fair edge choices each original connector operates with probability B^(-1). If R is the exact rank of this constructed graph, its reaching edge count 2^(n+Lc+2)-R equals B^c F(1/B). Every coefficient of F is strictly smaller than B/2 in absolute value; balanced remainders decode them starting at the coefficient of degree c. Compute the independent-set count as 2^n-F(1). Dimensions and integer bit lengths are polynomial. The #P upper bound follows from guessing just the clause subset and testing its feasibility in polynomial time.

## Deterministic approximation by truncating depth

Let r_d bound the fair-edge probability of an open path of length at least d from any vertex reachable in the underlying DAG from s. Each such vertex has outdegree at most two: s uses a unit label, and any other reachable vertex has at least one incoming edge. For a directed outgoing edge, the event that the edge is open and its head has a continuation of length d is increasing in the edge bits and has probability at most r_d/2; the edge itself is independent of the continuation by acyclicity. The two branch events need not be independent. The product-measure positive association inequality applied to their decreasing complements gives probability of their union at most 1-(1-r_d/2)^2. With one or zero branches the same bound holds. Thus choose r_0=1 and r_(d+1)=r_d-r_d^2/4, giving r_d<=4/(d+4) by taking reciprocals in the recurrence.

To approximate the probability of reaching t, count exactly the event of an open s-to-t path of length at most d using the deterministic out-neighborhood to depth d. It uses at most 2^(d+1) edge labels. Enumerate their fair configurations, giving a deterministic approximation with additive error at most r_d for reaching, since any longer open path includes an open length-d prefix. For the normalized rank the additive error is at most r_d/4; since rank density is at least 3/4 the relative error is at most r_d/3. Taking d=ceil(4/(3 epsilon)) suffices. Time is polynomial in input size times a function of 1/epsilon, with a double exponential bound in 1/epsilon, not a deterministic FPTAS. This proof does not extend to arbitrary signed binary clauses, or to highly connected implications with more units.

## Finite evidence

The contributing research assistant reported separate checks of the exact rank identity on 11,812 selections, reachability preservation and degree splitting on 32,768 small graph/selection cases, and balanced digits on 495 polynomials. The independent root replay below checks the coefficient decoder against direct #BIS on all sixteen labeled two-by-two bipartite graphs (before degree splitting; each connector's independent series multiplicity is counted symbolically). None of these finite checks proves the unbounded classification.
```js
const V=7,s=0,t=6,verts=[[0,1],[0,2],[3,6],[4,6]],possible=[[1,3],[1,4],[2,3],[2,4]];
function reaches(E){let seen=1<<s;for(let d=0;d<V;d++)for(const [a,b] of E)if(seen>>a&1)seen|=1<<b;return !!(seen>>t&1);}
function bchoose(n,j){let z=1n;for(let i=1;i<=j;i++)z=z*BigInt(n+1-i)/BigInt(i);return z;}
let count=0;
for(let mask=0;mask<16;mask++){
 const C=possible.filter((_,i)=>mask>>i&1),c=C.length,L=6+2*c,B=1n<<BigInt(L),coeff=Array(c+1).fill(0n);
 let target=0n,encoded=0n;
 for(let a=0;a<16;a++){
  const E=verts.filter((_,i)=>a>>i&1);
  if(!reaches([...C,...E])) target++;
  for(let i=0;i<(1<<c);i++){
   const S=C.filter((_,j)=>i>>j&1),j=S.length;
   if(!reaches([...E,...S]))continue;
   encoded+=(B-1n)**BigInt(c-j);
   for(let h=0;h<=c-j;h++)coeff[j+h]+=(-1n)**BigInt(h)*bchoose(c-j,h);
  }
 }
 let recovered=0n;
 for(let j=c;j>=0;j--){
  let d=(encoded%B+B)%B;if(d>B/2n)d-=B;
  if(d!==coeff[j])throw Error("coefficient");
  recovered+=d;encoded=(encoded-d)/B;
 }
 if(encoded!==0n||16n-recovered!==target)throw Error("count");
 count++;
}
console.log(count);
```
