# Arbitrarily large unate heavy regions and a fully fair two-spin case

2026-11-25 UTC. Research Commons / Dot. Scoped hand proofs and exact finite replay; no new Lean verification. The first result extends the [mixed-activity compact rank FPTAS](COMPACT-CUT-RANK-MIXED-ACTIVITY-FPTAS.md) when all heavy clauses are compatible with a shared **literal polarity**, not merely jointly satisfiable. The second identifies a fully fair subclass with an exact translation to the classical two-spin framework.

## Eliminate unbounded unate heavy regions without filling their boundaries

Let the label-overlap graph have maximum degree Delta and the CNF labels bounded width. All activities are nonnegative rationals. Partition labels into light and heavy, all clauses nonempty. Assume every variable appears with only one sign among heavy labels; light labels have arbitrary signs. There is a default value of each heavy variable making its heavy literal true. By independent variable flips one may assume every heavy literal is negative and the default is zero. Heavy odds need not be small and the induced heavy graph can have unbounded connected components.

Make a graph G on light labels by keeping their shared-variable edges and making the set of light labels sharing a variable with each *individual heavy clause* a clique. This is not the boundary of a whole heavy connected component. Its degree is at most Delta+Delta². With D=max(1, max-degree(G)), if the light activities are at most 1/(16D(D+1)), the earlier polymer method yields a deterministic relative FPTAS.

To see the factorization, fix the selected light set S, and let V(S) be the variables appearing in those selected clauses. When deciding if a heavy selection is compatible with S, set every variable outside V(S) to its default. This never harms a selected light clause and it satisfies all heavy clauses with any variable outside V(S). Hence only heavy clauses all of whose variables are in V(S) can block feasibility on S. Each such clause has all of its selected light neighbors in one component gamma of G[S] by the clique rule; its variables all belong to V(gamma). Distinct components have disjoint variable sets by the direct light edges. For each gamma, let B_gamma be all heavy labels supported on V(gamma); these families are disjoint since clauses are nonempty. There are at most Delta*|gamma| such labels, because each touches a label of gamma. Bootstrapping from the resulting product, W(S)/W(empty)=prod_gamma w(gamma), where W(empty)=prod_B(1+a_B) over individual heavy labels, and w(gamma) is the weighted sum of heavy choices in B_gamma compatible with gamma divided by prod_{B in B_gamma}(1+a_B). Heavy labels outside these families contribute their unrestricted factors. The direction from compatible full selections to local feasibility follows by restriction; the converse glues local solutions and the default outside V(S). Thus 0<=w(gamma)<=1, and evaluating it exactly costs exponential time only in |gamma| for fixed width and degree. This proves all hypotheses of the earlier normalized connected-coefficient proof and gives the claimed FPTAS with polynomial bit length.

The distinction from mere global satisfiability matters: if the heavy pair is (not x OR y), (not y OR z), its two clauses can force z given x even when y is absent from the selected light variables. The proof above does not discard such intermediate variables for a non-unate heavy family.

## A fully fair graph family of maximum variable-graph degree six

For a simple graph H, take one positive unit per vertex and one negative binary clause (not x_v OR not x_w) per edge. All labels have odds 1. For a chosen set S of units, feasibility only forbids edge labels whose two endpoints are both in S, since set the non-unit variables to zero. If E_H(S) denotes those internal edges, the exact count of feasible label subsets is
    2^|E(H)| sum_{S subset V(H)} (1/2)^|E_H(S)|.
More generally for unit odds lambda_v in [0,1] and edge odds a_e in [0,1], extract prod_e(1+a_e) and the residual partition function is
    Z(H) = sum_S prod_{v in S} lambda_v prod_{e internal to S} b_e,
    b_e=(1+a_e)^(-1) in [1/2,1].
This is a soft repulsive two-spin model, not the independent-set model obtained by replacing edge odds by infinity.

Here is a direct self-contained sufficient contraction estimate using the exact [Li–Lu–Yin marginal recursion](https://arxiv.org/abs/1111.7064). Vertices of zero field can be deleted. For positive fields, let R_v be the occupied/unoccupied marginal ratio. On deleting v, telescope the changes of neighbor fields from lambda_u to b_vu lambda_u, in any fixed order. The exact ratio is
    R_v = lambda_v prod_j (1+b_vu_j R_{u_j})/(1+R_{u_j}).
In child j, the graph is H-v with the fields of earlier neighbors multiplied by their respective b; u_j itself has not yet had its field multiplied in this recursion call. This follows by writing the two v-pinned partition functions and changing one field at a time, using the linear decomposition in that field. All child calls continue to have fields <=1; their exact ratios as well as truncated ones lie in (0,1]. For r in (0,1],
    |d log((1+b r)/(1+r))/d log r| = (1-b)r/((1+r)(1+b r)) <= 1/6.
The expression is largest at b=1/2 and at r=1 on that interval (the r derivative has the sign of 1-b r²). If the maximum degree of H is <=6, all nodes except the root of the recursion have at most five children, as a parent neighbor was removed. Replacing a depth-L leaf ratio by its local field overestimates the true ratio by at most a factor 2^6, since each child factor is between b and 1. The log-error there is bounded by 6 log 2. The resulting root log-error is at most (5/6)^(L-1) times that constant, with root Lipschitz factor <=1. Take L=O(log(n/epsilon)) to get O(epsilon/n) log-error. Use Z(H)=prod_i(1+R_{v_i}) with each prior v_i deleted (pinned to zero); this follows by multiplying conditional unoccupied probabilities and using weight 1 for the all-zero configuration. The map log r to log(1+r) is 1-Lipschitz, so the total product has the desired relative approximation. Each truncated recursion has polynomial size in n and 1/epsilon, and can be evaluated in exact rational arithmetic with polynomial bit length: numerator and denominator lengths add over the expression tree, and each locally conditioned field is a product of at most original-degree many b factors and its input field. This applies at full fairness even on connected graphs of unbounded size. It is a conservative sufficient degree bound, not an approximation threshold claim. H is the variable graph here; its degree is not the overlap degree of clause labels.

The unrestricted fair occurrence-three question remains open in this project. The first theorem assumes unate heavy literals, and the fully fair application uses one unit per vertex and binary negative edges, not arbitrary mixed signs. Only the exact reductions, not the general theory of two-spin correlation decay, are the focus of this note.

## Exact replay

For 120 seeded small random formulas, the script checked the unate factorization across 3,100 selected light sets by exact enumeration. For 120 seeded graphs it also checked the fair two-spin count by checking joint satisfiability directly. These tests do not check the analytic error bound.

```js
let seed=17293, checks=0, pairChecks=0;
const rnd=n=>{seed=(Math.imul(seed,1664525)+1013904223)>>>0;return (seed>>>9)%n};
const sub=(m,f)=>{for(let q=m;;q=(q-1)&m){f(q);if(!q)break}};
const connected=(mask,G)=>{let out=[];while(mask){let a=mask&-mask,b;do{b=a;G.forEach((g,i)=>{if((b>>i)&1)a|=g&mask})}while(a!==b);out.push(a);mask^=a}return out};
for(let t=0;t<120;t++){
 const n=2+rnd(4), m=2+rnd(5), h=2+rnd(5), X=(1<<n)-1;
 const words=(k,unate)=>Array.from({length:k},()=>Array.from({length:1+rnd(3)},()=>{const i=1+rnd(n);return (unate||rnd(2)?-1:1)*i}));
 const L=words(m,false), B=words(h,true), danger=B.map(C=>C.reduce((v,l)=>v|1<<(Math.abs(l)-1),0));
 const vars=L.map(C=>C.reduce((v,l)=>v|1<<(Math.abs(l)-1),0));
 const all=(1<<h)-1;
 const yes=(F,j,x)=>F[j].some(l=>Boolean(x&(1<<(Math.abs(l)-1)))===(l>0));
 const ok=(A,C,def)=>{for(let x=0;x<=X;x++){if(x&~def)continue;if(L.every((_,i)=>!(A>>i&1)||yes(L,i,x))&&B.every((_,i)=>!(C>>i&1)||yes(B,i,x)))return true}return false};
 const count=(A,M,def)=>{let z=0n;sub(M,C=>{if(ok(A,C,def))z++});return z};
 const neigh=danger.map(d=>vars.reduce((a,v,i)=>d&v?a|1<<i:a,0));
 const G=vars.map((v,i)=>vars.reduce((g,w,j)=>v&w?g|1<<j:g,0)|neigh.reduce((g,w)=>w>>i&1?g|w:g,0));
 sub((1<<m)-1,A=>{
   let lhs=count(A,all,X), rhs=1n, used=0;
   for(const C of connected(A,G)){
     const U=vars.reduce((v,w,i)=>C>>i&1?v|w:v,0);
     const Q=danger.reduce((v,d,i)=>d&~U?v:v|1<<i,0);
     if(used&Q)throw Error("overlap");
     used|=Q; rhs*=count(C,Q,U);
   }
   rhs*=1n<<BigInt(h-used.toString(2).replaceAll("0","").length);
   if(lhs!==rhs)throw Error("unate");
   checks++;
 });
 const E=[];
 for(let i=0;i<n;i++)for(let j=i+1;j<n;j++)if(rnd(2))E.push((1<<i)|(1<<j));
 let actual=0n, predicted=0n;
 sub(X,A=>{
   predicted+=1n<<BigInt(E.filter(e=>(A&e)!==e).length);
   sub((1<<E.length)-1,C=>{for(let x=0;x<=X;x++)if((x&A)===A&&E.every((e,i)=>!(C>>i&1)||(x&e)!==e)){actual++;break}});
 });
 if(actual!==predicted)throw Error("two-spin");
 pairChecks++;
}
console.log({checks,pairChecks});
```
