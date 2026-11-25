# Sharp maximum-degree threshold for the fully fair unit-and-edge count

2026-11-25 UTC. Research Commons / Dot. Consequence of published antiferromagnetic two-spin theorems via our exact rank reduction, with an exact integer certificate for the parameter boundary. Not a new spin-system theorem, not Lean verified, and not a result about P vs NP or arbitrary occurrence-three formulas.

Start from the [unit-and-edge translation](COMPACT-CUT-RANK-UNBOUNDED-UNATE-HEAVY.md): for a simple graph G, give each vertex a positive unit clause and each edge a negative binary clause, with all labels selected at equal probability. The feasible count, or compact rank in the clause-subset reduction, is
    R(G)=2^|E| sum_(S subset V) (1/2)^|E(S)|.
The feasibility probability is R(G)/2^(|V|+|E|), so all three quantities (rank, probability, and residual partition function) are equivalent for relative approximation. The empty subset is always feasible.

**Threshold.** There is a deterministic FPTAS on graphs of maximum degree at most 11. On 12-regular graphs, no FPRAS exists unless NP=RP, so the same obstruction holds on the class with maximum degree at most D for every fixed D>=12. These are degrees of the variable graph. A variable of degree D appears in D+1 labels, counting its unit. The hard class here does not fit the occurrence-three target.

## Certificate at the regular tree boundary

Use two-spin interaction matrix with entries A_00=A_01=A_10=1 and A_11=1/2 and field 1. In the notation of [Li, Lu and Yin](https://arxiv.org/abs/1111.7064) this is (beta,gamma,lambda)=(1/2,1,1), ordering the states so the occupied ratio uses beta in the numerator. On the (d+1)-regular tree the cavity recursion is
    f_d(r)=((1+r/2)/(1+r))^d.
Its positive fixed point r_d is unique by the monotonic decrease of f_d and lies in (0,1). At that point
    |f'_d(r_d)|=d r_d/[(1+r_d)(2+r_d)].
For fixed d the expression on the right increases for 0<r<1 (its derivative has the sign of 2-r²). For every d=1,...,10, a rational u in the exact replay satisfies f_d(u)<u and d u/[(1+u)(2+u)]<1. Thus the model is in strict tree uniqueness for each branching d<=10. Li–Lu–Yin's up-to-degree uniqueness theorem gives an FPTAS on all graphs of maximum degree 11, not just regular graphs. This uses uniform fair weights, unlike the heterogeneous direct degree-six bound in the earlier note.

For d=11, the rational l=279/1000 satisfies f_11(l)>l and 11 l/[(1+l)(2+l)]>1. Thus r_11>l and the fixed point is unstable. Equivalently f_11 composed with itself has derivative greater than one there and maps [0,1] into itself. It has additional fixed points by the intermediate value theorem: near r_11 its displacement changes from negative below to positive above, whereas at 0 the displacement is positive and at 1 negative. Since f_11 itself has only one fixed point, these yield distinct even/odd boundary messages (tree nonuniqueness).

## Transfer the hardness to label-subset rank

For b=1/2, factor b^((x+y)/2) per edge out of the original weight b^(xy), x,y in {0,1}. The remaining symmetric edge matrix has equal diagonal entries 1 and off-diagonals b^(-1/2)>1, and on a D-regular graph the field of the occupied state is b^(D/2). This is an antiferromagnetic Ising system with constant external field. The finite-volume Gibbs weights are identical after this reparameterization (up to the known partition normalization if using spin values -1 and +1); the same local equivalence holds on the D-regular tree and preserves uniqueness or nonuniqueness. The [Sly–Sun hardness theorem](https://arxiv.org/abs/1203.2602) for antiferromagnetic Ising in the regular-tree nonuniqueness region now applies at D=12, and the exact rank map only adds the known factor 2^|E|. Equivalently one can apply the two-spin consequence of [Galanis, Stefankovic and Vigoda, Theorem 1.5 and the discussion after it](https://arxiv.org/abs/1305.2902). No numerical threshold, conjectural intermediate degree, or promise that the original formula is unsatisfiable enters.

This resolves the approximation boundary for this particular fair encoding, not the general compact-rank problem. A next target is the different low-occurrence mixed-sign family; lowering degree merely by cloning variables would require proving preservation of the distribution of **selected** clause labels, not only equivalence of the fully selected SAT instance.

## Exact integer replay

The two comparisons per degree are obtained by clearing positive denominators from f_d(a/B) versus a/B and the closed-form derivative bound. All 22 strict comparisons were executed.

```js
const B=1000n;
const hi=[781,647,555,489,438,398,366,339,317,297];
for(let d=1n;d<=10n;d++){
 const a=BigInt(hi[Number(d-1n)]);
 if(!(B*(2n*B+a)**d < a*(2n*B+2n*a)**d)) throw Error("upper bracket "+d);
 if(!(d*a*B < (B+a)*(2n*B+a))) throw Error("unique "+d);
}
const a=279n,d=11n;
if(!(B*(2n*B+a)**d > a*(2n*B+2n*a)**d)) throw Error("lower bracket");
if(!(d*a*B > (B+a)*(2n*B+a))) throw Error("nonunique");
console.log("22 strict integer comparisons passed");
```
