# Unbounded routing rank on each fixed target diagonal fibre

Contributor: Codex / laplace_recovery, 14 October 2026; consequence suggested by the lead G4 researcher.
Status: HAND consequence of accepted source suppliers; independent review pending. No new GKP theorem, latent-observation adapter, or full-menu G4 impossibility result is claimed.

## Statement

Fix any finite strict private target T with K cells and a positive ordinary segment of duration H. For every finite diagonal cap m and every integer J>=1, there is one finite strict private rival W such that

    d_n(W)=d_n(T)                  for every n<=m,
    c_2(W)<c_2(T),
    rank(T_(R_W)) >= 2^(K+J).

Here d denotes INDEPENDENT no-merger diagonals, c_2 denotes COMMON pair survival evaluated at the SAME physical tuple, and R_W is the auxiliary static routing kernel. Thus routing rank is unbounded on every finite diagonal fibre of this ONE fixed target. New coins may all be prescribed to equal any one gamma in (0,1); newly inserted arms can all be shorter than any prescribed positive bound.

## Inheritance and distinction from previous results

The accepted arbitrary-cap diagonal-return theorem and its fixed-coin short-arm strengthening are cited and pinned in the preceding [COMMON-interval corollary](TARGET-RELATIVE-DIAGONAL-FIBRE-COMMON-INTERVAL.md), SHA256 `99ef1325792eb144c47c6b2671f64635838b3cb5d30b007913e0f1a03bb9cca2`. No return construction is repeated here.

The [13 October GKP gate](../../../2026-10-13-dot-g4-gkp-observer-gate-0221z/DIRECT-GKP-CHRONOLOGY-ATTEMPT.md), SHA256 `d5e9f0f25633998c4f139e0291d85cfeb526b295cb4343ed1e31fecd263bcd16`, and its [review](../../../2026-10-13-dot-g4-gkp-observer-gate-0221z/INDEPENDENT-SCOPE-REVIEW.md), SHA256 `5dd794769af9198000187fabcb65a4906f8fc7622a64f3162b3bb2f326f705cd`, already reuse the rank formula `2^K` in the equal-arm class. The same finite tensor argument for unequal positive arms is written below to make the current rival scope explicit.

The earlier [finite-cap star-motif result](../../../2026-10-10-dot-g4-source-uniform-primitive-checkpoint-1258z/routing-motif-adapter/FINITE-CAP-STAR-MOTIF-NONRECOVERY.md) concerns equal complete forest prefixes and COMMON laws, with the target allowed to depend on the cap. The present simpler consequence instead fixes T throughout and matches only its finite diagonals. These different quantifiers and observation promises are not interchangeable.

## Proof

Split the selected target duration as H=J(H/J). By the inherited theorem, choose a nonempty strict word V with

    d_n(V)=exp[-(H/J) binom(n,2)],  n<=max(m,3).

Its N>=1 cells may use the prescribed fixed coin and short arms. Replace `E_H` inside T by J successive copies of V. These copies are distinct physical cells with fresh independent routing; repetition of numerical parameters does not identify their original routing events. Adjacent ordinary connectors merge to positive connectors. One resulting finite physical tuple defines all response rows.

No-merger diagonals multiply, so the inserted product has exactly the original diagonals through m. From the preceding corollary, `c_2(V)<exp(-H/J)`. COMMON pair survival also multiplies, hence the inserted product has pair survival smaller than `exp(-H)`, proving the strict COMMON inequality in W. Its total cell count is `K+JN>=K+J`.

For completeness let any strict private word U have L cells, total ordinary duration A, arm durations a_i,b_i>0, and coins g_i in (0,1). On the product route space `{0,1}^L` with positive product weights pi, its static kernel is

    R_U(x,y)=exp(-A) product_i M_i(x_i,y_i),
    M_i = [[exp(-a_i),1],[1,exp(-b_i)]].

The finite matrix of the associated integral operator, in the orthonormal indicator basis of L²(pi), is

    exp(-A) tensor_i [D_i^(1/2) M_i D_i^(1/2)],
    D_i=diag(g_i,1-g_i).

Every block has determinant

    g_i(1-g_i)[exp(-a_i-b_i)-1] < 0.

Every block therefore has rank two, and tensor-product rank gives `rank(T_(R_U))=2^L`. This calculation does not assert that a positive-valued kernel is a positive-semidefinite operator. Repeated parameters do not reduce the rank: tensor products of invertible blocks remain invertible. A step-function realization on an atomless probability space has the same nonzero rank, with zero action on the orthogonal complement of the step subspace.

Apply this to W with L=K+JN to obtain the stated bound. The clique density `t(K_n,R_U)=d_n(U)` follows directly because on the no-merger event every entering root persists through the entire word, so independent route vectors may be sampled once per root. No such static-type interpretation is imposed on histories after a merger.

## Exact consequence for a GKP bridge

There is no finite bound on rival routing rank determined by the target and any fixed finite list of its clique/no-merger values, even allowing arbitrary postprocessing of that list. This rules out the inference

    finitely many target clique values agree
      => a target-dependent finite bound on rival routing rank.

It does not contradict the rank formula, GKP's forcing theorem for its full graph-density family, or a bridge using richer legal forest observations. Where the GKP theorem applies to the fixed target kernel, its full motif list cannot agree on these different-rank rivals; those extra motif values have not become legal observations by this argument.

The rivals may have unequal arms, and their COMMON laws deliberately differ. Thus this is not a counterexample inside an equal-arm-only rival promise, nor on a fibre that also fixes COMMON observations. It is a scoped obstruction to a diagonal-only spectral-rank route in the original class that permits these positive unequal-arm cells.

No numerical search, compiler run, Lean verification, external-mixture substitution, or new source-count theorem is used. General finite INDEPENDENT forcing remains separate.
