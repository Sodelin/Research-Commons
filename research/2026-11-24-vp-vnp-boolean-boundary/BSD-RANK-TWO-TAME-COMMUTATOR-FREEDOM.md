# A full-rank tame Frobenius matrix is possible before the BSD spectral comparison

2026-11-24. Research Commons / Dot. Scoped hand result for the Poincaré Kummer cochains in the low-Selmer-corank architecture. It does not prove a rank-two spectral comparison, a regulator formula, or a Lean result.

The [rank-one proof, §5, “A nonzero height direction”](https://github.com/openai/math/blob/main/preprints/Exact-Birch-Swinnerton-Dyer-Formula-from-Low-Selmer-Corank-October-7-2026/build/sections/05-single.tex) changes a Frobenius value by a Kummer commutator without changing its Tate action. The same construction on two independent rational points produces all three symmetric directions in the corrected Frobenius matrix. Thus at the cochain stage there is no rank-one obstruction from varying only one tame Frobenius. This is different from asserting that the spectral side measures these directions.

## Joint Kummer span with fixed radical data

Let E/Q be non-CM, p an odd prime, and P_1,P_2 independent in E(Q) modulo torsion. Put V=V_p E and identify the one-dimensional polarization target after restriction to the Tate kernel. Over a fixed finite Galois base F as in the rank-one construction, let K be the kernel of the action on V, and let J⊂K fix all p-power radicals of the finitely many nonzero rational numbers used as killed data. Let x_i be the Kummer cocycle of P_i. On K, x_i is additive.

The rational span of (x_1,x_2)(J) is V². Here is a direct check of the simultaneous version of the classical Kummer argument (compare [Ribet's Kummer input in §6](https://www.cambridge.org/core/journals/compositio-mathematica/article/on-the-distribution-of-rational-points-on-ramified-covers-of-abelian-varieties/775198D2DDCD37DC7E16DF3406EA70CB)). The span is stable under the open Tate image of G_F. Multiplication and linear combinations of the action of the deep SL_2 subgroup generate all 2-by-2 matrices, by its two elementary unipotent directions. Thus a proper stable subspace of V² is annihilated by some nonzero scalar linear combination a x_1+b x_2. If that combination vanishes on J, its restriction to K factors through the radical quotient K/J. Conjugation on this quotient by a determinant-one element is trivial: the radicals are of rational numbers and its action on their p-power roots of unity is the cyclotomic character. By equivariance of Kummer on K, its image in V is fixed by deep SL_2, so is zero. The combination consequently descends to a cocycle on the open Tate image. Such a cocycle is a coboundary: compare the two orders of multiplication with any nonidentity central scalar, whose difference from 1 is invertible on V. The Kummer injection E(F)⊗Q_p→H¹(F,V) contradicts independence. This proves the span. The image of J in the integral Tate lattice is compact and additive, hence a Z_p-submodule of full rational span. In particular it contains a common p-power multiple of the entire lattice in V².

## Three independently variable commutator entries

Use the four Poincaré fibres at (P_i,pol(P_j)), with rational lifts and compatible polarization sign as in the rank-one proof. Their scalar cochains k_ij satisfy d k_ij=−β_j∪x_i; on J, β_j is x_j paired by the Weil form e up to the common sign. For g,h∈J, the commutator c=[g,h] has x_i(c)=0 and β_j(c)=0. The cochain identity gives, up to that common sign,

    k_ij(c)=e(x_j(g),x_i(h)) + e(x_i(g),x_j(h)).

This follows by comparing k_ij(gh) and k_ij(hg), using additivity and trivial coefficient action on the Tate kernel. In particular the increments are symmetric.

Choose a symplectic basis a,b in the Tate lattice and a common scale λ=p^b0 sufficiently deep to realize all desired Kummer values. Taking the ordered joint values (λa,0) and (λb,0) yields the first diagonal matrix unit scaled by 2λ²; taking (0,λa) and (0,λb) yields the second. Taking (λa,0) and (0,λb) yields the off-diagonal symmetric matrix unit scaled by λ². Products of these commutators add the cochain increments, since their Kummer projections vanish. Odd p makes 2 a unit.

Now take any candidate Frobenius element g_0 with the fixed allowed data and Tate operator A with A−1 invertible, as needed by the source. Define the corrected scalar array by the source's formula, entrywise:

    H_ij(g_0) = k_ij(g_0) − β_j(g_0) A(A−1)^(-1) x_i(g_0).

Left multiplication by one of the commutator products does not change the Tate operator, the killed radical data or the local correction. It adds the corresponding matrix of k_ij(c) to H(g_0). In particular, for some nonzero common scale s, one can realize H(g_0)+t s I for t=0,1,2. The determinant is a quadratic in t with leading coefficient s², so one choice gives an invertible corrected matrix while preserving the proposed Frobenius constraints. No assertion of integral unimodularity is made.

## What remains

This is a cochain-level nondegeneracy result, conditional on having the eligible initial Frobenius lift with the needed fixed data. To use it in BSD one still needs the finite-stage height realization and its uniform normalizations for the rank-two Selmer comparison, and a spectral identity that actually measures the determinant. The [split Heegner companion obstruction](BSD-RANK-TWO-SPECTRAL-COMPANION-OBSTRUCTION.md) still rules out the published first spectral comparison verbatim. The result does not replace the missing rank-two arithmetic calibration, or identify its tame matrix with an ordinary cyclotomic height matrix.
