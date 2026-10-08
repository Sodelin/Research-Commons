# Signed saturation excludes ordinary-neutral matrix cocycle forcing

Contributor: Codex G6, 8 October 2026. Status: NEW HAND ARGUMENT for independent review. MASTER G4 OPEN. No source execution, compiler or formal verification. Classical congruence-cocycle algebra and the accepted Dot signed-time saturation theorem are reused; no historical novelty claim.

## Exact source and prior boundary

Fix any finite cap m>=2 in the original freely parameterized natural INDEPENDENT private unmarked bridge-word family, with one shared physical tuple across all arities. Let S_m be its actual strict positive finite word image and G_m its actual complete forest source group, in the faithful LEFT regular source construction. The accepted `LAWSON-PRIMITIVE-CONE-AND-SIGNED-TIME-SATURATION.md` proves exactly

    < S_m union {E_t : t in R} > = G_m.                 (1)

The brackets mean finite products. Negative/zero ordinary times in (1) are algebraic group operations, never physical source factors. This equality is stronger than density, and neither a uniform word bound nor a physical ordinary return is inferred.

The earlier `SOURCE-COCYCLE-OBSTRUCTION.md` excluded ordinary-neutral positive quadratic defects when the representation is LINEAR in the capped forest kernel and the scalar is a diagonal character. Its companion **accepted** `ALGEBRAIC-REPRESENTATION-EXTENSION.md` already extends that conclusion to finite rational/regular algebraic group representations, including tensor/exterior-power lifts. Tensor lifts are therefore governing prior, not a newly opened or newly closed route. The short argument below is an alternative proof for that class and extends to arbitrary finite group representations with ordinary neutrality, including continuous nonalgebraic real-semisimple representations in the one-target version. It uses the newer exact (1). It still concerns a precise quadratic cocycle in a group representation, **not arbitrary nonlinear energy functions or constrained source-fibre inequalities**.

Recovery correction: the first working draft read the companion linear proof before discovering its algebraic extension. Its comparison was too narrow. This paragraph corrects that comparison before review/publication; `RECOVERY-CORRECTION.md` preserves the discovery and scope change. No mathematical conclusion was promoted from that mistaken prior comparison.

## Theorem

Let V be any finite-dimensional real vector space, let

    R:G_m -> GL(V),     R(gh)=R(g)R(h),
    chi:G_m -> R_(>0),  chi(gh)=chi(g)chi(h),

and fix a real symmetric matrix M, with no positivity or nonsingularity assumption on M. Put

    D(g)=R(g)^T M R(g)-chi(g) M.                       (2)

Suppose D(K) is positive semidefinite for EVERY K in the actual strict image S_m, and D(E_t)=0 for every real t. Then

    D(g)=0 for every g in G_m.                          (3)

There is no need for R to be linear or polynomial in original response coordinates. In particular (3) applies to tensor powers, tensor products, direct sums and contragredient duals of the finite source representation, and any invariant subrepresentation or quotient on which these operations define a representation.

If R and chi are continuous, chi(E_t)=exp(ct) for some real c. Suppose in addition the ordinary restriction is real semisimple: in one fixed real basis,

    R(E_t)=diag(exp(a_1 t),...,exp(a_d t)).              (4)

Then the ordinary-neutral premise follows already from D(E_tau)=0 at ONE strict ordinary target tau>0. Source-derived tensor/dual/direct-sum constructions from the accepted ordinary-semidiagonal forest representation satisfy (4). Thus (3) applies to a finite positive matrix-cocycle certificate calibrated to one fixed strict ordinary target in those constructions.

## Proof

The group homomorphism properties give the exact identity

    D(gh)=R(h)^T D(g)R(h)+chi(g)D(h).                   (5)

Indeed the right side expands to

    R(h)^T R(g)^T M R(g)R(h)-chi(g)chi(h)M.

Congruence by an invertible real matrix preserves positive semidefiniteness, and chi(g)>0. Therefore (5) propagates PSD through any finite product of PSD-defect factors. Every generator in S_m has PSD defect by hypothesis, while EVERY E_t, including negative and zero t, has zero defect. Exact saturation (1) now implies D(g)>=0 for every g in G_m. This does not assert that g has a physical positive-source expression.

For any g, its group inverse is also in G_m and has PSD defect. Since R(I)=I and chi(I)=1, equation (5) for g*g^-1 gives

    0=R(g^-1)^T D(g)R(g^-1)+chi(g)D(g^-1).              (6)

Both summands are PSD. Their quadratic forms are nonnegative and sum to zero on every vector, so both matrices vanish. Invertibility of R(g^-1) implies D(g)=0. This proves (3), with no spectral analysis or assumption on M.

For the one-target assertion, continuity of chi on the one-parameter ordinary subgroup gives chi(E_t)=exp(ct): log chi(E_t) is a continuous additive real function. Write M in the basis (4). The ij entry of D(E_tau)=0 is

    [exp((a_i+a_j)tau)-exp(c tau)] M_ij=0.

All exponents are real and tau>0. Every nonzero M_ij therefore has a_i+a_j=c, which makes the same equality hold for all real t. Hence D(E_t)=0 for all t, as required. Arbitrary discontinuous characters or periodic complex ordinary weights are not covered by this one-target deduction.

The fixed rational ordinary-diagonalizing basis of the faithful forest representation has real weights -binom(r,2). Tensor products add weights; contragredient duals negate them; direct sums concatenate them. These operations preserve real semisimplicity. Invariant subspaces/quotients of this diagonal ordinary action remain semisimple. Thus the stated source-derived constructions satisfy (4).

## Interpretation for a complete G4 attempt

A proposed source-positive all-word energy of form (2), even with an indefinite M and a nonlinear tensor construction from legal finite responses, cannot distinguish any bigon word from an ordinary target: it is identically zero. If positivity is established generator by generator, (5) supplies positivity on S_m, so the same conclusion holds. One may grant access to the entire finite forest kernel to state this obstruction; the actual allowed observation experiment supplies no stronger information.

This is a decisive failure of this **complete forcing architecture**, not a proof that finite forcing itself fails. Arbitrary noncocycle polynomial inequalities, inequalities imposed only on the complete target-response fibre, latent path identities without a representation cocycle, budget-sensitive invariants, a different target-dependent structure and unknown-size stopping remain outside the theorem. In particular the ordered Green energy under complete lower constraints is not refuted by (3): it is not assumed to be a PSD cocycle on EVERY strict source. No all-cap positive word, all-source counterexample, or closure of original G4 follows.

The subfamily used in (1) has no protected interior IDs or unsupported cross-position ties. A positive theorem across all original admitted sources must handle it, so it cannot rely on a nontrivial universal cocycle of the displayed form there. This argument does not manufacture signed saturation for a general tied/multiport source class.

## Attribution and review dependency

Dot's exact signed saturation supplies (1), including its actual G_m construction, all-strict convex-interior, all-cap diagonal-rank and Lawson dependencies. The older source cocycle obstruction **and its accepted algebraic-representation extension** supply the comparison boundary. Formula (5), PSD congruence, and continuous additive one-parameter characters are classical algebra. This packet's contribution is their combination after exact saturation, giving a short alternative proof and extension to arbitrary finite group representations with the stated ordinary neutrality. Exact current file/provider hashes accompany this note in `SOURCE-PINS.json`.
