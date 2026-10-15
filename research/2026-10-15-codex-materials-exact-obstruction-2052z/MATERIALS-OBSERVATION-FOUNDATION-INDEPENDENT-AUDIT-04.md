# Materials observation/recovery foundation: independent contract audit 04

15 October 2026. Existing mathematical/source auditor. **Definition/hand/source audit only.** No formal implementation, compiler, probability experiment or checker replay occurred.

The completed obstruction, independent reviews, uncompiled conditional adapter and original evidence remain unchanged. [Custody is closed](https://github.com/Sodelin/Research-Commons/blob/d7d106cc8c9e044d303366fe50ecb2c1a3814704/research/2026-10-15-astra-materials-kernel-adapter-2035z/obstruction-review-r1/ORIGINAL-ARTIFACT-CUSTODY-CLOSURE-02.md). Its one-attempt result does not imply block-power or recorded-cadence non-lumpability. This audit addresses the newly selected foundation contract, independently of its formal implementation; it does not restart program design or the prior lane's baseline proof/references.

## Actual cross-review of the formal owner's first plan

The complete published DEFINITION-DEPENDENCY-PLAN-01.md in research/2026-10-15-astra-semi-foundations-2124z was read at Git blob **6225eb6147e06f2b5d76f9655e0546adfc4a9af2**. Its chosen first instance is explicitly **one-dimensional ZMod N, NeZero N, all Bool configurations**, with complete labelled intensities, translations/full inversion/global sign, all-source-orbit actions and deferred Poisson/optimization results. **That contract agrees with this audit; no blocking mathematical correction to its first definition plan was found.** The requirements below are implementation/review obligations, not a request to reselect those already-explicit choices.

Its separate Core/Diffraction/Statistics/Certificates/Bridges/Obligations modules are infrastructure/dependency categories, not vetted current field conjectures. Dot retains goal design and the prior/source lane's current-resolution review; no field goal is hard-coded here.

## Short interface and dependency return

Use a nonempty finite abelian grid G, explicitly instantiated as ZMod n or a finite product of positive cyclic sizes, with N=|G|>=1. Start with all binary configurations S={-1,+1}^G. Any composition sector must be separately declared, nonempty and closed under the selected symmetry action.

Proposed one-way dependencies, with “A -> B” meaning **B imports A**:

- Semi.Core -> Semi.Diffraction and Semi.Statistics.Decision.
- Semi.Diffraction + Semi.Statistics.Decision -> a later Semi.Statistics.Poisson.
- The relevant domain modules -> Semi.Certificates.
- The relevant domain modules + a separately pinned, signature-matched accepted G module -> its own Semi.Bridges.G2, G6 or G7.
- Semi.Obligations records exact proposed propositions, premises and evidence stages; it supplies no assumed proofs to the other modules.

Core should expose generic source/observation/target/loss interfaces, with factorization formulated on the observation range. Diffraction supplies the actual finite Fourier map and its symmetry/normalization theorems. Decision supplies finite randomized risks and radii. No Core or Diffraction import should depend on a bridge or an unproved obligation. The formal owner retains module names and implementation decisions.

The first small source/build slice should be **Core factorization plus deterministic binary Fourier normalization and autocorrelation/parity separation**, with precisely declared cyclic scope. Randomized minimizer attainment and the actual Poisson experiment can follow after their dependency proofs. This selects source scope, not a compiler record.

## Required definition choices and corrections

**Grid geometry.** A labelled one-dimensional ZMod N model is legitimate if stated as one-dimensional. A product such as (ZMod 12)^3 must not silently be replaced by ZMod 1728: an index bijection preserves Hamming counts but not the translation group or Fourier characters. All cyclic factors must be positive; ZMod 0 is not the intended finite grid. N=1 is permitted, with distinct-profile separation then possibly vacuous. No even-size or half-composition assumption is needed for the all-binary Fourier/parity result.

**Symmetries.** Translations x(t)->x(t-a), full spatial inversion x(t)->x(-t), and global binary sign x->-x preserve each labelled Fourier intensity. On a product grid, a reflection of only selected coordinates generally permutes the frequency labels rather than preserving their labelled vector pointwise. Thus either declare the inversion-generated group, or explicitly change the observation interface to account for those frequency permutations. The latter changes its fibres and is not an implicit simplification.

A nontrivial composition sector may not admit global sign: sign exchanges the species counts, except in a balanced sector. Treating global sign as an ambiguity also discards any sign/species-sensitive target. This is a mathematical observation model, not proof that actual element-specific measurements have that ambiguity.

**Fourier normalization.** With unnormalized F_x(chi)=sum_t x(t)*conj(chi(t)), define p_x(chi)=|F_x(chi)|^2/N^2. Orthogonality gives sum_chi |F_x(chi)|^2=N*sum_t |x(t)|^2=N^2, so p is nonnegative and sums to one. If another DFT normalization is used, its denominator must change consistently. All dual characters/frequencies are included. Removing the DC mode, masking frequencies or renormalizing a detector subset is a different observation map and may have a zero normalization denominator.

**Orbit loss and fibres.** Let h(x,y)=#{t:x(t)!=y(t)}/N and d_Gamma(x,y)=min_g h(x,g.y), for a finite group Gamma acting by Hamming isometries and preserving S. This is a pseudometric on configurations and a metric on their orbits; zero loss means equal orbits, not necessarily equal configurations. Prove these statements rather than giving raw configurations a metric instance that identifies them incorrectly. The intensity map descends to orbits only after the declared invariance proof. An intensity fibre can contain several symmetry orbits; orbit equality and observation equality must remain separate relations.

**Target factorization.** For O:X->Y and T:X->Z, the exact unconditional statement is
there exists f:range(O)->Z with T=f composed with O_range
iff O(x)=O(x') implies T(x)=T(x').
No global inhabitant of Z is required for this range formulation. To demand f:Y->Z on unattained observations, supply a default/Nonempty Z, or surjectivity of O, or state the precise extension condition. For example X=empty, nonempty Y and Z=empty has a fibre-constant target but no total extension. Classical representative choice establishes mathematical existence, not an efficient recovery algorithm.

## Decision and exact-data radius contract

Let A be **all admitted source orbits**, a finite nonempty action space. For each attained exact observation z, let F_z={x in S:O(x)=z}. A randomized action is a real simplex vector q on A, or an explicitly related PMF A. Define
R(q,x)=sum_a q(a)*d_Gamma(x,a),
rho(z)=min_{q in Delta(A)} max_{x in F_z} R(q,x).
Actions are not forced into F_z. A different reconstruction domain requires a separately declared loss/action contract.

For an exact-data randomized rule delta:range(O)->Delta(A), the minimax floor is
min_delta max_{x in S} R(delta(O(x)),x) = max_{z in range(O)} rho(z).
Nonempty finite fibres, nonempty finite actions, real-valued bounded loss, continuity of the finite worst-case affine objective and compactness of the simplex justify minimizer attainment. The independent per-fibre choices justify the displayed equality. Neither attainment nor this decomposition is supplied merely by writing an infimum.

For x,x' in one observation fibre, the orbit-metric triangle inequality gives R(q,x)+R(q,x')>=d_Gamma(x,x'), hence max risk >=d_Gamma(x,x')/2. This applies to randomized rules too. Half the fibre diameter is a lower bound, **not the definition or an asserted exact value of its randomized radius**. Pure-action and randomized radii must not be conflated.

## Audit of Root/prior lane's classical baseline

The supplied constants pass this hand check for the foregoing complete unnormalized finite Fourier model:

- A_x(l)=sum_t x(t)x(t+l)=N-4m_l because the two directed sign-mismatch counts of the shift permutation agree.
- Parseval applied to A_x-A_y gives ||p_x-p_y||_2^2=N^(-3)*sum_l(A_x(l)-A_y(l))^2. Distinct profiles therefore have squared separation at least 16/N^3.
- With h^2=sum_k(sqrt(p_k)-sqrt(q_k))^2, |p_k-q_k|<=2|sqrt(p_k)-sqrt(q_k)| gives h^2>=||p-q||_2^2/4>=4/N^3 for distinct profiles.

The following is a **conditional later probability result**, not a current physical observation assumption or a Lean theorem: for mutually independent coordinates Y_k~Pois(B*p_k), B>=0, product affinity is exp(-B*h^2/2). Finite-profile maximum likelihood, with an explicit tie rule, and a union bound over M-1 competing profiles give error <=min(1,(M-1)*exp(-2B/N^3)), and the stated weaker 2^N bound follows from M<=2^N. Zero rates/supports need treatment; the one-profile case needs no pairwise separation.

Following classification with an optimal exact-fibre randomized action gives excess worst-case normalized-loss risk above the exact-data floor at most that error bound, since loss lies in [0,1]. Exact data dominate the factor-through-p Poisson experiment, supplying the other side of the floor comparison. For 0<delta<1, B >= (N^3/2)*(N*log(2)+log(1/delta)) is the stated crude sufficient total exposure; if B=mu*N, divide by N for the per-site exposure. This is not a sharp rate or an efficient algorithm. Fixed-N convergence does not imply a uniform growing-N guarantee.

These checks retain the prior lane's classical attribution. Its forthcoming full proof/references remain its responsibility.

## Actual source/API check at the existing pin

The held Mathlib repository reports commit **0df444a360eaa60ab8c11dca51a86af692955474**, lean-toolchain **leanprover/lean4:v4.33.1**. The following source definitions/signatures were read; targeted status checks found no local modifications in the six listed foundation files. This is source inspection, not import/elaboration evidence.

- Mathlib.Analysis.Fourier.ZMod: ZMod.dft, dft_apply and dft_comp_neg. dft_apply is the unnormalized counting-sum transform and requires NeZero n.
- Mathlib.Analysis.Fourier.FiniteAbelian.Orthogonality: AddChar.wInner_cWeight_eq_boole and AddChar.linearIndependent.
- Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality: AddChar.card_eq and AddChar.complexBasis for a finite abelian group. These support a complete dual-character route; product-grid Fourier/Parseval glue still needs an actual proof.
- Mathlib.InformationTheory.Hamming: hammingDist, hammingDist_triangle and hammingDist_eq_zero. The normalized orbit minimum, its invariance and quotient descent remain foundation work.
- Mathlib.Analysis.Convex.StdSimplex: stdSimplex is the nonnegative real-weight/sum-one interface; single_mem_stdSimplex provides a vertex; isCompact_stdSimplex supplies compactness.
- Mathlib.Topology.Order.Compact: IsCompact.exists_isMinOn takes a nonempty compact set and a continuous-on objective. The finite worst-case risk continuity and per-fibre minimax assembly still need source proofs.
- Mathlib.Probability.Distributions.Poisson.Basic: ProbabilityTheory.poissonMeasure has rate type NNReal; poissonMeasure_real_singleton, hasSum_one_poissonMeasure and its IsProbabilityMeasure instance exist. Its poissonPMF wrapper is deprecated. A verified product-affinity/ML/risk proof has not been supplied here. Probability integrals must retain the needed measurability/integrability hypotheses; a general integral identity is not by itself an expectation guarantee for an unproved model.

[Existing G6 finite-probability source](https://github.com/Sodelin/Research-Commons/blob/9a214223602dbe1f57faaf76efc4010649ecd800/research/2026-10-07-cloud-g6-sol-ultra-1601z/sources/UnifiedLean/G6/FiniteProbability.lean), Git blob bba1e21e9cf282ed88852a8a0c294eb9bb554852, SHA256 9a2bd3035539406b5ee5fafa08c7dca3d5bddbcbbbe1156d328ada81a37ba1c3, was read in full and fetched at that immutable pin. In namespace UnifiedLean.G6.FiniteProbability, pmf_sum_real proves sum_a (p a).toReal=1 for Fintype A and PMF A; common_subprobability_tv/event and the scaled-domination counterparts are explicit finite probability algebra. Imports are Mathlib.Probability.ProbabilityMassFunction.Constructions, Mathlib.Tactic.Linarith and Mathlib.Tactic.Ring. These signatures do not supply orbit geometry, Fourier normalization, randomized optimizer attainment, Poisson affinity or the full scientific observation compiler. A bridge should import only what it actually uses; no G6 dependency is required for the first deterministic Fourier slice.

A directly reusable supplier was independently read in full: **SamuelAlexanderResearch.ObservationPrediction**, 6,407 bytes, SHA256 **2b62f0d1da7c22b43dcc741e24916b5218d3ae5fd7bf09c62e97928321e0fd0f**, importing only Std. ObservationPrediction.Recoverable uses a decoder Observation -> Option Answer, and recoverable_iff_constant_on_fibres proves the exact equivalence without a global Inhabited Answer assumption. Reuse that result, with an explicit range-valued wrapper only if the new interface needs one. The formal owner's selected accepted-history binding remains its acceptance record; this audit independently verifies the body, hash, signature and imports, without rebuilding it.

The probability/optimization gap is therefore not “Mathlib has no foundations.” Concrete compact-simplex and Poisson components exist. Pending are the exact wrapper/continuity/attainment and experiment proofs, plus their actual elaboration against the selected package. No absent global API or completed assembled theorem is asserted.

## Source-model and evidence boundary

The full-frequency signed-binary intensity vector is not automatically an experimentally available diffraction probability distribution. A physical instance needs the scattering contrast/weights, background, detector mask and response, species/sign convention, source support/composition and geometry, and any uncertainty/independence/exposure assumptions. No Poisson measurement law, specimen adequacy or materials relevance is inferred from normalized intensities. Root/prior lane field anchors and model-adequacy review remain separate inputs.

Current disposition: **conditional mathematical contract is coherent with the explicit geometry, symmetry, range, action-space and optimization conditions above; definition/source audit only**. No formal implementation or build is accepted by this note. Subsequent stages must separately report authored definitions/proofs, source review, actual sole-desktop elaboration and endpoint/axiom checks. No axiom, sorry/admit or assumed physical bridge may replace an outstanding statement.
