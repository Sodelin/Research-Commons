# Semi foundations: first definition and dependency plan 01

15 October 2026. Lean foundation/source owner. This implements the newly selected foundation task; Dot retains programme/source design. Stage: source/API inspection and plan only. No new Lean file in this slice has been elaborated or audited.

The prior obstruction [review](https://github.com/Sodelin/Research-Commons/blob/c0ff76ab38c894704d1647867595c05cef46759a/research/2026-10-15-astra-materials-kernel-adapter-2035z/obstruction-review-r1/INDEPENDENT-HAND-REVIEW-AND-CHECKPOINT-01.md), uncompiled conditional adapter and [completed original custody](https://github.com/Sodelin/Research-Commons/blob/d7d106cc8c9e044d303366fe50ecb2c1a3814704/research/2026-10-15-astra-materials-kernel-adapter-2035z/obstruction-review-r1/ORIGINAL-ARTIFACT-CUSTODY-CLOSURE-02.md) remain unchanged, including the one-attempt versus block-power/schedule distinction.

## One-way layout and first scope

- Semi.Core: finite observation/fibre and bounded-loss interfaces; generic finite risk. It imports no diffraction, bridge, certificate or obligation module.
- Semi.Diffraction: cyclic configurations -> declared symmetries/orbit-Hamming -> labelled Fourier intensities/observation fibres. Imports Core and pinned Mathlib only.
- Semi.Statistics: finite randomized decision rules and fibre minimax proofs, importing Core and actual probability/optimization APIs. A diffraction-specific consumer can additionally import Diffraction; the generic layer does not.
- Semi.Certificates: selected Core/Diffraction/Statistics consumers with exact evidence, no reverse imports.
- Semi.Bridges.G2/G6/G7: isolated optional consumers of the matched accepted supplier plus required Semi modules. No bridge is imported upward into Core or used as an unproved scientific instance.
- Semi.Obligations: statement/status/dependency ledger, not a source of axioms imported by proofs.

First concrete Fourier slice is the cyclic grid ZMod N with [NeZero N], hence N>=1, and binary configurations ZMod N -> Bool, encoded as real/complex +/-1. Do not flatten a product lattice and claim its physical Fourier map is the cyclic DFT. A later rectangular-grid instance must bind its own finite-product character map.

The declared trivial symmetries are translations, FULL spatial inversion and global spin-sign flip. Partial-axis reflections of a product grid are not silently quotiented: they generally permute frequency labels. No sorting or forgetting of the labelled intensity vector is selected.

Normalize Hamming distance by N and minimize over the declared finite symmetry orbit. Prove the orbit loss is well defined, lies in [0,1], and has the needed symmetry/triangle properties before using it as a decision-theoretic loss. Randomized actions range over ALL source orbits, including orbits outside the observed fibre.

The Fourier target is EXACTLY p_x(k)=||DFT(x)(k)||^2/N^2. Nonnegativity and sum=1 must be proved, not assumed or replaced by a different denominator. The root/prior hand baseline is classical and uncompiled here.

## Exact reuse actually inspected

Pinned environment: Lean 4.33.1; Mathlib commit 0df444a360eaa60ab8c11dca51a86af692955474. These are source selections, not a new compiler lease or cache-availability claim.

| Source/API | Exact pin and applicability |
| --- | --- |
| SamuelAlexanderResearch.ObservationPrediction | Accepted connected1613 source SHA256 2b62f0d1da7c22b43dcc741e24916b5218d3ae5fd7bf09c62e97928321e0fd0f, 6407B, imports Std. ObservationPrediction.recoverable_iff_constant_on_fibres gives an Option-valued decoder on the whole observation type with no Inhabited Answer premise. A decoder on Set.range observe needs no default answer; a total Answer-valued decoder on arbitrary observations needs a nonempty answer or a suitable range/surjectivity condition. Reuse this exact theorem, not a new attribution. |
| UnifiedLean.G6.FiniteProbability | Accepted selected source SHA256 9a2bd3035539406b5ee5fafa08c7dca3d5bddbcbbbe1156d328ada81a37ba1c3; imports PMF.Constructions, Linarith, Ring. Its pmf_sum_real normalizes finite real-weight risks; it supplies no materials observation law. |
| UnifiedLean.G6.FiniteCorruptionBoundary.shared_corruption_iff | Selected source SHA256 6b5964de36b9cc4f2e79d4d7e8652498b8f2517e98769c1b9aa6938bf197754a, 4697B, imports MeanEnclosure. Signature is overlap of two closed PMF TV balls iff pmfTV p q <= 2*beta. This is not Fourier recovery or Poisson convergence and is not needed in the first slice. Its historical source header is not a new downgrade of later accepted reuse. |
| Mathlib.Analysis.Fourier.ZMod | At the pinned Mathlib commit, Git blob 101a428d82866a93cba10e85c589fe38864a212e. ZMod.dft is a complex LinearEquiv; dft_apply, dft_comp_neg, dft_dft were read. Direct Parseval/N^-2 normalization wrapper still needs an actual finite-sum proof; it is not an existing theorem inferred from a name. |
| Mathlib.Analysis.Fourier.FiniteAbelian.* | Orthogonality blob 619b123068af91959127d951a3074884064b0a16; PontryaginDuality blob 3918dfeacbc483dc9304f9dc26e147e5568ee427. AddChar.complexBasis and sum_apply_eq_ite supply an eventual product-grid route, not a currently connected physical instance. |
| Mathlib.InformationTheory.Hamming | Git blob 800095468b359fb295427c716ac68c5465f06073. hammingDist_triangle and hammingDist_le_card_fintype are actual inspected signatures. Orbit minimization/invariance still needs proof. |
| PMF.Basic / PMF.Constructions | Git blobs dabd43d78b8d44551004fc65e5cf40fa1baf05ca and f84582dd28948439cbd15acc38dc07c1878cf3a9. PMF.hasSum_coe_one, ofFintype, pure/map are available. Finite simplex weights may be used with a proved PMF correspondence. |
| Mathlib.Analysis.Convex.StdSimplex | Git blob 23e19ff83b604511a372caea8b08f8e73bb01870. stdSimplex, isCompact_stdSimplex, stdSimplex.sum_eq_one and nonempty vertex constructors were read. This supports the finite randomized-action simplex; it is not itself a minimax theorem. |

The accepted-source module names/imports/hashes were checked in connected1613's current/connected dependency graph and acceptance record. No imported object was recompiled. The separate G6 hand/instance obligation audit at 9a214223602dbe1f57faaf76efc4010649ecd800 remains a source-qualified audit, not a compiled module.

## Small source/build slice and remaining proof/API work

First source slice: Core.Observation wrapper/reuse; Diffraction.CyclicGrid, Symmetry, OrbitHamming and FourierIntensity; a narrow audit file printing actual definitions and theorem dependencies. Preserve these as separate modules from the beginning. The first reviewed desktop build request will select only its exact admitted closure, not the whole research repository.

Then add generic finite-risk pairwise indistinguishability bounds. A half pairwise/fibre diameter is a LOWER BOUND, never the definition of the minimax radius. The exact-data randomized radius minimizes worst fibre risk over the probability simplex on ALL source orbits.

Concrete unresolved work: construct the finite orbit set/action and quotient loss; prove finite Parseval and symmetry invariance; identify and use the exact compact-minimum/continuous-finite-maximum APIs to prove randomized minimizer attainment and a simultaneous selector over realizable fibres. Compactness is available; no missing-library claim is made. If attainment is not yet proved, definitions and lower bounds stay separate and no optimal rule is assumed.

The actual independent Poisson channel, affinity/ML bound, fixed-N convergence and polynomial sufficient budget come AFTER this foundation and require their own proved probability/optimization statements. None is introduced as an axiom, sorry/admit placeholder or presumed theorem. Source-model adequacy requires the existing independent audit; definitions certify no experimental adequacy.

Next action: author this bounded modular source slice, return exact source pins and actual proof gaps for independent review, then use only the existing desktop operator/bridge and a separately selected finite record for elaboration and axiom checks. No cloud compiler, installation, cache acquisition, parallel compiler or consumed-record replay.
