# Indicator scope and identifiability register

17 October 2026, 02:06 UTC. Prepared by dot (OpenAI), working with Nolan.

**Status:** draft research-scope checkpoint for review. The elementary statements below are proved here as classical set-theoretic facts. Their application obligations are not new physical theorems. Previously accepted nanowire and biological results retain their exact source and verification status. No historical novelty or Lean verification is claimed.

## 1. The question being tracked

Can the information collected from an admitted physical model determine every indicator of interest? Which indicators can be certified, which remain ambiguous, and what additional measurements would help?

“Every finite number of channels” and “every indicator” quantify over different things. The accepted all-channel theorem handles one particular target, the real determinant Q of a zero-energy reflection matrix, for every finite electron-channel count N. It does not recover every property of the underlying device.

There is no useful finite list of literally all mathematical indicators: each subset of a source class defines a binary indicator. A research register therefore needs a declared family of scientific targets. Each entry must specify:

1. The admitted source class, including physical parameters and calibration uncertainty.
2. The target and its precise meaning. A numerical reflection determinant, a periodic invariant and a protected phase are different targets.
3. The actual observation: one conductance, a bias sweep, a magnetic-field sweep, several contacts, or a statistical law.
4. The noise and model-error allowances, including which nuisance parameters are shared across settings.
5. The identification or certification statement, its quantifiers, evidence and remaining obligations.

The same device and one shared parameter tuple must generate the entire observation record. Fitting each setting independently changes the inverse problem.

## 2. Exact target identification: the classical criterion

Let X be the admitted source set, O : X → Y its exact observation map, and T : X → Z a target. Use the attained observation space O(X), so no arbitrary answer is needed at impossible observations.

**Proposition 1.** There exists a function F : O(X) → Z satisfying T = F ∘ O if and only if

    O(x) = O(x′)  implies  T(x) = T(x′), for every x,x′ in X.

**Proof.** If F exists, equal observations have equal F-values. Conversely, at an attained observation y, assign F(y) the target value of any source x with O(x)=y. The displayed condition makes that value unique, independent of the representative. This defines F on O(X), including the vacuous empty-source case. ∎

An observation fibre is the set of sources giving the same observation. Thus the target is identified exactly when it is constant on every observation fibre. This is an existence statement about a decoder; it does not establish its computability, continuity, robustness, efficiency or laboratory implementation.

If O(x) denotes a probability law, the proposition concerns access to that exact law. It does not turn one finite random sample into the law.

**Proposition 2.** Every unrestricted binary target b : X → {0,1} is exactly recoverable from O if and only if O is injective.

**Proof.** Injectivity makes every observation fibre a singleton, so Proposition 1 applies to every target. If O(x)=O(x′) with x≠x′, the indicator of the singleton {x} distinguishes them and cannot factor through O. ∎

The word “unrestricted” matters: measurable, continuous, symmetry-invariant or experimentally relevant indicator families can be smaller. For a specified family 𝒯, all its targets are recoverable precisely when every observation collision is also a collision for every T in 𝒯.

### Physical equivalence and irrelevant labels

Suppose x∼x′ means physical equivalence for the intended science, and permit every binary indicator that is constant on equivalence classes. Every such indicator is recoverable exactly when

    O(x)=O(x′) implies x∼x′.

Necessity follows by the indicator of one equivalence class; sufficiency follows from Proposition 1. If observations themselves are invariant under ∼, O descends to X/∼ and this is exactly injectivity of that descended observation map. Without observation invariance, do not call it injectivity of a quotient map that has not been defined.

This prevents demands to recover a basis choice or an arbitrary internal name. It also prevents quietly declaring scientifically distinct devices equivalent merely because the present measurements cannot distinguish them.

## 3. Noisy observations: the sharp feasible answer set

Allow a general declared report relation R ⊆ X × Y. A report y is permitted from source x exactly when R(x,y). This can encode bounded deterministic error, several calibrated settings, temperature uncertainty and shared nuisance parameters without imposing an unjustified independent-error model.

Define

    X_R(y) = {x in X : R(x,y)},
    A_T(y) = {T(x) : x in X_R(y)}.

**Proposition 3.** A single target answer is valid for every source compatible with y exactly when A_T(y) is a nonempty singleton. More generally, a reported set C contains the true target for every compatible source exactly when A_T(y) ⊆ C.

**Proof.** Each member of A_T(y) has an admitted witnessing source that can produce y. Excluding it would fail at that source. Conversely, including every member includes the target of any compatible true source. ∎

Consequently A_T(y) is the smallest honest feasible answer set under this deterministic contract. An empty set means the report is inconsistent with the declared source/error assumptions, rather than certifying an arbitrary answer. Several possible values require a set-valued answer or abstention.

For numerical targets, interval hulls can be convenient summaries, but gaps in A_T(y) may matter. Infima and suprema need not be attained without additional compactness and continuity assumptions. This definition gives no general algorithm for computing A_T(y) for every X,O,T.

For the usual normed-vector observation model R(x,y) iff ‖y−O(x)‖≤ε, two source balls overlap exactly when ‖O(x)−O(x′)‖≤2ε: the triangle inequality proves necessity and their midpoint proves sufficiency. This midpoint statement assumes the midpoint is an allowed report; arbitrary metric/report spaces need their actual overlap relation. Opposite targets with overlapping balls prevent a uniformly correct single-valued answer at the shared report.

Noiseless identification and stable identification are different. Two target classes may have disjoint observation images but zero distance between them. Then exact observations can identify the label while every positive uniform error tolerance admits ambiguity. Computing effective separation is a further obligation.

## 4. Current nanowire indicator register

### A. Reflection determinant and its sign: established algebraic scope

For any finite N≥1, let the zero-energy reflection matrix be a contraction with canonical particle-hole symmetry,

    r = [[A,B],[conj(B),conj(A)]],
    g = N − ‖A‖F² + ‖B‖F²,   Q = det(r).

Here g is local conductance in units of e²/h, with spin included in N and the stated current convention. The accepted hand theorem and independent review give the exact attainable region:

    0≤g≤2N, |Q|≤1, Q≥1−g,
    (−1)^N Q≥g−(2N−1).

Equivalently, the exact feasible Q-set at a known g is

- Even N: [max(−1,1−g,g−2N+1), 1].
- Odd N: [max(−1,1−g), min(1,2N−1−g)].

Every point in these intervals is attained in the declared algebraic reflection class. Thus this already is a complete target-image answer for this one observation/target pair. For N=1, Q=1−g. For N≥2, g=2 admits both Q=−1 and Q=+1, so this single conductance does not identify even the sign throughout the full class. That algebraic ambiguity is not automatically a pair of original Rashba-wire realizations.

A calibrated upper bound g≤u<1 certifies Q≥1−u>0 for every finite N, even when N is unknown. Stronger promise-based decisions require independent justification of their source promise, such as |Q|≥m. Positive or negative finite-device Q is not itself a proof of protected Majorana modes, a robust gap or a thermodynamic phase.

Source: [accepted all-channel theorem and review](https://github.com/Sodelin/Research-Commons/blob/f79a9a7626de25a58ee33d4a3dbff00f9f3f3db1/research/2026-10-16-nanowire-fixed-lead-nonseparation/all-channel/README.md). Its prior assessment credits the unitary special case and Gaussian parity identities; historical novelty is unestablished.

### B. Finite-temperature conductance to the same Q: conditional measurement adapter

The reviewed thermal adapter derives an upper bound on the required zero-energy conductance from a thermal average only with specified regularity or local regularity plus nonnegative local-conductance tails. Measurement error and a separate warm-to-cold model discrepancy must be included. A temperature-dependent superconducting gap can change the underlying frozen-model curve, in addition to thermal averaging.

Once those hypotheses supply f(0)≤U, the existing theorem gives Q≥1−U. It does not infer all missing regularity or calibration constants from a good fitted curve. The adapter also proves an effective-scattering narrow-resonance obstruction: at fixed positive temperature, whole thermal curves can be arbitrarily close while zero-energy Q values are opposite. This is a stability obstruction in the stated effective class, not exact equality of the curves or a new fixed-wire microscopic realization.

Source: [thermal adapter, independent hand review and scope](https://github.com/Sodelin/Research-Commons/blob/e8c71a1ddfb5aafae97eb1de06ba4d02be928e92/research/2026-10-16-nanowire-fixed-lead-nonseparation/finite-temperature/README.md).

### C. Spectral energies, gaps and spatial information: target-specific work remains

A conductance value is not a complete energy spectrum. A bias sweep can reveal resonances under an admitted transport/contact model, but recovery of energies, widths, local spectral weight or a gap needs its own target and calibration theorem. The existing same-device energy-curve nonseparation result concerns inference in the other direction: energy curves can be close while reflection labels stay separated. It is not a theorem that every spectral quantity is unidentifiable from every conductance experiment.

Status: no general all-indicator recovery claim. Existing pair-specific conductance separation remains a useful benchmark, not class-wide recovery of the Hamiltonian or wavefunctions.

Sources: [finite-pair conductance benchmark and prior comparison](https://github.com/Sodelin/Research-Commons/blob/f174251a09468254c778a1136ed5b975173fc378/research/2026-10-16-nanowire-fixed-lead-nonseparation/conductance-example/README.md); [bounded-class identification obligations](https://github.com/Sodelin/Research-Commons/blob/3775abf04f2efe0d7861666286ffd02f548bc40b/research/2026-10-16-nanowire-fixed-lead-nonseparation/bounded-class/README.md).

### D. Protected phases, periodic invariants and usable Majorana devices: different targets

These require their own definitions. A periodic-disorder invariant of an infinite repeated supercell is not the finite open-device reflection determinant. Protection, spatial separation, robustness and device operation require additional physical conditions and observables. They cannot be inserted as synonyms for Q or imported from classification accuracy in a simulated training set.

Status: unproved transfers in this register. Before proposing a general theorem, specify the source class in which the target is defined, the observation family and the required robustness/error criterion. This register does not purport to enumerate every possible invariant.

Sources: [version-specific 2026 source comparison](https://github.com/Sodelin/Research-Commons/blob/0aff15fdf3c7db3a11bda84a458d59c2a2765c1f/research/2026-10-16-nanowire-fixed-lead-nonseparation/LITERATURE-COMPARISON-20261017-0154.md), including [MEDA v2](https://arxiv.org/html/2607.26208v2) and [Taylor–Pan–Das Sarma v2](https://arxiv.org/html/2512.13825v2).

## 5. Using the accepted biological programme responsibly

Nolan requested using G1, G2, G5, G6 and G7 to organize general features. Their useful roles are below. The biological theorems retain their original source classes; the right-hand obligations must be proved anew for a physical application.

### G1: preserve the information when reducing the source

- Established original role: exact source-derived contextual replacement and a sharp reduced structural-core bound, retaining declared source provenance and joint readouts. Internal decorations can remain unbounded.
- General-feature obligation: for a proposed reduction R:X→Xred, prove both O=Ored∘R and T=Tred∘R, or their explicitly quantified error versions. Preserve all relevant exterior contexts, correlations and shared parameters.
- Missing physics supplier: an admitted physical reduction and its observation/target error. A biological core-count bound is not a bound on nanowire length or hidden modes.
- [Exact original G1 contract](https://github.com/Sodelin/Research-Commons/blob/0e3d36f4035d61a8ad6ae4dc5000b8cf9e54dc2d/research/2026-10-04-dot-complete-original-g1-1549z/THEOREM.md).

### G2: keep every panel or setting consistent with one process

- Established original role: actual-source restriction/projectivity of the declared laws. The separate universal operator criterion connects generator/control intertwining to all finite transition programmes.
- General-feature obligation: establish that changing panels, readouts or allowed controls is implemented by one source-consistent observation diagram. If a generator criterion is used, prove its hypotheses for the actual physical evolution and readouts, including boundary conditions.
- Missing physics supplier: such intertwining or a controlled approximate version. Independently fitting conductance rows does not establish it.
- [Registered timed endpoint](https://github.com/Sodelin/Research-Commons/blob/68691262f082c0ab94d1893a94367dc3c62d4f00/research/2026-10-07-dot-g2-timed-endpoint-ordinary-integration-0941z/G2ActualTimedAllPanelLaw.lean); [classical universal operator criterion](https://github.com/Sodelin/Research-Commons/blob/e85b58325b4541343630296ceb003029ed7205a5/research/2026-10-05-dot-g2-universal-transition-criterion-1950z/package/src/G2UniversalTransitionCriterion.lean).

### G5: identify a named feature without recovering the entire source

- Established original role: exact three-tip calendar laws identify displayed cluster/split unions in the stated positive temporal cut-child source class. Its bounded hidden supports, Cartesian support and chronology are substantive source-specific suppliers.
- General-feature obligation: prove that the chosen physical target is constant on the relevant observation fibres. If borrowing a local-to-global proof pattern, establish its actual support, factorization and finite-witness hypotheses.
- Missing physics supplier: a physical feature-identification theorem. Three biological labels do not translate to three contacts or three nanowire measurements.
- [Exact G5 target and source assumptions](https://github.com/Sodelin/Research-Commons/blob/6ae0c54a20aa4571264f8e3136404da625f5174f/research/2026-10-01-sol61-head-audit-1956z/G5-TRIPLE-CALENDAR-FULL-TARGET.md).

### G6: turn source-image information into honest noisy certification

- Established original role: effective finite-profile approximations of target-labelled observation-law closures; an anytime-honest finite-target procedure; and a matching finite-read stopping boundary for the declared source, computational and sampling model.
- Its robust fibre includes alternatives approachable at every allowed finite profile. This is stronger and different from the exact equality fibre in Proposition 1. Different rival sources may witness different finite profiles.
- General-feature obligation: supply effective approximations of the actual target-labelled physical images, a justified observation/noise model, simultaneous confidence control, and the target separation needed for the claimed stopping guarantee.
- A desired property of the accepted finite biological target is handled by an effectively supplied finite answer map. Arbitrary discontinuous physical targets, infinite target alphabets, unknown calibration, correlated unmodelled noise or unavailable measurements are not automatically covered.
- The exact feasible-set logic in Section 3 is not a replacement for these source/effectivity/statistical proofs. Conversely, G6's mathematical characterization is already stronger than a bare slogan that “equal data imply equal answers.”
- [Accepted G6 proof](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-01-g6-effective-certification/PROOF.md); [independent source-critical acceptance, Sections 5–6](https://github.com/Sodelin/Research-Commons/blob/6ae0c54a20aa4571264f8e3136404da625f5174f/research/2026-10-01-sol61-g6-independent-review-2005z/REVIEW.md).

### G7: select legal measurements for the chosen feature

- Established original role: complete-registry, exact-response experimental-design characterization with shared-source constraints, semialgebraic response/legality and deletion-closed resource rules.
- General-feature obligation: define the available physical action registry, reset/sequence rules, costs, observation statistics and target. Prove the response representation and any finite policy bound used by the design algorithm.
- Missing physics supplier: an admitted measurement-design model. A response redundant in noiseless affine algebra may still be useful as a noisy repeat; irreversible or prerequisite actions cannot simply be deleted.
- [Accepted exact G7 design scope and limitations](https://github.com/Sodelin/Research-Commons/blob/6ae0c54a20aa4571264f8e3136404da625f5174f/research/2026-10-01-sol61-head-audit-1956z/G7-EXACT-MASTER-REVIEW.md).

These are five explicit adapter obligations, not a proved common physical theory. General G3 source recognition and General G4 finite forcing retain their separate unresolved master obligations. The indicator register does not close or reopen them.

## 6. Concrete next use and evidence boundary

For each proposed new physical indicator, first write one row containing X,T,O,R and the actual source of each premise. Seek either a same-observation different-target pair, a certified opposite-target noise overlap, or a source-faithful separation theorem. Only after that should an implementation claim to return a unique answer, an interval, a confidence set or a recommended new measurement.

This checkpoint records the user's broader indicator question without promising a universal list, solver or recovery theorem. It reuses accepted results and classical logic. It does not provide an all-indicator Lean proof, a new physical model or historical priority evidence.

## Proposed short addition to the readable report

**Which indicators can the measurements determine?**

- Our theorem covers every finite channel count for one target: the zero-energy reflection determinant. It does not recover every device property.
- A target can be identified only if every admitted device producing the same data has the same target value. With noise, retain every target value compatible with the full error and calibration budget.
- The current conductance theorem gives the exact possible determinant interval in its algebraic class. Finite-temperature use needs additional justified measurement and model-error bounds. Protected phases, energy spectra and periodic invariants need separate identification results.
- The earlier biological programme supplies a useful checklist: preserve the target during reduction; keep all settings consistent with one source; prove feature identification; certify it under noise; and choose legal informative measurements. Each physical application must establish these conditions. The biological theorems do not transfer automatically.

Link this paragraph to the reviewed successor of this register after publication. No document edit is included in this draft.
