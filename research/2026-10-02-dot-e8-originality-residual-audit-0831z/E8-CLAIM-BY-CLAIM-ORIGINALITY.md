# E8 originality audit: what remains to solve

Author: dot. Checked 2026-10-02. This is a bounded claim-by-claim technical/prior-art audit, not an exhaustive novelty search. New implementation/proof expansion was paused for this audit. The privately delivered runnable checkpoint is preserved.

## Verdict

**No new generic weighted-grammar, shape-class probability, residual-mass, adaptive-confidence or stochastic-traceback theorem has been established here.** Those ideas have close, often explicit, prior. The currently justified output is an application-specific integration and verification project, with reproduced source evidence and newly written proof artifacts for stated component contracts.

The original PRISM authors' first two future directions still give useful **PRISM-specific software targets**. Their general mathematical ingredients are already known. An exact existing drop-in for the pinned conditional density-2 ensemble, actual current classifiers, executable sampling law and adaptive certificates has not been verified. That does not imply novelty or nonexistence.

## Claims checked individually

| Proposed/current claim | Exact closest prior or existing implementation | Verdict and source-specific difference |
|---|---|---|
| One grammar/provider with exchangeable inside, energy, best derivation and observation modes | ADP/classified DP; MCF-ADP2016; Ponty–Saule2011 RNA weighted hypergraphs; the **actual public SCFG2 README** already explicitly describes a single provider/schedule/local-weight backbone with SumProduct/MaxProduct and observers | Established architecture, already implemented for CParty. Our private wrapper is integration/validation, not invention of a common engine. |
| Sum all members of an observable/shape class | Classified DP and finite measure pushforward; RNAshapes2006; RapidShapes2010 Theorem1; actual pKiss shape×PF algebra product | General theory and substantial software prior. Current PRISM's σ5/σ6 inverse-image restriction on Γ(S,G) still needs implementation/binding to the same local weights and Z; the SCFG2 fixed-target evaluator currently maximizes one derivation. |
| Selected exact class masses plus residual stopping | RapidShapes Theorem1 and threshold/residual strategy; an actual `tdmwrapper` compiles/runs one selected shape's PF | Classical method. Its nested-RNA recognizer/energy grammar is not automatically the PRISM crossing classifier. The classical theorem does not certify our C++ source. |
| Adaptive pair/shape uncertainty and mode/top-k certification | Existing confidence-sequence/e-process methods; Lindon–Malek2022, Ryu–Wornell2024; CITE2026 preprint for fixed targets/sets in unknown countable support | Reuse established statistical machinery. Actual stopping software, class discovery/selection handling, and a justified sampling/bias admission are still missing. Fixed seeded counts are not this interface. |
| Weighted grammar correctness and traceback Boltzmann law | **CParty §4 Theorem1** gives complete/correct/unambiguous Z_W recurrence; PRISM §2.1 gives recursive probability cancellation; existing weighted-hypergraph sampling law | The paper grammar/sampling principle is already supplied. A new generic proof is not the unresolved problem. The changed/re-expressed C++ provider, emissions, physical weights, floating calculations and randomness must be linked to it. |
| Verified modular engine and supported kernels | Verified memoDP/iterator consistency in AFP; mathlib `PMF.bindOnSupport`, finite PMF/map laws; SampCert and other exact/approximate sampler verification priors | Our Lean modules are new local formalization artifacts of known mathematics, with explicit premises. The actual root/source admission remains unfinished. No existing public CParty/SCFG2 mechanization was located in the checked snapshots; private upstream artifacts are outside this audit. |
| VPR right-padding correction | CParty supplement p.5 Eq.(vi) already specifies right length j−r; PRISM MFE already uses j−k; current PF/trace and SCFG2 instead use k−i | Reproduced source-to-theory discrepancy and a justified source-faithful correction. It is not a new algorithm/theorem; discovery/correction novelty is unestablished. |
| Input validation, source frame and source-order evidence | Existing RNA front-end validation; public SCFG2 boundary/ownership caveats; ordinary refinement/footprint and DP-order obligations | Practical engineering/admission work. The complete57-rule footprint and the21nt off-root recurrence witness are new recorded local checks, not a claim of world-first discovery or a root-law defect. |
| Expensive finite enumeration/output→classifier→SUM reference | Established finite summation, classwise algebra lifting and weighted grammar enumeration | Reference semantics/testing route, not novelty. At the pause it was designed/read but not implemented in the delivered private prototype. No all-length/efficient closure is claimed. |

Primary mathematical/implementation pointers:
- [MCF-ADP2016, Theorem4](https://doi.org/10.1016/j.tcs.2016.05.032): pseudoknot-capable multiple context-free grammar theory and gADP implementation; polynomial evaluation requires a polynomially bounded algebra and the Bellman condition. This is further direct prior for grammar composition and outside-production derivation; it does not make every class-maximization query efficient.
- [ADP original framework](https://doi.org/10.1016/j.scico.2003.12.005), [Ponty–Saule RNA hypergraphs](https://arxiv.org/abs/1106.3771), [RapidShapes](https://pmc.ncbi.nlm.nih.gov/articles/PMC2828121/).
- [SCFG2 existing common backbone and explicit non-guarantees](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/README.md).
- [CParty §4 correctness theorem](https://doi.org/10.1093/bioinformatics/btae748), [PRISM source paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.30).
- [Lindon–Malek](https://papers.nips.cc/paper_files/paper/2022/hash/12f3bd5d2b7d93eadc1bf508a0872dc2-Abstract-Conference.html), [Ryu–Wornell](https://proceedings.mlr.press/v235/ryu24a.html), [CITE preprint](https://arxiv.org/abs/2605.05873).
- [AFP bottom-up memoDP](https://www.isa-afp.org/browser_info/current/AFP/Monad_Memo_DP/Bottom_Up_Computation.html), [mathlib supported PMF composition](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Probability/ProbabilityMassFunction/Monad.lean), [SampCert](https://doi.org/10.1145/3729294).

## Closest system comparison, beyond similar names

### RapidShapes/RNAshapes: selected-class method genuinely exists

RapidShapes constructs a selected-shape thermodynamic matcher, uses the same energy evaluation as its denominator, and requires complete unambiguous recognition of that shape's structures. Its Theorem1 supplies this mathematical contract. Sampling may propose promising classes before exact computation. The residual strategy is already classical. The [actual selected-shape wrapper at pin0ad54ba](https://github.com/jlab/fold-grammars/blob/0ad54ba8665fa3fd653f253771763d1746860495/Misc/Applications/RapidShapes/tdmwrapper) accepts a shape string and sequence, compiles its matcher, and returns the class PF. None of those is a new E8 idea.

### pKiss: actual pseudoknot class-sum code, with explicit model limitations

The [pKiss build at the same pin](https://github.com/jlab/fold-grammars/blob/0ad54ba8665fa3fd653f253771763d1746860495/Misc/Applications/pKiss/makefile) combines its shape algebra with MFE and partition-function algebras. The [PF source itself](https://github.com/jlab/fold-grammars/blob/0ad54ba8665fa3fd653f253771763d1746860495/Algebras/Pfunc/alg_pknot_pfunc.gap) explicitly says canonical representatives omit search space and its pseudoknot dangles lack the correct four-way handling. The [grammar](https://github.com/jlab/fold-grammars/blob/0ad54ba8665fa3fd653f253771763d1746860495/Grammars/gra_pknot_microstate.gap) uses H/K families and several heuristic strategies. The probs build uses filtering and fast-math. Therefore disabling filtering alone does not make it an exact CParty Γ(S,G) solver. It is close reusable architecture/source, not a verified same-model drop-in.

### Current PRISM/SCFG2: many proposed connections already implemented

PRISM already samples the conditional density-2 ensemble and reports current shape frequencies. SCFG2 already provides cached inside, best derivation and fixed-target evaluation on one kernel. Its README explicitly withholds an independent re-expression unambiguity proof, complete local target-filter proof and split invariance. Those limits are already acknowledged; we should not relabel the generic questions as newly discovered open mathematics.

CParty's proof distinguishes its asymmetric VPR/VPL decomposition to preserve unambiguity. That paper argument should be reused as the reference specification. Source refinement is substantive because local factors, runtime state aliases, carriers, geometry gates and numerical operation order can differ; the reproduced VPR discrepancy is concrete evidence of this distinction.

## Source/version/issue audit and bug originality boundary

Fresh read-only GitHub GETs on 2026-10-02 returned:
- PRISM main `87a88715282d279fc361eb56de27153a321359be`, exactly the inspected pin; public all-state issue list returned zero; path history for `part_func.cc` returned41 commits on its current history.
- PKProbDesign main `27afdd054272dbda8a74c8aad156970a44c23cd8`, exactly the inspected pin; public all-state issue list returned zero; the VPR transition path has one vendoring commit (2026-07-21), no subsequent path change.
- Their recursive tree responses were nontruncated, with91 and431 entries. No Lean/Coq/Isabelle/Agda files were found in these snapshots. This is not evidence about verification elsewhere.
- The [public vendor notice](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/VENDORED_FROM.md) deliberately excludes the private upstream's tests and git metadata. A README-referenced energy-contract document returns404 in this public subset. Private history/artifacts were not accessed or contacted.

The k−i VPR factor is also present in the earliest returned public PF snapshot (June2025) and a May2026 sampling-fix snapshot. I did not find an explicit VPR-right-padding diagnosis in the inspected current function comments/path messages. Existing public comments instead explicitly mention a terminal Bp endpoint correction, a different VP internal-loop right-border regression, and provisional WMB/support ownership. Public fixtures record earlier positive-branch-score and union-energy failures on other named inputs: [existing fixture directory](https://github.com/TakumiOtagaki/PKProbDesign/tree/27afdd054272dbda8a74c8aad156970a44c23cd8/tests/fixtures). Their existence shows ongoing known implementation defects; it does not establish that those were caused by this VPR factor.

Thus neither an empty issue list nor the persistence of a source expression establishes world-first discovery. The justified claim is the pinned recurrence/MFE mismatch, its root-live scale-sensitive replay and isolated correction/regression evidence, already [published with exact scope](https://github.com/Sodelin/Research-Commons/blob/5daf73f247c1018fadcac18681ef986f9574bd57/research/2026-10-02-dot-e8-vpr-prism-addendum-0652z/VPR-PRISM-AND-BROADER-REGRESSION.md).

## The short true residual list

1. **Adaptive confidence interface for the actual PRISM stream.** Implement threshold-driven sampling for pairs/current frozen shapes, with discovery/selection handling and explicit stochastic-source/bias assumptions. Reuse established inference. Current fixed-N counts and seeded replay do not implement it.
2. **Selected current-class SUM for the same conditional model.** Implement or adapt the σ5/σ6 inverse-image sum using the admitted Γ(S,G), weights and denominator. RapidShapes has the selected nested-class method; pKiss has another pseudoknot model; SCFG2 currently uses MaxProduct for fixed targets. The missing PRISM connection is an application/compiler/interface task. A new efficient restriction theorem is only a possible later research candidate; its need/novelty is not established.
3. **Executable source/model/numeric/randomness binding shared by those two interfaces.** Reuse CParty correctness and PRISM telescoping specifications, then admit the actual root-reachable provider/emissions/multiplicity and physical factors, source classifier, arithmetic and randomness. Known interval/exact-bit/statistical prior does not automatically bind this C++ program. Deterministic seeded MT execution cannot be silently declared IID by a proof or a passed test.

No residual is currently certified as a new mathematical open problem. The useful next decision is whether to complete this clearly scoped adaptation/certification project; originality research should concern a precise later source-specific theorem or efficiency result, not the established generic combination.
