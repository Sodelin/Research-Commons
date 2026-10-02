# E8 paper/prior bindings and actual admission goals

Owner: prior-art/duplication auditor, coordinated by dot. 2026-10-02.
Canonical Lean module: `UnifiedLean.Source.E8PaperObservableBridge`.
This register changes no runtime feature or paper model.

## What the module contributes

- Constructs a normalized finite weight table with existing `PMF.normalize`.
- Reuses `PMF.map_ofFintype` for finite class tables; it does not rediscover that theorem.
- Derives selected-class mass via `PMF.map_apply` and finite tsum conversion. This main statement accepts arbitrary class types, including String; it does not impose a globally finite shape universe.
- Reuses `Equiv.sum_comp` to transport the normalizer and exact class fibers under an admitted source-to-paper equivalence, pointwise weight preservation and classifier commutation.
- Names the positive-support continuation interface using existing `PMF.bindOnSupport`'s supported-domain type. It supplies no new sampler execution proof or fallback kernel on a dead state.

The fields of `SourceContract` are explicit obligations, not constructors automatically supplied for actual C++. The selected probability equality is a derived theorem, not a record field. Both finite carrier instances and root normalizer nonzero/finite conditions remain explicit. Zero-weight outcomes remain allowed.

## Prior attribution and reuse

1. CParty section4 Theorem1 already supplies completeness/correctness/unambiguity of its paper recurrence. Its next paragraph explains asymmetric VPR/VPL decomposition. [Primary paper](https://doi.org/10.1093/bioinformatics/btae748).
2. PRISM section2.1 already supplies recursive stochastic traceback cancellation; section5 asks for adaptive confidence thresholds and more direct selected class masses. [Primary paper](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.30).
3. RapidShapes Theorem1 already computes a selected shape's mass with a complete unambiguous same-energy recognizer. [Primary paper](https://pmc.ncbi.nlm.nih.gov/articles/PMC2828121/).
4. Mathlib finite probability constructors/mapping/support laws and finite-equivalence sums are library results, not new E8 mathematics. [Pinned probability source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Probability/ProbabilityMassFunction/Constructions.lean).
5. Existing E8 finite/supported traceback and observable-prefix modules already formalize cancellation/fiber sums. This module contributes the PMF/source-paper contract binding, rather than another cancellation theorem.

## Actual goals deliberately not discharged by this module

| Gate | Existing evidence | Required actual link |
|---|---|---|
| Finite source derivation carrier/root order | Abstract universal interpreter checked; actual57-rule source-frame footprint; positive off-root future-child witness with unchanged root | Bind the original runtime's root-reachable carrier and child-domain/order to the imported theorem. A full raw-provider/all-cache-cell instantiation is false on the checked witness. |
| `interpret` equivalence | CParty paper grammar completeness/unambiguity | Construct the equivalence for the actual re-expressed provider/emitted RNA outputs, preserving the admitted same S,G,parameters/options. A field containing an equivalence is not its construction. |
| `weight_preserved` | Paper factors; reproduced VPR PF/trace-versus-paper/MFE mismatch and isolated source-faithful correction | Bind every live production's actual local factor/ownership/scaling and numeric representation to the intended paper weight. Correcting one factor does not settle all factors. |
| `classifier_commutes` | Frozen current PRISM L5/L6 source and bounded standalone classifier checks | Bind actual emitted structures/current classifier to the paper observable, including lane/output ownership and abstraction semantics. No recognizer or class-SUM runtime is built by this record. |
| Program PMF equals `law` | Conditional sampler/interface theorems | Admit actual categorical operations, arithmetic and random input contract. Seeded deterministic replay and integrity tests do not establish IID Boltzmann draws. |
| Original authors' adaptive interface | Established confidence-sequence prior | Implement/admit the stopping/selection procedure; the frozen private prototype reports fixed-N counts only. |
| Original selected class-SUM interface | RapidShapes/classified-DP prior; SCFG2 currently uses MaxProduct for fixed targets | Build/bind actual σ5/σ6 inverse-image SUM with the same Γ(S,G), weights and normalizer. A best derivation is not the aggregate class mass. |

These are application/source verification and interface tasks. No new generic mathematical open problem or novelty of a compiled theorem is asserted.

## Linked evidence

- [Exact9-claim originality and residual audit](https://github.com/Sodelin/Research-Commons/blob/5ec6b65a77eb833ed695741c1d98f36c1c66fa24/research/2026-10-02-dot-e8-originality-residual-audit-0831z/E8-CLAIM-BY-CLAIM-ORIGINALITY.md).
- [Actual validation/private runnable and root-boundary checkpoint](https://github.com/Sodelin/Research-Commons/blob/ccedf5da2c3b16d7b3c452d916f7b410475918b9/research/2026-10-02-dot-e8-validation-root-evidence-0804z/E8-VALIDATION-AND-ROOT-BOUNDARY-CHECKPOINT.md).
- [Complete57-rule observer-frame hand/source audit](https://github.com/Sodelin/Research-Commons/blob/e53153047185981b57f8d31e3d02272bc0a02a5c/research/2026-10-02-dot-e8-observer-frame-0722z/SCFG2-COMPLETE-OBSERVER-FRAME-AUDIT.md).
- [Once-for-all interpreter theorem packet](https://github.com/Sodelin/Research-Commons/blob/b54050446c8a6dda68eb57803a1afd0ba42ca095/research/2026-10-02-dot-e8-universal-interpreter-0648z/README.md).

The canonical compiler receipt records the exact current source hash, imports, object hash and axiom output. Failed elaboration attempts are preserved and are not accepted proof artifacts. No private product code is part of this module/register.
