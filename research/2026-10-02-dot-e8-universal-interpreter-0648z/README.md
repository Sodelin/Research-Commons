# E8 once-for-all scheduled weighted-hypergraph interpreter

Attribution: dot (OpenAI), research assistance for Nolan.
Checkpoint: 2026-10-02 06:48 UTC.

## Main checked theorem

For every finite schedule size, finite provider list, ordered runtime-normalized child list and exact semiring weight assignment, the reference callback-bearing scheduled interpreter computes the sum of complete derivation choices in the finite acyclic expansion, provided:

1. Every child is indexed strictly earlier than its parent in the proposed schedule.
2. Candidate-observer callbacks preserve the semantic provider/allowed/local-weight view.

The theorem is parametric over those inputs and value assignments. It is not a collection of separately checked RNA parameters or finite caps. Its final endpoint is `E8ScheduledDerivationSum.observed_scheduled_derivation_sum`.

**The actual all-input SCFG2 factory/schedule/frame admission, RNA model/weight fidelity and C++/numeric refinement are not yet proved.** This is a once-for-all reference-interpreter result with explicit operational prerequisites. It must not be advertised as universal end-to-end SCFG2 or PRISM correctness.

## What is proved

Three sources passed the pinned Lean compiler, with 14 selected endpoint axiom audits using only standard axioms:

- `E8ScheduledObserverFrame`: the actual source-inspired allowed/zero-local skips, ordered child multiplication, callback and parent chart update are modeled explicitly. When callbacks leave the semantic view unchanged, the callback-bearing loop matches its pure ordered reference for every finite schedule. No associativity assumption is used in this frame result.
- `E8ScheduledHypergraphCorrectness`: strictly earlier normalized child indices imply stabilization of the recurrence expansion; the full finite expansion satisfies every cell equation and is its unique solution. The ordered zero-default chart update schedule computes that solution. This also composes with the observer-frame result.
- `E8ScheduledDerivationSum`: deduction occurrences and multiplicities are retained in lists. Cartesian products combine every completed child-derivation choice. In an exact semiring their weighted sum equals the finite expansion. The final theorem connects the callback-bearing reference loop directly to that sum.

Allowed, nonzero-local deduction occurrences are enumerated; zero-local skips preserve the semiring sum. Distinct occurrences with identical weights are not silently deduplicated. The earlier-child condition makes the finite n-layer expansion sufficient for the acyclic recurrence. Derivation multiplicity is not assumed to equal RNA structure multiplicity.

## Actual source contract

The selected runtime is the public PKProbDesign-vendored CParty SCFG2 at commit `27afdd054272dbda8a74c8aad156970a44c23cd8`.

The source reference is [run_w_final_exact_dp_schedule](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/replay/w_final_exact_inside.hh), Git blob `f4b6ab09e1d16f20f7d9851b6bb3c83fdaf9ec05`. It uses the exact deduction factory, allowed/zero-local skips, ordered runtime child lookups, a candidate callback and a final parent chart write. Proving only the smaller generic `engine/execute.hh` loop would omit its runtime alias and callback/storage behavior.

The [previous concrete normalization adapter](https://github.com/Sodelin/Research-Commons/tree/2c79f134ec3dab03a1851567aa01373d2de7e386/research/2026-10-02-dot-e8-scfg2-child-adapter-0601z) supplies the valid-active-child key/lookup/order correspondence. In particular, the WMBP direct rule uses the runtime-normalized VP child, not its raw exported VP_DIRECT tag.

The universal proof takes ordered normalized children as input. Its all-input source instantiation still needs to show that the real factory and proposed schedule provide those inputs and satisfy predecessor/coverage/frame conditions. These premises describe operational dependencies and callback effects, rather than assuming the intended RNA probability as a field.

## Whole-engine source admission, not per-example accumulation

The public exact schedule contains all 17 families in this order per increasing primary span:

VM, V, WMv, VP_CLOSED, VP, VP_DIRECT, BE, VPL, VPR, WMBP, WMBW, WMB, WMp, WM, WIP, WI, W.

A span-plus-family order explains ordinary splits and wrappers. The remaining source-wide work must identify every generated normalized child, including band/scaffold helpers, with an earlier scheduled slot or an explicitly modeled zero-default terminal. Mere child-key validity does not establish parent containment, all required fixed-anchor cells, or predecessor coverage.

The observer frame is also an actual source theorem still to prove: materialized storage/owner callbacks must preserve the provider, allowed predicate and local factors used by the semantic pass, or a richer explicit state semantics must replace that frame contract. It cannot be inferred from an “observation-only” comment alone.

The organizing target is one all-input generator/schedule/frame instantiation over valid sequence/scaffold/parameter contexts, not another parameter-by-parameter test ladder.

## Reused prior machinery

- [Ponty–Saule weighted acyclic independent hypergraph framework, WABI 2011](https://arxiv.org/abs/1106.3771): established unification of RNA optimization, partition functions, probabilities, sampling and moments under complete/unambiguous decomposition assumptions. This package formalizes the declared interpreter contract; it does not claim a new dynamic-programming principle.
- [AFP Monad_Memo_DP](https://isa-afp.org/entries/Monad_Memo_DP.html), including [Bottom_Up_Computation](https://isa-afp.org/browser_info/current/AFP/Monad_Memo_DP/Bottom_Up_Computation.html), [heap variant](https://isa-afp.org/browser_info/current/AFP/Monad_Memo_DP/Bottom_Up_Computation_Heap.html) and [DP_CRelVS](https://isa-afp.org/browser_info/current/AFP/Monad_Memo_DP/DP_CRelVS.html): verified cached-value/memory-frame and bottom-up iterator correctness contracts. Their invariant architecture is reused; Isabelle theorems are not presented as directly imported Lean proofs.
- [Pinned mathlib PMF support-only monad](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Probability/ProbabilityMassFunction/Monad.lean): existing support-aware probabilistic composition to reuse next. This package does not reprove PMF.bindOnSupport or claim that an executable RNG satisfies its source law.

Inside chart correctness in an exact semiring does not imply an efficient outside algorithm for arbitrary semirings or an efficient arbitrary-class inverse-image sum. Classifier compositionality, output-language intersections and complexity need their own applicable contracts.

## Important separation from physical weight fidelity

A correct interpreter computes the weight assignment it is supplied. It cannot make a wrong represented factor faithful to the intended RNA energy model.

Independent source-to-paper work found that the public PRISM PF/traceback and SCFG2 VPR factor used left-gap padding for a right-gap rule, whereas CParty's published recurrence and PRISM's own minimum-energy backend use right-gap padding. An isolated copied-source intervention restored scale invariance on the reported bounded fixtures. That evidence is recorded separately in the [primary/source causal checkpoint](https://github.com/Sodelin/Research-Commons/blob/787408f8b241a5abd9a752504951d65065f6d0fe/research/2026-10-02-dot-e8-vpr-source-evidence-0639z/SCFG2-VPR-EVIDENCE-CHECKPOINT.md) and [PRISM/broader regression addendum](https://github.com/Sodelin/Research-Commons/blob/5daf73f247c1018fadcac18681ef986f9574bd57/research/2026-10-02-dot-e8-vpr-prism-addendum-0652z/VPR-PRISM-AND-BROADER-REGRESSION.md). No test result is used as a universal weight-fidelity premise here.

The local same-anchor BE gauge obstruction also remains a distinct support/ownership question: the checked fixtures had no root-live same-anchor stack witness. It is not asserted to explain the observed root bias.

## Remaining end-to-end obligations

1. Prove the actual all-input normalized provider/schedule/zero-default and observer-frame interface.
2. Establish complete/unambiguous emitted RNA structure/scaffold support, with explicit derivation multiplicity.
3. Prove paper/source physical energy and homogeneous scaling agreement for all admitted contexts; corrected VPR alignment is one required source fact, not the entire theorem.
4. Refine the reference loop to C++/memory/IEEE arithmetic or provide a separately certified numeric interpretation/error bound.
5. Instantiate supported-state sampling with a justified conditional RNG/fair-bit law and existing applicable exact/approximate sampler contracts.
6. Connect the frozen L5/L6 observable, selected-class SUM calculation and established all-time confidence machinery with certified numerics.

No biological validation or full executable probability guarantee follows from this package.

## Exact receipts and replay

`SOURCE-AND-COMPILE-MANIFEST.json` contains complete successful source/log/object pins and direct import-object dependency hashes. All three source/receipt/log triples are copied from immutable successful attempts. True project dependencies are included: observer frame → scheduled chart correctness → weighted derivation sum.

- Observer frame: 1.449 s, source `c21c170e78bdd186bf30f1dbe8a561a225a7210fc3a76fa16e41c319e9faa728`
- Scheduled chart: 1.621 s, source `0c6dd3c3eb49ac4647707ab6e2b7a48350d113f26a0946ad5ba3486ef5546487`
- Derivation sum: 1.611 s, source `c694b0e648b053b4e4b16083c8b2dd2af789731669575158502af7cb65ea4bcf`

Compiler: Lean 4.33.1 commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Compile the three modules in the dependency order above with their objects and the pinned mathlib/dependency objects in `LEAN_PATH`, using `lean -j1 -M3072`. The harmless unused-section-variable warnings are retained in exact logs. No private product code is included.
