# Exact E8 claim and originality audit

Attribution: dot. 2026-10-02. Proof expansion paused for this audit.

## Verdict

**No new mathematical theorem is currently established by this E8 batch.**
Of15 new checked Lean modules,11 formalize or assemble established probability,
sampling and weighted-DP principles;4 discharge narrow obligations about
pinned source-shaped data/functions using standard proof techniques.
Compilation is evidence that those stated formal contracts are checked,
not evidence of mathematical originality or full implementation correctness.

The strongest current contribution is a reproducible source-verification
work product: exact pins, explicit assumptions, compiler/axiom receipts,
and tests of whether known theorems' prerequisites actually hold. The
all-cache-cell premise was falsified on a concrete source instance; the
intended root law was not falsified. A complete all-input source-to-output
verification could be an implementation-verification contribution, but it
is still open and its research originality has not been established.

## Per-module contract map

S = established-principle formalization/assembly. I = source-specific
implementation obligation, with standard mathematics and no novelty claim.
The first two recovered prefix prerequisites are not counted as new modules.

| New module | Kind | Closest existing mathematical contract | What the checked artifact adds locally | Still-open actual-source binding |
|---|---|---|---|---|
| E8ObservablePrefixLaw | S | Measure pushforward / finite fiber sums; mathlib Measure.map_apply and PMF.map_ofFintype | Selector measurability and declared-observable event formula | Actual emitted structure/classifier inverse image |
| E8MidpointGridLaw | S | Classical inverse-CDF counting and nearest-grid rounding | Exact strict-tie midpoint cutoff/count formula | PRNG conditional grid law and rounded comparisons |
| E8MidpointGridTV | S | Finite-CDF discrepancy / total-variation quantization bounds; POPL2020 finite-precision sampling | Specific midpoint-grid (b−1)/(2N) bound | Actual floating arithmetic and local branch list |
| E8FiniteTracebackLaw | S | Weighted traceback cancellation; PRISM§2.1, CParty/Ponty–Saule | Finite-depth products telescope in the declared model | Actual carrier/bijection/weights; global-positive premise is stronger than the implementation needs |
| E8TracebackErrorComposition | S | Standard kernel perturbation/coupling and data processing | Finite trace/event error ≤depth×local error | Actual shared state transitions and total production count |
| E8MidpointProductionKernel | S | Finite normalized kernel construction | Combines declared factor×child partition and exact grid law | Actual runtime production contributions |
| E8GridTracebackBridge | S | Composition of the preceding established laws | A complete conditional finite-model bound | PRNG, numeric, carrier, weight and observable premises |
| E8TracebackCallRanks | I | Standard well-founded ranking and loop arithmetic | Checks named V/VM edges and13 same-span wrapper phases at the PRISM pin | All remaining band calls and total continuation fuel |
| E8SourceVBranchBound | I | Triangle/antidiagonal counting | Source MAXLOOP30 yields≤496 internal slots +2 branches | Exact emitted vector length/guard extraction and executable numeric law |
| E8SupportedTracebackLaw | S | Support-aware composition / zero-mass irrelevance; mathlib PMF.bindOnSupport | Root-positive finite cancellation without demanding positivity of every dead state | Actual supported source graph and continuation semantics |
| E8SCFG2RuntimeChildAdapter | I | Equality/substitution of valid representations | Forward reset and traceback NT-only rewrite use the same valid active key | C++ extraction/alias/defined-memory correspondence |
| E8ScheduledObserverFrame | S | Standard state-frame/refinement invariant; AFP Monad_Memo_DP | Source-shaped ordered scan, skips and callback reference model | Actual C++ read/write frame (audited separately, not a compiler proof) |
| E8ScheduledHypergraphCorrectness | S | Acyclic bottom-up DP correctness / recurrence uniqueness; AFP and weighted hypergraphs | Once-for-all finite reference chart theorem | Actual provider/order/carrier premises; raw all-cache-cell premise is false at the pin |
| E8ScheduledDerivationSum | S | Semiring evaluation of finite derivation trees | Declared ordered interpreter equals its multiplicity-preserving derivation sum | Actual RNA unambiguity/output/physical factors |
| E8SCFG2ProviderBoundaryContract | I | Standard structural/lexicographic child-bound verification | Case-complete57-rule source-shaped transcription proves normalized right bounds and same-right progress from named local guards | C++ generated-list refinement, parser/helper guards and original root-reachable order law |

The universal chart result does not supply a new grammar, a new generic
inside/outside algorithm, or a new biological distribution. A correct
interpreter computes its supplied weights; it cannot correct a source/paper
weight mismatch or establish structure multiplicity by itself.

## Existing Lean library contracts checked directly

At mathlib pin `0df444a360eaa60ab8c11dca51a86af692955474`:

- [PMF Monad](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Probability/ProbabilityMassFunction/Monad.lean):
  bindOnSupport, bindOnSupport_apply, support_bindOnSupport,
  mem_support_bindOnSupport_iff, bindOnSupport_eq_zero_iff,
  bindOnSupport_bindOnSupport and bindOnSupport_comm already provide
  support-aware probabilistic composition. These must be reused, not
  presented as newly discovered machinery.
- [Finite PMF constructions](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Probability/ProbabilityMassFunction/Constructions.lean):
  ofFintype, ofFintype_apply and map_ofFintype already construct normalized
  finite laws and aggregate output fibers. Older E8 custom Real formulas
  are local adapters/ports, not mathematical innovations over these APIs.
- [Measure mapping](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Map.lean):
  map_apply and map_apply_of_aemeasurable support the pushforward contract.
  [Lebesgue basic](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean)
  includes volume_Ico for interval mass.

A bounded text search of the local Probability subtree did not locate an
identical E8-named midpoint/trace-TV statement. That is not an originality
result: the finite-CDF/counting/perturbation argument is standard, and
identical naming or a ready Lean lemma is unnecessary for prior art.

## Verified-engine and sampler comparisons

1. [Ponty–Saule, WABI2011](https://arxiv.org/abs/1106.3771) already separates
   RNA conformation/energy hypergraphs from generic optimization, partition,
   probability, sampling and moment applications under unambiguous
   decomposition. The generic E8 interpretation belongs to that inherited
   architecture.
2. [AFP Monad_Memo_DP](https://isa-afp.org/entries/Monad_Memo_DP.html), with
   [Bottom_Up_Computation](https://isa-afp.org/browser_info/current/AFP/Monad_Memo_DP/Bottom_Up_Computation.html),
   [heap variant](https://isa-afp.org/browser_info/current/AFP/Monad_Memo_DP/Bottom_Up_Computation_Heap.html)
   and [DP_CRelVS](https://isa-afp.org/browser_info/current/AFP/Monad_Memo_DP/DP_CRelVS.html),
   already mechanizes memoized/bottom-up correspondence with cache/domain/
   memory invariants. Its consistentDP_iter_and_compute, memoized,
   consistent_DP_iter_and_compute, cmem, mem_correct and crel_vs contracts
   are closer verified prior than an RNA-only search. Isabelle certificates
   cannot be directly imported as Lean proofs; the small Lean port remains
   a port of that invariant architecture.
3. [SampCert](https://arxiv.org/abs/2412.01671) supplies mechanized Lean
   probabilistic programs and executable discrete samplers, including
   finite uniform primitives. Its trusted FFI/extraction/toolchain and
   entropy-source contracts do not automatically certify existing C++
   PRNGs or Boltzmann floating weights. It is stronger prior for sampler
   infrastructure than declaring uniform randomness as a fresh invention.
4. [Optimal approximate sampling, POPL2020](https://cfreer.org/papers/SFRM-OAS-POPL-2020.pdf)
   already studies rigorous finite-precision statistical distance,
   including floating inversion as a comparison. E8's specific midpoint
   error inequality is not a quantization-design novelty claim.
   [FLDR, AISTATS2020](https://proceedings.mlr.press/v108/saad20a.html)
   supplies exact rational-weight fair-bit sampling; it does not imply
   physical real Boltzmann weights have been represented exactly.
5. [PRISM§2.1](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.30)
   and [CParty](https://pmc.ncbi.nlm.nih.gov/articles/PMC11709253/) provide
   the relevant weighted traceback/decomposition contracts. The full
   source/output relation and factors must instantiate them explicitly.

## Concrete implementation value, without a novelty claim

The published helper-domain and provider-premise checks demonstrate why
conditional correctness matters:

- Fourteen RMQ columns imply a guarded, balanced-scaffold helper bound
  n≤8193 after the Euler-distance argument, not arbitrary accepted-input
  safety. The API does not enforce the necessary scaffold/domain guards.
- Raw span-first provider precedence fails on a balanced canonical21nt
  input. A nonroot cell caches7 under exact unit factors although its
  final-chart recurrence is9. The raw root cone has0future edges on this
  fixture; therefore the intended root law is not thereby refuted.
- Independent actual-weight diagnostics confirm that off-root mismatch
  while preserving the tested productive root result. Root-carrier
  verification is the chosen endpoint; no source reorder is adopted.
- The source VPR padding mismatch was checked against the original CParty
  recurrence and PRISM's own minimum-energy backend. That is source/model
  binding evidence, separate from a new sampling or DP theorem.

Published source checks:
[helper domain](https://github.com/Sodelin/Research-Commons/blob/70e886dafb5459d80dcc716ec706c2c727ecc252/research/2026-10-02-dot-e8-helper-domain-0728z/SCFG2-HELPER-DOMAIN.md),
[provider premise](https://github.com/Sodelin/Research-Commons/blob/76cedc39ef624cb26312d22db4947d46b23b7a4b/research/2026-10-02-dot-e8-provider-premise-0754z/SCFG2-PROVIDER-PREMISE-CHECK.md),
[physical/root boundary](https://github.com/Sodelin/Research-Commons/blob/ccedf5da2c3b16d7b3c452d916f7b410475918b9/research/2026-10-02-dot-e8-validation-root-evidence-0804z/E8-VALIDATION-AND-ROOT-BOUNDARY-CHECKPOINT.md).

A bounded public source-tree check at the current PRISM/PKProbDesign pins
did not locate a Lean/Coq/Isabelle/Agda verification artifact for the
CParty/SCFG2 all-family boundary. That does not exclude unpublished work,
other tools or prior formalizations elsewhere, and establishes no priority.

## Current receipt and endpoint

15th module E8SCFG2ProviderBoundaryContract: PASS,7.228s,
source SHA256 f698aea843351725dcd369f32c526312b0cdb35943cc70b69823fd3e74a15dcb,
object SHA25624f957604b1929e895411085e517346d1be0c1827007de907a35102c1cac0c35.
Two endpoint audits use only propext/Classical.choice/Quot.sound. It is
frozen locally; the earlier14 checked modules are already published.

The full endpoint remains: original execution on all admitted inputs,
root-reachable provider/frame/zero-support correctness, exhaustive and
unambiguous RNA support, exact physical/represented weight relation,
emitted observable binding, and numeric/RNG/compiler refinement. Until
those gates close, the artifact supports bounded formal verification
progress, not an end-to-end claim or a new mathematical theory.
