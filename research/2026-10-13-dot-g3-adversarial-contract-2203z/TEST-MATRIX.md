# Adversarial matrix

Baseline: [Commons 1e9910a6](https://github.com/Sodelin/Research-Commons/tree/1e9910a6a068c9e607d5b6949956a25e53602f2e).
`Inherited` means a concrete test was found in the inspected source, not rerun here. `New unit` means implemented in the accompanying unexecuted script. `Owner integration` means the stated correspondence must still be exercised with actual providers; no mock acceptance is permitted.

## Parsing and exact arithmetic

| ID | Input or mutation | Expected result and justification | Coverage |
|---|---|---|---|
| P01 | Duplicate JSON key; binary float; NaN; malformed UTF-8 | REFUSED_REQUEST; there is no unambiguous exact request. | Inherited compatibility test; new unit |
| P02 | PMF masses sum to 1/2 or exceed 1; negative mass | REFUSED_REQUEST, no implicit renormalization. | Inherited; new unit |
| P03 | Missing mask entry or duplicate ID within a namespace | REFUSED_REQUEST, since original identity/whole mask is incomplete. | Inherited; new unit |
| P04 | Identical text used as taxon, edge, hybrid and configuration IDs | Legal typed namespaces; certificate/menu processing continues, source answer UNKNOWN. | Inherited; new unit |
| P05 | Nonempty protected-parameter constraint list | Current API REFUSED_REQUEST as unsupported exact language, never discard constraints and never NO. | Inherited; new unit |
| P06 | Nine taxa or level above eight | Current bounded schema refusal, not a mathematical exclusion of larger admissible sources. | New unit |
| C01 | `(1,1/2,1/8)` with generated cubic `x^3-3x/4+1/4` | GENERATED_AND_CHECKED, no source YES. Weighted-square identity is exact. | Inherited; new unit |
| C02 | Change one coefficient without changing its square identity | REFUSED_REQUEST. | Inherited; new unit |
| C03 | Level one, moment 1, nonzero constant polynomial | REFUSED_REQUEST: nonzero constant cannot annihilate a normalized bank. | New unit |
| C04 | `P=x`, levels 1,2, coefficients `(0,1)`, moments `(1,0)` | CHECKED_RATIONAL_CERTIFICATE, with no source existence inference. Any positive bank has E[X]>0, so a compatible actual source is impossible once the legal-row binding is supplied. Current path does not return a source-bound NO. | New unit; future source-bound exclusion test |
| C05 | `P=1-x`, moments `(1,1)` | Arithmetic accepted; supported values must be exactly 1. Endpoint 1 may not be removed from the domain. This does not establish a whole-source witness. | New unit |
| C06 | Singleton acquisition on `(1,1/2,1/16)` | Current generator UNKNOWN. The data violate E[X^3] >= E[X]^3; that mathematical observation is not an implemented source-bound NO receipt. | New unit |
| C07 | Valid certificate encoded by exact fraction aliases | Same rational mathematics, potentially different original/canonical request bytes. Do not merge their authentication identities. | Inherited compatibility; new unit |
| C08 | L=3 cubic on an actual singleton bank | Generic support consequence is at most 2. At most 1 needs the separately proved cubic root characterization; never overstate the generic wrapper's conclusion. | New unit checks reported bound |

## One tuple and source decisions

| ID | Input or mutation | Expected result and justification | Coverage |
|---|---|---|---|
| S01 | Existing `finite-witness.json` and `bounded-witness.json` | CERTIFIED_SOURCE_WITNESS only after actual producer and semantic checker; verify one assignment against every row. | Inherited unified cases |
| S02 | Existing `shared-row-exclusion.json` | Scoped complete-registry exclusion. Each incompatible topology row is not a separately selectable source. | Inherited unified case |
| S03 | New singleton rows `(2/3,1/6,1/6)` and `(3/4,1/8,1/8)` on the same preferred triplet | Each singleton request has a strict ordinary witness with internal survival 1/2 or 3/8 respectively. | New JSON fixtures; owner integration |
| S04 | Join the S03 rows without changing allocation/control | CERTIFIED_EXCLUSION_WITHIN_VERIFIED_COVERED_CLASS for the declared complete zero-hybrid registry. One probability vector cannot equal two different vectors. This isolates shared parameters without changing topology. | New JSON fixture; owner integration |
| S05 | Across levels use one source/parameter tuple for k=2 and another for k=3 | A combined witness must be rejected unless one tuple really satisfies both; no concatenation of rowwise witnesses. In a future legal-row evaluator, use m2=1/2,m3=1/16 as a bank-impossible trap. | Missing actual legal-row integration control |
| S06 | Actual table bound to source A, certificate request bound to source B or changed mask PMF | Reject the claimed correspondence; no carried-over source YES. If no completed decision remains, UNKNOWN. | Owner integration; exact identity must cover source, allocation, mechanism, masks, readout and parameters |
| S07 | Existing strict-positivity exclusion with all triplets 1/3 in complete zero-hybrid registry | Scoped NO only. A zero-length limiting edge is not a strict positive witness. | Inherited unified case |

## Joint masks, support and original identities

| ID | Input or mutation | Expected result and justification | Coverage |
|---|---|---|---|
| J01 | Joint masks 00/11 versus 01/10, each weighted 1/2 | Different joint-law identities despite equal site marginals. | Inherited hash control; new unit forwards exact tables |
| J02 | Source-level J01 control: two serial proper private cells, arm survivals 1/2 and 1/4 at each, fixed ordinary multiplier A=1/2 | Correlated E[X]=5/64; anticorrelated E[X]=1/16. A product-of-marginals replacement gives neither original joint law in general. This is a proposed exact physical readout control; instantiate one admitted source before claiming execution. | Missing actual-source/native test; arithmetic oracle only |
| J03 | Replace natural mask `null` by forced zero | Different request/control meaning, even when a particular symmetric example happens to have equal outputs. Never infer global equivalence from that coincidence. | Inherited compatibility hash control; new unit |
| J04 | Add/reorder zero-weight configurations | Preserve original records; derived supported-mask distribution may omit zero mass without renormalization. Changing the raw request changes its identity. | Inherited; new unit |
| J05 | Assign positive weights 1/2,1/2 to repeated survival 1/2; zero weight to an arbitrary out-of-domain value | Abstract support adapter counts one value. No domain/root premise is needed for the zero-weight atom. Actual source values are all in (0,1] regardless. | Missing literal Lean adapter fixture; no new theorem assumed |
| J06 | Replace zero configuration mass by 2^-100 | It becomes positive support exactly; no floating tolerance or underflow may erase it. | New unit checks configuration support; actual support fixture remains |
| I01 | Parent-zero probability 1/4, arm survivals 1/2 and 1/4 | Correct COMMON mixture is 5/16, with snapshot Gamma=3/4. An uncomplemented swapped convention yields 7/16. Preserve original incoming occurrence order. | Existing conversion body inspected; missing end-to-end asymmetric assertion |
| I02 | Two parallel original edges with identical endpoints | Preserve two occurrences and distinct coordinates. Endpoint deduplication is an invalid source binding. | Existing native parallel examples; missing occurrence-map mutation test |
| I03 | Permute incoming parents | A transported equivalence must explicitly swap occurrence mapping, forced bits and complement inheritance coordinates together. Changing only parent order must fail identity/refinement checking. | Owner integration |
| I04 | Taxon text `selected:A1` | Baseline label `baseline:selected:A1` differs from selected copy `selected:A1`; n+k+1 distinct copies remain. | Inherited; new unit |

## Legal rows, finite-bank coverage and premature NO

| ID | Input or mutation | Expected result and justification | Coverage |
|---|---|---|---|
| R01 | Four taxa, k=1 padded row | Six distinct copies; selected normalized scalar is 1. Full six-copy table is not thereby trivial. COMMON6 cannot alone certify nontrivial support. | New unit |
| R02 | Four taxa, levels 1,2,3, singleton survival 1/2 | Required copy counts 6,7,8. Coefficients 1,1/3,1/18; event probabilities 1,1/6,1/144 for those moments. | New unit; actual source/forward/Lean correspondence missing |
| R03 | Change B-first labelled comb to a different labelled attachment order | Different event. Child swaps alone are quotient-equivalent; changing which A copy first joins B is not. Bind exact pruning/event, not just shape or number of leaves. | New unit checks literal encoding; owner native quotient test missing |
| R04 | Drop baseline copies to fit four-copy native profile | Invalid substitution for the declared query. An independently proved projectivity optimization would need explicit source/channel correspondence; none is supplied by this compatibility report. | Inherited allocation checks; owner mutation test |
| R05 | Input n=8 and L=8 | Last padded row has 17 copies; COMMON6/7/8 is only an incremental profile, not menu completion. | New unit |
| R06 | Replace rooted full table by unrooted split table, or fitted calendar by another calendar without exposure proof | Do not certify the rooted pruned comb probability or same-tuple correspondence. Retiming needs an explicit exposure-preserving map with shared parameters; identical raw edge-survival numbers alone are not a full calendar proof. | Owner integration |
| N01 | Existing complete-registry exclusion changed to incomplete registry/bounded search | UNKNOWN on exhaustion, with no unrestricted NO claim. A finite search limit is not a completeness proof. | Inherited bounded-exhaustion case; new paired fixture specification |
| N02 | Conditional COMMON support/hybrid number fed directly into search as a completeness bound | Do not certify global NO. Missing physical representative/admission transfer remains an explicit gate. | Existing `budget_applied_to_search=false`; new unit |
| N03 | Supplied list of finitely many banks or candidates, all tested and rejected | UNKNOWN unless exact coverage of every admitted realizer is separately proved for this input. Candidate-table completeness is not original-source completeness. | Owner result-policy control |
| N04 | Time/state/term/disk guard, SMT UNKNOWN, missing native/backend dependency | UNKNOWN, not YES or NO. Missing/changed authenticated native source makes compatibility report incomplete. | Several inherited cases; expanded budget-before-allocation tests pending |
| N05 | Alter request bytes but reuse a native SAT/UNSAT/TABLE certificate | Request-bound checker rejects; a prior certificate is not portable to new parameters, readout or profile. | Existing native checker contract; add mutation to owner corpus |
| N06 | AFFINE UNSAT or successful formal LAW table | Retain matrix-only exclusion or table-only scope; no source decision without authenticated reduction/admission. | Inherited native integration cases |

## What must accompany any owner execution

Authenticate the tested source versions first; retain exact requests, outputs, exit codes, source/binary pins, guard receipts and the original semantic check. Report pure parser/arithmetic tests separately from backend, native, legal-source and Lean checks. A failed anticipated result must remain a failed test, not be replaced with a mocked expected status. Any newly selected source version requires a new identity record.

## Primary repository providers

- [Unified test cases](https://github.com/Sodelin/Research-Commons/blob/1e9910a6a068c9e607d5b6949956a25e53602f2e/research/2026-10-13-astra-unified-solver-0645z/test_solver.py)
- [Compatibility tests](https://github.com/Sodelin/Research-Commons/blob/1e9910a6a068c9e607d5b6949956a25e53602f2e/research/2026-10-13-astra-native-common-compatibility-2106z/test_compatibility.py)
- [Exact certificate/menu implementation](https://github.com/Sodelin/Research-Commons/blob/1e9910a6a068c9e607d5b6949956a25e53602f2e/research/2026-10-13-astra-unified-solver-0645z/certificates.py)
- [Fixed external row encoding](https://github.com/Sodelin/Research-Commons/blob/1e9910a6a068c9e607d5b6949956a25e53602f2e/research/2026-10-13-astra-unified-solver-0645z/external_encoding.py)
- [Source-search decision gates](https://github.com/Sodelin/Research-Commons/blob/1e9910a6a068c9e607d5b6949956a25e53602f2e/applications/practical-solver/certified_bounds.py)
- [Actual legal-row Lean candidate](https://github.com/Sodelin/Research-Commons/blob/fb0c09628c33798e332ef3ff35992fa8ad2c5b04/research/2026-10-13-astra-legal-row-support-2115z/lean/Astra/ActualLegalRowSupport.lean)
- [Positive-support Lean candidate](https://github.com/Sodelin/Research-Commons/blob/fb0c09628c33798e332ef3ff35992fa8ad2c5b04/research/2026-10-13-astra-positive-support-adapter-0830z/lean/Astra/PositiveSupportAdapter.lean)

These are scoped software/proof-provider contracts. This packet does not claim a new mathematical closure, universal native correctness or historical novelty.
