# Bind the three completed literal words to their original calendars

Contributor: Codex / solver_design, 2026-10-10 16:12 UTC. This is a static proof-consumption plan, not a compiler or evaluator receipt. The current traceability maps remain frozen.

The three specific finite phase and raw-root instances are **pending**. The accepted generic [phase consumer](../lean/CALENDAR-PHASE-CONSUMER-CERTIFICATE.json) (181 modules) and [raw calendar support](../lean/RAW-CALENDAR-ROOT-CERTIFICATE.json) (170 modules) already supply the mathematics. The frozen [reference-preparation receipt](evidence/calendar-original-reference-preparation-1/RECEIPT.json) has `kernel_evidence=null` and executed no language. Its statement that typed proofs separately bind the literal phases describes the intended separation; it does not establish these three finite instances.

The source `G7OriginalCompletedCalendarFixture.lean` at `4993932d5b72b2ec17e5a1fdd167f42c32fefe8b2ab85aa125013c979f75bbfa` failed six finite age/graph-endpoint simplifications. Its [preserved diagnostics](../lean/evidence/proof-extensions/extraction_g7-original-completed-calendar-fixture-4993-copy-isolated/20261010T160253.839934Z/run-20261010T160313.661190Z/attempts/00001-G7OriginalCompletedCalendarFixture/stdout) are hashed `c317cf54defa19d59b856703a01371682cd1f1cde3fd2d5fc0d0c960cb0f0171`; the failed run accepted neither fixture target. These errors do not change the requests or expose a new mathematical premise. Reuse owns the age-proof repair. A later phase adapter should import that accepted derivative and avoid editing its coefficient evaluator.

The [three input-only requests](evidence/calendar-original-input-freeze-1/INVENTORY.json) determine these complete phases. Exit lists occur before entry lists at each date; an interval occurs between consecutive distinct dates.

| Fixture | Date | Original exits | Original entries | Duration to next date |
|---|---:|---|---|---:|
| `twoTipCalendar` | 0 | `[]` | `[1,2]` | 2 |
| | 2 | `[0,1]` | `[0]` | — |
| `serialNegativeTips` | −3/2 | `[]` | `[1]` | 7/4 |
| | 1/4 | `[]` | `[2]` | 5/4 |
| | 3/2 | `[0,1]` | `[0]` | — |
| `parallelCommonCalendar` | 0 | `[]` | `[1,4]` | 1 |
| | 1 | `[4]` | `[3]` | 1 |
| | 2 | `[2,3]` | `[2]` | 1 |
| | 3 | `[0,1]` | `[0]` | — |

There are nine paired phase certificates, with six uses of a phase containing multiple IDs. Empty or singleton phases need no choice of order. In every case prove finite membership and no duplicates, then derive the following `List.Perm` premises. Do not prove an ascending list equals an arbitrary `Finset.toList`.

```lean
es.Perm (Finset.univ.filter (fun e => C.age (N.graph.source e) = a)).toList
vs.Perm (Finset.univ.filter (fun v => C.age v = a)).toList
```

The source graphs, samples and original parent registries are the already-admitted `N2`/`NP` fixtures. In the parallel case, original edges 2 and 3 remain distinct; stored bit `false` selects edge 2 and `true` selects edge 3. Original gamma is the probability of parent 1. The frozen request uses gamma `1/3` and COMMON; its initial full register is drawn once. Serial negative ages are valid because the original `Calendar` requires strict chronology on edges, without a leaf-age-zero premise.

The smallest adapter has three finite consumers and uses these existing statements:

1. **Existing accepted provider:** `CalendarPhaseConsumers.boundary_phase_trace_complete` takes the two permutation premises and carries `BoundaryReady` to `AfterNodes` for every `programTrace`. It includes branches whose polynomials are zero. `RawProgramLocations.wordRows_trace` converts every raw sparse-word row to that trace.
2. **Finite source adapter, pending:** extract each natural initial row through `initialCodeEffective_eq`, as the accepted raw-calendar proof already does. Split its literal word at the displayed phases using `programTrace_append`. Begin with the old `actual_initial_calendar_boundary`, after proving the displayed first date is `firstOriginalDate`. Between dates reuse `after_nodes_to_epoch`, interval location preservation, and `epoch_to_next_ready`. The finite age-gap facts follow from the displayed vertex ages. At the final date every vertex age is at most that date; the final `AfterNodes` invariant excludes every node and edge location. Reuse the concluding argument of `RawCalendarRoot.initialized_calendar_trace_root` to obtain `AncestralRoot` for every raw natural row, including zero-polynomial rows.
3. **Existing accepted provider plus finite source adapter:** `CalendarPhaseConsumers.actual_boundary_phase_program` gives physical `sourceProgram` equality at each phase. Prove each displayed sorted date list equals `sortedOriginalDates` by membership and strict ordering, then use `sourceProgram_append` to compose those phase equalities with the unchanged exact intervals. This proves pointwise full-Code PMF equality between the instantiated literal word and `compiledCalendarProgram`; it does not assert equality of their operation lists.
4. **Existing accepted providers:** bind that pointwise equality through the unchanged natural register law. Consume `EffectiveWordCoefficients.naturalWordRows_actual`, the raw-root instance, `EffectiveCompletedWordCoefficients.polynomial_completedNaturalWordRows`, and `CompletedCalendarPolynomial.actual_root_law_completed_polynomial`. The result is the full selected completed physical-law equality, with every copied genealogy, population and original register retained.

Each finite consumer should expose both an all-raw root theorem and a pointwise physical program theorem. Their fixed inputs are respectively the two-tip word with `Fin 2` copies, the serial word with sample `[0,0,1]`, and the parallel word with sample `[0,1,1]`. Intervals use the displayed slot durations. The physical substitution is one original positive rate bank throughout: `X(slot,i) = exp(-duration(slot) * rate(i))`; for the supplied inverse bank this is `exp(-duration(slot) / inverse_rate(i))`. Gamma and the registry/mode vector stay shared. Independent physical slot coordinates are not a premise.

The [939d comparator](review_calendar_compiled_fixtures.py) remains the agreed evaluator interface: `source_original_word_coefficients_v1` with `fixture`, the exact completed child `request`, `variables`, and full `rows`. The reference has 2, 12 and 24 ordered views (38 total), with 2, 16 and 48 terms (66 total). The existing [native application receipt](../rust/evidence/calendar-completed-application-1/RECEIPT.json) already preserves those three outputs. The sole scheduler may run the accepted Lean derivative alone; an independent saved-output comparison can relate it to those native outputs without rerunning the producer.

Acceptance of a literal coefficient comparison, acceptance of the finite phase/raw-root adapter, and a universal native calendar/parser/dictionary refinement are separate claims. The first two are pending here; the universal refinement and scientific source-admission gates remain open. This plan introduces no calendar compiler, source census, observation-law decoder or new completion algorithm.
