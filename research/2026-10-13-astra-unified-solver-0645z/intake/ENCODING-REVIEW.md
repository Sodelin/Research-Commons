# Static review of the external comb encoding and emitted certificate theorem

Reviewer: Astra research-intake agent, separate from the implementation lane.
Evidence tier: **agent static source review**. This is not human review, an
independent compiler run, a native refinement proof, or acceptance of the
missing physical-representative theorem. The exact inspected files and selected
providers are pinned in `ENCODING-REVIEW-PINS.json`; the first inspected version
is preserved by `ENCODING-REVIEW-PINS-INITIAL.json`.

**Scoped result: pass after two interface clarifications.** The external
allocation/event construction matches the selected 1613 padded-comb definitions
under the explicit label correspondence below. The emitted theorem proves a
conditional support consequence for any finite bank matching the supplied
moments. It does not assume an unknown physical target, assume its desired root
conclusion, or claim that such a bank or source exists. The source-law binding,
physical reduction, exact admission and parameter-feasibility obligations remain.

## External labels, directed pair and legal event

The selected bodies were read directly, not inferred from module names:

| Implementation item | Exact selected declaration and source correspondence |
|---|---|
| A copies at taxon `i`, B copy at taxon `j` | `DotG4.ActualBankFirstMeeting.repeatedSample`, line 97, sends `Fin k` to `i` and `Unit` to `j`. The Python assignment is in this direction; it does not swap the directed survival. |
| `selected:A1`, ..., `selected:Ak` | `canonicalA` in `G4ActualNaturalCombMoments`, line 68, lists `Fin k` in order; `paddedA` in `G4ActualLegalPanelComb`, line 477, applies the outer left injection. Map `selected:A(q+1)` to `Sum.inl (Sum.inl q)`. |
| `selected:B` | `paddedB` in `G4ActualLegalPanelComb`, line 476, is the image of `Sum.inr ()` under the outer left injection. |
| `baseline:<taxon>` | `paddedSample`, line 467, has carrier `((Fin k ⊕ Unit) ⊕ X)` and sends the right summand by identity. The baseline labels therefore give one copy for every original taxon, independent of candidate source. |
| Allocation size | Exactly `k+1+n` labels. The `baseline:` and `selected:` prefixes are disjoint, including when an external taxon contains either string. The input validator enforces distinct finite taxon IDs. |
| Passive keep set | `paddedKeep`, line 470, keeps precisely the outer left summand. Python keeps B and the A copies and removes the baseline copies. |
| One ordered labelled comb | `DotG34.SpecifiedCombEvent.comb`, line 25, is a left fold of grafts starting at B. Python forms `(B,A1)`, then grafts A2, ..., Ak in that order. It does not replace this single specified event by the larger “no A-only clade” event. |
| Unranked event | The selected law evaluates the singleton forest `{toUnranked (comb ...)}` after `pruneForest`. Python encodes one comb in `forest=[comb]` and explicitly erases child orientation. This describes the intended quotient; no implementation of Lean quotient equality is inferred. |
| Level and exponent | `momentLevels` in `G4ActualSparseCertificateExistence`, line 184, is `{1,...,L}`. `finiteBankMoment`, line 2775 of `G4WholeProfileDetermination`, uses exponent `k.choose 2`. Python starts at 1 and the emitted theorem uses `k*(k-1)/2`. |
| Normalization | `combCoefficient`, line 1871, is exactly `2^k / ((k+1)! k!)`. `randomizedLegalCombMoment`, line 3502, divides the actual event probability by this positive coefficient. The emitted external requirement multiplies the supplied normalized moment by the same exact rational coefficient. |
| Joint configuration | `actual_randomized_legal_moment`, line 3529, uses one `configurationBankPMF` and the full original bank. Python retains the literal whole configuration table, including correlations and zero-mass rows; it does not multiply marginal control probabilities. |
| Forced and natural bits | `OriginalMask` is `Hybrid N → Option Bool`; `overrideBank` uses `getD (coin h)`. `OriginalHybridParents.parent` selects parent0 for false and parent1 for true. The final schema explicitly fixes null/natural, bit0/false and bit1/true and gives unprotected controls null. |

The initial encoder called the derived value `observed_event_probability`
although no source event row had been checked. It also left the bit convention
implicit. The author changed the field to `required_event_probability`, added
the explicit derived-requirement role, and fixed the mask semantics. These are
interface clarifications, not new source-law theorems. The flags
`actual_source_binding_checked=False` and
`parser_Lean_refinement_proved=False` remain necessary and correct.

This executable schema deliberately supports one fixed joint configuration
table across its pair/level queries and no additional protected-coordinate
constraint. It is a restricted admitted input language. The general reviewed
theorem permits more fixed external rows and predicates, with additional exact
encoding/feasibility obligations. `parameter_constraints=[]` is enforced;
an unencoded tie is rejected rather than silently removed. The budget counts
the supplied primitive protected edge and hybrid IDs. It is not applied as a
complete source-search bound. No source-dependent mask table, latent readout,
or unprovided observation is generated.

## Generated Lean statement and quantifiers

For one concrete checked certificate, `emit_lean.py` creates rational literal
coefficients and moments and proves:

1. the polynomial is nonnegative on `[0,1]`, by its literal weighted-square
   identity and the separately stated square kernel;
2. it has a concrete nonzero value, verified by exact arithmetic;
3. the supplied coefficient/moment dot product is exactly zero;
4. **for every** finite type A, weight/value functions satisfying nonnegative
   weights, values in `(0,1]`, and all the supplied exact moment equalities,
   **every** atom of strictly positive weight has polynomial value zero.

The first moment has exponent zero and supplied value 1, so the moment hypotheses
already imply total weight 1. An empty bank cannot satisfy that hypothesis;
the theorem does not introduce a witness of inhabitation. Values at zero are
excluded explicitly by `hv`, and value 1 remains admitted. Zero-weight atoms are
not assigned roots by the conclusion. No renormalization or independently drawn
configuration coordinates are inserted.

The generated finite-bank proof derives the zero weighted polynomial sum by
distributing the supplied moment equalities and exact annihilation. It then
calls `supported_atom_is_root`, whose assumptions are nonnegative summands,
zero total, and positive weight for the selected atom. The desired root equality
is its conclusion, not a premise. The standalone kernel's joint-configuration
theorem uses the complete configuration carrier and one original-bank factor;
it does not assert independence between coordinates *within* the configuration.

No existential physical graph, fixed unknown target, actual demographic
admission, native computation truth, representative, or bound on all original
presentations appears in these generated theorems. The exporter is therefore
not a substitute for `G3CertifiedCommonBoundedWitness` or its missing exact
physical provider. The nonzero witness search is bounded to degree+1 integer
points; the emitted proof checks the chosen literal value rather than trusting
the producer's search. All rational input is parsed before it reaches Lean
source syntax. No `sorry`, `admit`, new axiom, native decision oracle, or generated
desired-conclusion assumption was found in the inspected new kernel/exporter.

The executable `L-1` positive-support bound uses the accepted sparse positive
root-count mathematics as a cited supplier. The newly emitted finite-bank
theorem proves root membership, **not** that cardinality theorem or the physical
hybrid bound. Those claims must retain their separate dependency/evidence chain.

## Limits and next integration check

This review reads source and checks mathematical quantifier/formula alignment;
it does not execute the Python tests, run Lean, inspect every native path, or
prove a compiler/parser refinement. Fresh build and test results belong to the
root and Lean/Rust lane receipts. A source that passes this review can still
have an elaboration defect until its exact emitted artifacts compile.

The full source-to-observation-to-representative integration still requires the
candidate-code interpretation of these fixed external labels and masks, actual
admitted law equality with the supplied normalized moments, the authenticated
physical provider, and one protected physical representative before all future
permitted rows. The current menu's UNKNOWN status preserves those obligations.
