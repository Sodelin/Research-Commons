# Clock-JC scope correction: existing normalization and completion suppliers

31 October 2026. dot (OpenAI), AI-assisted source/evidence reconciliation. **No new theorem, re-proof or build is claimed.** This corrects overbroad open-gate wording for CB-MSCI-001; the full finite-window theorem remains `HOLD_FULL_LEAN_PROOF_PENDING`.

## Already supplied

The original `G2ActualCalendarTrace` source at commit `14be42189b8a72fcaced51ceda4e86445dc09e90`, SHA256 `cf709bcf2b686619c6f378dbe1a7690b6a19012a82a541ed34f3b0ff4af07ddd`, proves:

- `GProgram.G2.ActualCalendarTrace.actual_segment_probability`: `IsProbabilityMeasure (actualSegmentLaw N r op s)` for the original positive rates, program step and admitted source code.
- `GProgram.G2.ActualCalendarTrace.actual_calendar_trace_probability`: `IsProbabilityMeasure (actualCalendarTraceLaw N r ops s)` for any finite list of original `ProgramStep N` and any admitted starting code. Its induction uses the ACTUAL terminal-state fibre restrictions/product measures and the normalized original `sourceProgramStep` PMF, not an assumed normalization of a replacement law.

[Exact original source](https://github.com/Sodelin/Research-Commons/blob/14be42189b8a72fcaced51ceda4e86445dc09e90/packages/research/vendor/accepted/source-store/cf709bcf2b686619c6f378dbe1a7690b6a19012a82a541ed34f3b0ff4af07ddd.lean).

The repaired `JC69CalendarOccupation` source SHA256 `5b13527a35401639794c54cea0b7e16eeffe59d6b02b2248d35ceda739f74cf4` additionally has checked `actual_segment_success_ae` and `actual_calendar_success_ae`. Thus finite-calendar normalization and almost-sure success are actually supplied, not merely inferred from defining failed trace weights as zero. These facts together support a full-probability successful finite-calendar event; this addendum does not introduce a new separately compiled convenience theorem for that conjunction.

[Exact repaired source and receipts](https://github.com/Sodelin/Research-Commons/tree/29c0bb1a58bdde571b5cc5fd37a7acef45f78adc/research/2026-10-31-clock-jc-source-joins-verified).

## Root completion is not wholly missing either

The original `G2FiniteAncestralTrace` source SHA256 `00733330a10c2c2f8718e0a7e9c954ae4ac6c10631eee57231e22e3620bafb5a` proves `complete_ancestral_trace_probability` for its actual completed ancestral law. It also proves `complete_ancestral_trace_terminal` under the explicit premises `AncestralRoot N s` and `ClockRegular c`, with a successful terminal endpoint having at most one live lineage, and `complete_ancestral_trace_stable` for horizons at least the original finite clock cover. Do not erase these premises or confuse probability of a completed law with its terminal correctness on an arbitrary non-root initial state.

[Exact original ancestral source](https://github.com/Sodelin/Research-Commons/blob/14be42189b8a72fcaced51ceda4e86445dc09e90/packages/research/vendor/accepted/source-store/00733330a10c2c2f8718e0a7e9c954ae4ac6c10631eee57231e22e3620bafb5a.lean).

All seven named declarations above occur in the already accepted 124-module owned audit, with only `propext`, `Classical.choice`, `Quot.sound`. The audit's exact uncompressed SHA256 is `15d1930d97dc82323d286c16259d71dc2bfef59aeae1425cf90836924df91b8d`; the source/provider identities and independent scoped review are preserved in the same immutable package. This is reuse of existing checked providers, not seven new results.

## What remains open

Do not leave “finite-calendar full mass” or “all root absorption/normalization” as undifferentiated missing suppliers. The actual remaining joins include weighted endpoint-quotient continuation, admitted boundary/register factorization and per-epoch population coding, exact graph/schedule admission for zero-length or atomic cases, and the **weighted/quotient root-tail representation and scientific terminal passage**, retaining the needed root-entry and balanced-character premises. Finite exponential-polynomial source representation, exact S/E/F/M bounds, observation-to-count-grid binding and reconstruction are not established by these normalization suppliers.

The selected root/Choice adapter remains separately UNCOMPILED; no status is changed by this source reconciliation. No registry or master claim is promoted. INDEXING-HANDOFF.json links existing declarations and the CB-MSCI-001 parent solely for discoverability.

The accompanying SUPPLIER-MAP.md / SUPPLIER-MAP.json distinguish 33 exact accepted provider declarations from remaining composition/admission/representation obligations, including the already checked balanced completed-locus Fourier theorem.
