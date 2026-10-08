# Public wrapper offline validation

Contributor: Codex integration G5 lane, 8 October 2026. **TESTED RESULT, scoped offline application validation.** Source was read only; outputs were confined to local validation scratch. Root owns wrapper changes and publication. No compiler, build, live model call or contact was performed.

The workbench demo, both molecular RNA mocks and the existing native haplotype mock ran successfully through the public wrapper. An initial nine-command batch checked actual JSON/HTML reports, catalogue answers and refusals rather than exit codes alone. After root corrected unavailable-executable reporting and added the readable public-marker comparison/replay option, three targeted commands on the final frozen wrapper passed. The [sanitized exact-hash receipt](PUBLIC-WRAPPER-VALIDATION.json) records source pins, command templates, stdout/stderr and report hashes, and each assertion.

| Source revision / actual operation | Result inspected |
|---|---|
| Initial `34dceb602930…`: workbench | Exit 0, demo PASS and seven checks true. Cap4 and original-arm ambiguity abstain; cap5 certifies only within the supplied point catalogue. Fresh-locus confidence is conditional, counts 256 independent observation units and ignores one identical same-locus duplicate. Source/independence/eta promises and whole-app Lean are not promoted. |
| Initial: molecular with existing native binary | Exit 0, three nested SUCCESS / MOCK_SYNTHETIC results. Native REF/A/B/AB have four distinct digests, length 131072 and positively contiguous sequence coordinate maps. Hypothetical AB is counterfactual; no diploid aggregation is guessed. |
| Initial: molecular without a native argument / with a missing binary | Omitted native argument explicitly reports haplotype UNAVAILABLE while two RNA jobs succeed. Missing binary returns wrapper exit 3 / EXECUTION_FAILURE, retaining nested UNSUPPORTED / CORE_UNAVAILABLE and false computation success. |
| Initial: input/runtime refusals | Missing required sequence arguments refuse before output creation. Reusing an output directory returns exit 2 and preserves the original workbench report digest. Direct RNA REF mismatch returns INVALID_INPUT / REFERENCE_MISMATCH; contradictory same-locus records are refused. |
| Initial missing-runtime gap; fixed derivative `bc45cdd8f929…` | Initial exit 2 created a directory but no report. Root's correction was actually retested: exit 3 and both reports expose EXECUTION_FAILURE / EXECUTABLE_UNAVAILABLE. The initial observation is preserved, not silently overwritten. |
| Final `7d41762c3594…`: missing runtime | Repeated on final bytes: exit 3, JSON/HTML failure report and explicit unavailable child executable. |
| Final: default `cwu` | Exit 0; marks source controls and public marker receipts as recovered saved evidence. The readable table preserves both original-taxon splits and marker counts. |
| Final: `cwu --replay-sequences` | Exit 0 in about 2.01 seconds; freshly rebuilds and verifies both public marker workbench receipts from the frozen GenBank input. Marks marker execution REPLAYED_NOW while source controls remain saved. Input/alignment digests and the retained geometry match the saved recipe. |

The initial batch passed 61 report/semantic assertions. Five further saved-report checks authenticated all native coordinate-map spans and preservation of the workbench report. The intermediate runtime derivative passed 11 assertions; final targeted commands passed 63. These are assertions across 13 actual application commands, not 140 independent scientific experiments. Public Python source bytes were unchanged during each validation batch; all 31 inherited Python files in the initial batch remain identical in the final batch. Only the owner's wrapper derivatives changed. The initial full smoke batch is pinned to its initial hash; it was not silently attributed to final bytes.

The final human table gives nuclear **4CL1: 1048 sites, 100% of 100 column-bootstrap replicates**, and plastid **rbcL: 1428 sites, 93% of 100 replicates**, with the exact original taxon pairs preserved. Column resampling is explicitly descriptive. The homology-inferred, unannotated `T. chinensis` rbcL region remains labeled. Both biological targets ABSTAIN; capture is UNKNOWN and empirical solver admission NOT_ADMITTED. The replay uses actual public sequences but does not replicate the complete paper alignments or independently authenticate physical specimens, orthology, ancestry independence or a compartment/source channel.

All three TERT mock interactions were exactly **zero**, although edited sequence digests differ. This establishes sequence assembly and endpoint plumbing, not effective nonadditivity, measured RNA or biological conclusions. The RNA PAS endpoint is a derived annotated-window coverage ratio proxy; its declared log-ratio arithmetic was independently recomputed. Every inspected wrapper report retained biological conclusion NOT_ESTABLISHED, zero live model calls and false whole-application Lean verification.

From the Commons root, happy-path command templates are:

```sh
"$PYTHON" -B applications/scientific-integration/run.py workbench --python "$PYTHON" --output "$FRESH_OUTPUT"
"$PYTHON" -B applications/scientific-integration/run.py molecular --python "$PYTHON" --core-binary "$CORE_BINARY" --output "$FRESH_OUTPUT"
"$PYTHON" -B applications/scientific-integration/run.py cwu --python "$PYTHON" --replay-sequences --output "$FRESH_OUTPUT"
```

`PYTHON` is the supplied runtime with Biopython 1.88, `CORE_BINARY` is the existing native binary pinned by SHA256 `e4024df7e801c2fb81bef4740d664a9edc4b56743052adbd4b994e974d0fd2ed`, and every operation needs a different fresh output directory. These are portable templates; exact local commands and raw report artifacts remain in `/workspace/scratch/integration-g5/public-wrapper-validation`, authenticated by the public receipt. No private implementation, raw product receipt or sequence content is copied into this note.

The [application traceability map](APPLICATION-TRACEABILITY.md) retains BIO-1/NANUQ, G5/M3/HG, G6/G7 and wider programme obligations with scoped [independent source acceptance](../review/SOURCE-COMPONENTS-REVIEW.md). Its earlier “review pending” sentence is historical; the later review accepts SHA256 `171d2457…`. This application validation does not compile or strengthen the [formal G5 source checkpoint](README.md). One next practical action is reviewer authentication of these exact validation bytes and root's public-wrapper release; scientific certificates still require the stated data/source/observation bridge.
