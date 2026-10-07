# Saved G5/G6 rebuild: actual successful results

Codex coordinator for Nolan. Requested rebuild input 0f0c173f385c3633595b3068cf3d7bae0bd9fcf0; baseline scientific snapshot 2aeb123fb53b61594a1cf5b0542daf953cf90ab3. Final evidence checked 2026-10-07T15:28:26Z (08:28:26 Pacific). Engineering G6 replay execution by the existing Codex g6_value review worker; root independently verified source/log identities and outcomes. No additional Astra research chat, slot reassignment, source edits or setting changes.

| Saved target | Actual new result |
|---|---|
| G5 corrected finite polynomial/mixture Lean module | Fresh pinned source compilation PASSED; all 18 component declarations report only propext, Classical.choice, Quot.sound; no sorryAx or compiler-trust axioms. |
| G6 source/count reference suite | 1143 exact controls PASSED, exit 0; three source blobs verified; new stdout/stderr and JSON retained. |
| G6 boundary-forest/carrier suite | 770 exact controls PASSED, exit 0; new full case report/stdout/stderr retained. |

## Lean replay

[Actual successful run 37643836409](https://github.com/Sodelin/Research-Commons/actions/runs/37643836409), job 112869305240, attempt 1; frozen input 0f0c173f385c3633595b3068cf3d7bae0bd9fcf0. Run completed success at 15:27:20Z. The full log includes archive/executable checks, exact Mathlib checkout and Lake dependency manifest, 1920 selected cache files, actual compiler output and the marker tying compilation to the input commit/blob.

[G5 full job log](g5-lean-job.log), [run receipt](g5-run-receipt.json), [all 18 axiom reports](g5-component-axioms.json) and [job steps](g5-job-steps.json) are preserved. Lean 4.33.1 compiler 819816b2e0a3bf405af45ae5c7af2491d8f5bee6 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 match the previous pins. Checked proof blob c9e470498aa30bb1f712006484726bfb1193cf4f is unchanged. Same three nonfatal tactic-linter warnings remain. No proof error.

This is ordinary fresh compilation of the saved G5 component with official precompiled library dependencies, not a fresh whole-Mathlib rebuild or the unchecked hidden-register/G2 consumer. No complete G5 or G6 master closure follows.

## G6 exact-source reconstruction

Sources were faithfully reconstructed from main snapshot 2aeb123fb53b61594a1cf5b0542daf953cf90ab3. All3 Git blobs and SHA256s were verified before/after execution, without source edits. Full identities are in [SOURCE-IDENTITIES.json](g6/SOURCE-IDENTITIES.json).

Serial execution on Python 3.12.14 (Linux), 180-second cap per job:

- test_finite_source_prefix.py: 15:25:30.706892–15:25:30.882484Z, 1143 controls, exit 0.
- forest_pair_controls.py --output <new-file>: 15:25:30.885588–15:25:31.277810Z, 770 controls, exit 0.

[Summary](g6/REPLAY-SUMMARY.json), [1143 receipt](g6/reference-1143.NEW-EXECUTION-RECEIPT.json), [770 receipt](g6/forest-770.NEW-EXECUTION-RECEIPT.json), all stdout/stderr streams, both detailed new original-script reports and the exact executed wrapper are saved beneath g6/. Root checked every stdout/stderr hash against its receipt. Both stderr files are empty. Source hashes remained unchanged.

For a new replay, materialize ONLY the three frozen source/test files into a NEW empty directory, then run the two original commands there with a new forest output filename. The source/count script writes evidence/reference-tests.json, so do not run it directly over an existing preserved evidence directory. run_fresh_replays.py is the exact executed wrapper with this execution's original absolute paths, preserved for provenance; the receipts give actual argv/cwd and environment.

## Preservation limit and next work

These are NEW execution receipts. They reconstruct reproducible evidence from committed source; they do not recover the missing historical 770-run output, its timestamps or its original Python 3.13.5 environment. Original historical source/1143 evidence remain unchanged. G6's original forest receipt request stays unresolved if the original output is still unavailable; the new 770 replay is now a durable separate result.

Finite rational controls are not Lean or an all-size proof. The all-source/calendar/shared-target/statistical master and actual-source adapters retain their original obligations. Next formal work: implement the scaled finite subprobability/count-source lemma from G6's saved COUNT-SOURCE handoff, retain its source and joint-observation gates, then progress contextual compression. No new G6 Lean theorem was implemented in this replay.

11. Process integrity: exact frozen inputs, bounded serial runs, complete new outputs, pin/axiom checks and source/log hash verification; no retroactive historical receipt claim.
12. Robustness: G5 component reproduces pinned compilation; 1,913 finite G6 checks reproduce on a different recorded Python version. This does not establish full scientific master closure or infer unseen chat activity.
