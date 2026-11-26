# Lean bank: listener, source locator, and proof evidence

The purpose is to stop losing work, not to assign a proof label to every file.

| Layer | Exact commitment | Failure behavior |
|---|---|---|
| Main listener | Listen to every push to main, without GitHub changed-path filters. Scan the immutable triggering Git tree. Daily reconciliation and manual dispatch use the same workflow. | GitHub can delay or drop jobs. A superseded run visibly does not publish. Nothing claims current until a successful covered snapshot. |
| Git coverage gate | The committed regular-file tuples (path, category, Git blob) in the declared scope must match every indexed row. Re-read the tree independently of the scanner and check all 256 shards. | Missing, extra, stale, wrong-category, duplicate and malformed rows fail the job, even if the altered index was rehashed. The previous good snapshot stays published; the error is in GitHub Actions. |
| Incremental scan | Search hints come from source bodies only when missing, changed, or under a new extraction version. Reuse an old hint only at the same path, kind and exact Git blob after checking manifest and shard hashes. | A bad cache rebuilds from Git; verified coverage still gates publication. Hints are not declaration elaboration. |
| Public provider intake | An approved repo, immutable revision and exact paths authorize a bounded metadata-only read. The worker verifies hashed Git trees and corroborates files through parent directory metadata. The index accepts providers by registry, not hard-coded filename selection. | Public GitHub failures remain unavailable. Pinned registrations do not move automatically. No private sources or blobs are read by this hosted provider observer. |
| Selected package source closure | Resolve explicit modules and import prefixes, plan one pinned fetch at a time, verify staged bytes, order dependencies. | Unavailable package, unmapped import or toolchain dependency remains pending or unsupported. No Lake hook, arbitrary file execution or compiler verification. |
| Proof evidence ingress | Require separate trusted registry and trusted receipt ledger pins. Bind by exact job, source commit, statement, checker/stage and inputs. | Indexed files do not confer proof status; SMT unknown is not discharged; synthetic tests cannot produce a real theorem receipt. A trusted prior receipt isn't a fresh replay. |

## What to commit so it can't fall between the cracks

The defined coverage scope is regular UTF-8 Git paths under research/, packages/research/, lean/, and docs/discovery/lean-bank/. Commit Lean as .lean, write-ups as Markdown or MDX, and receipts as *.receipt.json, *-receipt.json, receipt.json, or SHA256SUMS. Markdown in the bank's tools subfolder is excluded. Symlinks, gitlinks, unsupported paths and extensions, uncommitted scraps, other branches and other repositories are not counted in the guarantee. The indexed coverage is **at a named commit**, not a guarantee of hosted uptime or proof of truth. GitHub's changed-path filter behavior is documented in [workflow syntax](https://docs.github.com/en/actions/reference/workflows-and-actions/workflow-syntax#git-diff-comparisons); scheduled events may be delayed as described in [event documentation](https://docs.github.com/en/actions/reference/workflows-and-actions/events-that-trigger-workflows#schedule).

## How to see and use it

    node docs/discovery/tools/query.mjs --lean-bank "TriangleRun" --layer commons_git_source
    node docs/discovery/tools/query.mjs --lean-bank "inventory only" --layer commons_coverage_receipt
    node docs/discovery/tools/query.mjs --lean-bank "lean4 core" --layer external_source_only
    python docs/discovery/lean-bank/automation/index_health.py --repo . --head HEAD --verify-shards

- Generated index, coverage report, check battery and normal search smoke report live under docs/discovery/generated-source-index/. The last good snapshot is checked before no-op publication; cached metadata is never the sole proof of coverage.
- [Approved provider input](providers/reference/approved.json), [independent snapshot checker](providers/project_intake.py) and [bounded metadata-only requester](providers/fetch_public_metadata.py). The selected Lean 4 core snapshot is at compiler commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. It is a four-file demonstration, not a complete import of Lean or arbitrary external repositories. Expanding a project requires explicit pinned source roots and bounded metadata; selecting a file does not install that version.
- [Actual Thue–Morse closure fixture](closure/results/thue-complete-plan.json): nine upstream files and two local files; raw source closure present, toolchain modules separately unverified by the planner. [Proof-job intake boundary](jobs/README.md). Current hosted runner still does not have the pinned Lean runtime, and no new SMT job is registered; it does not declare theorems proved.
- [Integrated local test suite](ALL-TESTS.log) and [real-file staged smoke test](STAGED-E2E.log). These are supplemental to hosted receipts, not evidence that the hosted daily backstop already fired.

## Reflection

**Best:** exact coverage is checked against Git itself, so recomputing an index hash cannot hide an omission. **Worst:** one generic “verified” column would make the whole system misleading; a source locator, a solver run and a kernel proof are different facts. **Most interesting:** reuse is safest at immutable file bytes, and its value is the ability to cheaply answer narrower questions. A Thue–Morse target can ask for its own import closure rather than loading every formal project. **Still weak:** declaration hints are text-based, external snapshots are bounded and opt-in, and automatic trusted proof-job production is not in place. The next investment should be a single real new proof job with a trusted Lean receipt, not bulk cloning or an automatic claim of correctness.
