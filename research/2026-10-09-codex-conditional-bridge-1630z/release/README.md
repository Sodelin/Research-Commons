# Practical release correction and launch integration

Contributor: Codex release lane for Nolan. Publisher: root coordinator.
This packet preserves authored execution; the sibling validation packet records
independent replays. Mathematical source-provider acceptance and Lean kernel
verification are separate evidence tiers.

The launcher now records successful process creation rather than inferring
invocation from a numerical-branch exception. `solver_called` remains false on
staging, authentication and `Popen` failures. It becomes true immediately after
the producer starts and remains true when that process or the subsequent
checker fails. Separate `checker_called` and `diagnostic_called` flags retain
their own meaning. A fresh recheck invokes only the checker.

[BASELINE-DEFECT.json](BASELINE-DEFECT.json) preserves an actual isolated CLI
reproduction using the original launcher SHA256
`b3bb290eb899f5a5550907047115de989d35a16d78b6b9cdb8f178b5ad046143`:
authenticated manifest tamper refused before producer/checker dispatch, but
incorrectly reported `solver_called=true`. It corrects the pending issue in
[dot's provenance review](../../../handoffs/2026-10-07-codex-cloud-sol-ultra-g5-g6/inbox/G6/20261009T025100Z-DOT-PRACTICAL-LAUNCH-PROVENANCE-REVIEW.md).
Earlier release validation receipts and numerical results are preserved.

[PROVENANCE-AND-CLI-RESULTS.json](PROVENANCE-AND-CLI-RESULTS.json) records 13/13
authored bounded cases, including literal manifest tamper, actual staged-source
authentication refusal, isolated staging and process-creation failures,
genuinely launched failing producer/checker controls, fresh informative and
finite-data journal replay, saved display, fresh independent recheck,
MOCK_SYNTHETIC/zero-live molecular computation and archived-panel audit.

Replay in a fresh scratch directory from the repository root:

```sh
python3 -B research/2026-10-09-codex-conditional-bridge-1630z/release/test_release.py --output /tmp/conditional-bridge-release-new
```

The harness supplies a minimal clean environment, 80-second CPU/110-second
wall/768-MiB address-space/32-MiB per-file caps. Each application child retains
its stricter 30-second CPU/45-second wall/512-MiB/16-MiB caps. It recomputes
whole-union widths from every retained cell and requires complete semantic
journal replay, rather than checking exit codes or hashes alone. It leaves
production sources unchanged. Large runtime/journal files stay in scratch;
packet receipts preserve exact commands, source hashes, statuses and log
hashes. Small stdout/stderr logs are included.

The fresh informative replay retains maximum normalized width
`17394377843899475/4611686018427387904`; the finite-data replay remains UNKNOWN
with all nine widths one and the inherited exact `3/55` ambiguity. These are
conditional arithmetic results, not source existence, empirical confidence
or measured biological accuracy. Rust remains an optional post-checker pair
diagnostic; this lane does not claim a fresh Rust build or quantum speedup.

The biology change is label-only: `ingestion.py` is explicitly an
**archived-panel audit**, with additive `audit_kind: ARCHIVED_PANEL_AUDIT`.
Pinned extraction/forward receipts remain inherited, and containment is freshly
rechecked. No generic alignment-to-observation intake, new confidence event or
new biological admission is introduced. The molecular fixture retains its
MOCK_SYNTHETIC and no-live-call labels.

See [researcher limitations and failure recovery](LIMITATIONS.md) and the
[current application README](../../../applications/practical-solver/README.md).
The inherited runtime `SOURCE-IDENTITIES.json` and every historical hashed
release manifest remain unchanged. [DERIVATIVE-MANIFEST.json](DERIVATIVE-MANIFEST.json) records current launcher,
documentation and audit-label derivatives alongside preserved inherited pins.

[FINAL-RESULTS.json](FINAL-RESULTS.json) records **21/21 PASS** on frozen
production code. The exact authored command was:

```sh
python3 -B research/2026-10-09-codex-conditional-bridge-1630z/release/test_release.py --output /workspace/scratch/bridge-release-regression-final21 --backend-python /workspace/scratch/conditional-bridge-bounded/venv/bin/python
```

That prepared backend is a pinned disposable environment created by the
bounded lane. The default 18-case standard-library suite needs no provisioning;
the optional three backend cases establish an actual shared-source witness,
a checked finite-registry exclusion and bounded-exhaustion UNKNOWN through the
integrated launcher. The graph example independently yields exact 7/192; an
invalid zero survival is refused. Conditional count arithmetic gives delta=1/2
and ceiling=24 while provider and core-catalogue verification remain unavailable.
Missing backend invocation remains UNKNOWN. No status is converted into
unrestricted NO. Small final logs are under [final21-logs/](final21-logs/).

The separate [17-case integration receipt](INTEGRATION-PRELIMINARY-RESULTS.json)
and initial 13-case receipt remain preserved. Final application documentation
also links the current bridge byte verifier and the archived release checker;
the latter intentionally detects changed current derivative files. Byte
integrity is separate from semantic certification. The final source manifest
pins documentation after its last label/link clarification; that docs-only
change followed numerical execution. Independent final replay is recorded in
the [validation packet](../validation/).

[REPORT-SEMANTIC-SMOKE.json](REPORT-SEMANTIC-SMOKE.json) additionally checks
seven exported HTML reports for fresh/saved/rechecked labels, UNKNOWN/count
text, the exact graph probability and failed-component status. It checks static
report content; no browser rendering test is claimed.

A launched component exit code 1 without result or semantic refusal evidence
is now an execution failure. It is not classified as invalid input merely
from its exit code. The added crash control passes alongside the actual
zero-survival refusal control.

[POST-FREEZE-INTEGRITY-FAILURE.json](POST-FREEZE-INTEGRITY-FAILURE.json)
preserves detection of a bounded-module correction after an earlier source
snapshot. The two earlier 20-case receipts remain available under
[AUTHORED-20-BEFORE-FINAL-FREEZE.json](AUTHORED-20-BEFORE-FINAL-FREEZE.json) and
[AUTHORED-20-BEFORE-SEMANTIC-REFUSAL-CHECK.json](AUTHORED-20-BEFORE-SEMANTIC-REFUSAL-CHECK.json).
A final replay uses the definitive bounded source and semantic-refusal
launcher correction. These source changes do not withdraw the older scoped
numerical results.
