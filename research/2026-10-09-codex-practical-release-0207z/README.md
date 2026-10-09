# Researcher-facing practical solver release

Contributor: Codex coordinator with four direct roles, 9 October 2026.

The additive release candidate integrates the inherited nine-parameter
producer, separate whole-journal checker, optional native/reference diagnostic,
scientific input limits and evidence exports. Its examples keep numerical
localization, finite-data uncertainty and model refusal visibly distinct.

Start at [the application](../../applications/practical-solver/README.md).
Read the [research report](RESEARCH-REPORT.md),
[independent review](validation/INDEPENDENT-REVIEW.md) and
[Nolan walkthrough](validation/NOLAN-WALKTHROUGH.md).

- [Recovered scope and ownership](RECOVERY-AND-OWNERSHIP.md)
- [Original-master and release obligations](OBLIGATIONS.md)
- [G1–G7 and theorem-to-software contracts](contracts/CAPABILITY-MAP.md)
- [Biological inputs and uncertainty](biology/BIOLOGICAL-INPUTS.md)
- [Existing-method comparison](validation/COMPARISON.md)
- [Read-only private identity summary](PRIVATE-REVIEW-SUMMARY.json)
- [Byte-integrity verifier](verify_release.py)

The application is useful without closing general G3/G4. The finite-data
example remains UNKNOWN and empirical all-nine accuracy remains unverified.
Rust remains a post-checker diagnostic. New contract drafts do not acquire
Lean-checked status without a matching compiler receipt.

From the repository root, verify packaged file identities with:

```sh
python3 -B research/2026-10-09-codex-practical-release-0207z/verify_release.py
```

This checks bytes only, not scientific validity. Exact fresh-run, build,
review and resource evidence is linked from the application and lane records.
Earlier artifacts, failed tests and original source pins remain preserved.
