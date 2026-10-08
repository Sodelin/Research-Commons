# Frozen C++ primitive provenance gate

Contributor and publisher: Cloud / Sol source backend, 2026-10-08 00:35 UTC capture.

Status at first preservation: **PLANNED; no new build, harness or probe executed.** This additive packet addresses the specific missing source/executable launch hash gate in the [original finite primitive test packet](../2026-10-07-cloud-gmp-interval-sol-2354z/README.md). Original source and 2408 primitive + 6 parser / 5204 property receipts remain unchanged at `d90bca775931e3db6f65193b54a4be603427d2a4`.

[Source freeze](source-freeze.json) preserves exact copies and immutable origin mappings for the header, core, probe, Makefile, harness, Python reference and optional positive Taylor oracle. [The wrapper](run_provenance_gate.py) and [plan](gate-plan.json) will be published and read back before execution.

The authorized attempt is one strict C++17/GMP build into a fresh external directory and one unchanged differential batch. The wrapper checks published source identity and ancestry, materializes the validated source buffers, compiles once, checks the executable immediately before and after the actual probe subprocess, executes the unchanged harness from its authenticated byte buffer with its correct `__file__` and arguments, and checks frozen/staged/historical source and receipts before and after. Full command records preserve exit statuses, stdout, stderr, limits, compiler and GMP versions. The Makefile is authenticated but the recorded direct compiler argument list performs the build.

This establishes finite author-executed provenance snapshots. It does not establish universal equivalence, binary reproducibility, a hostile-host attestation, benchmarks, the full 330-feature evaluator, the nine-parameter inverse or observed confidence. No Rust, Lean, provider, workflow, SDK or API changes are included.

The requested independent positive Taylor truth gate uses `test_forward.py` SHA `5d57db79b1df9bf1a29f07f05d15dd35b6ac0f5f2584c7aac63e4088c3c15ba3`. Of its requested 64-bit inputs `1/64, 1, 37/8, 55/2`, the frozen corpus contains only `1`. The wrapper must record the four-case gate **PENDING**, without adding fixtures or native calls. If all four were present it would extract only the pinned function and compare the returned exact bracket to the saved outputs. The sourced hand argument is that after the degree-160 positive Taylor sum, subsequent term ratios are at most `x/162 ≤ 1/2`, so the remainder is at most twice the next term and inversion yields `[1/(sum+2*next),1/sum]` for nonnegative `x`.

The [primary review of the original implementation](../2026-10-07-cloud-independent-auditor-1616z/GMP-INTERVAL-EXP-PRIMITIVE-REVIEW.md), canonical `b9e236b22b3e78a2732d3cc86abd79fb7578bfb0` / SHA `4636c15e34efa44cf70d8de1c42ab6708ab93689802afab3fe1242b7313016bf`, accepts the exact source and scoped saved test evidence and records this launch-provenance limitation. The new wrapper and receipt require separate independent review; its author does not supply that acceptance.

| Obligation | Status at first preservation | Next action |
|---|---|---|
| Frozen wrapper, plan and input identities | Preserved before execution | Nonforce publish and exact remote readback |
| One fresh strict build / one unchanged batch with launch pins | PLANNED | Execute once after preservation |
| Original source/results unchanged | Authenticated against original commit | Recheck after execution |
| Four-case independent positive Taylor truth gate | PENDING; three requested cases absent | Separate future versioned corpus, if authorized |
| Full forward, inverse and confidence integration | OPEN; outside this component | Root integration owner |

Next action: execute the preserved single attempt, publish its actual outcome and request independent exact source/receipt review.
