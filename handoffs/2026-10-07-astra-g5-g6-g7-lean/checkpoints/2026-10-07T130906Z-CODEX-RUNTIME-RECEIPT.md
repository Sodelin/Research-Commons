# Verified pinned Lean runtime receipt

Contributor: Codex coordinator for Nolan. Observed 2026-10-07T13:09:06Z.
Scope: execution route only; no G5/G6/G7 scientific theorem or Mathlib build.

- Source commit: 5a94f375c9e5538da65b3d3ed05d4d6aa40177f6, published on main; all nine changed files independently read back equal to prepared bytes.
- Workflow: .github/workflows/g567-lean-runtime.yml, push-triggered, contents read-only, serial concurrency group, ten-minute limit.
- Run: https://github.com/Sodelin/Research-Commons/actions/runs/37626100435, attempt 1; job 112808125473.
- Actual final run: completed / success; updated 2026-10-07T13:08:15Z. Job step summaries and full decoded job logs fetched independently.
- Official archive: lean-4.33.1-linux.tar.zst; SHA256 890afd185370f85666025b883914ab4f4b339136f8c96167b69cfb62aecaf235; checksum check reports OK.
- Actual compiler: Lean 4.33.1, x86_64-unknown-linux-gnu, full commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, Release.
- Actual executable SHA256: e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550, matching the inherited integration pin reported by G6.
- RuntimeSmoke.lean SHA256: 5114a5b2e77fa40336ddd9491ebc5f04e767a5c299b7ebdd637104b1f96d2758; compiled with --trust=0.
- Output: ResearchCommonsRuntime.runtimeSmoke does not depend on any axioms; RUNTIME_SMOKE_PASSED source_commit=5a94f375c9e5538da65b3d3ed05d4d6aa40177f6.

[Full retrieved job log](2026-10-07T130906Z-CODEX-RUNTIME-JOB.log) is preserved alongside this receipt. Logs originally generated in runner temp were not uploaded as Actions artifacts; this is a connector-retrieved copy now committed as an immutable record.

No local Lean process is running. The GitHub job completed. Future proof builds can use the verified installation route but still need pinned Mathlib setup, actual proof inputs, import/dependency/axiom audits and semantic validation. The runtime smoke theorem proves no research obligation.
