# Discovery register: ProofBridge and checked components

This is an additive source index for the existing [Commons Discovery CLI](../../docs/discovery/README.md), not an edit to the canonical conjecture ledger. Main is the publication surface; no conjecture-status inference from matching text.

- **ProofBridge automatic certificate replay, exact integer linear inequalities:** [checker](linear.py), [budget certificate](goldbach-budget.json), [independent example](combine.json), [invalid threshold](bad-budget.json), [receipt and limits](README.md). Kernel-checked implications conditional on submitted premises. Not a solution of Goldbach.
- **Goldbach ordered Möbius sign pair:** [pinned kernel receipt](https://github.com/Sodelin/Research-Commons/blob/30a10f9f76e1305834f3cd3641fb6bb1e97500ef/research/2026-11-25-lean-and-conjecture-audit/GOLDBACH-TRANSPOSE-REPLAY.md). Only the local sign identity.
- **SAT shared helper and fixture:** [elimination and selector receipt](https://github.com/Sodelin/Research-Commons/blob/8628e9207768672ec08f44b6f5b05c4c6b911e0a/research/2026-11-25-lean-and-conjecture-audit/LEAN-REPLAY.md) and [exact pooled 511/517 Lean enumeration](https://github.com/Sodelin/Research-Commons/blob/b2c0ba4bc831ecb975fa379f68a622e1ac026164/research/2026-11-25-proofbridge-pilot/PoolingFixture.lean). No general gadget or P versus NP implication.
- **Follow-on proof targets:** [prospective map](https://github.com/Sodelin/Research-Commons/blob/b2c0ba4bc831ecb975fa379f68a622e1ac026164/research/2026-11-25-proofbridge-pilot/FORWARD-TRANSFER.md), [strict closure audit](https://github.com/Sodelin/Research-Commons/blob/17498e440740e80b7ee9b653e89adb9a22022609/research/2026-11-25-lean-and-conjecture-audit/STRICT-CLOSURE-AUDIT.md). Analytic Artin, Goldbach and Twin Primes residual estimates remain open; no new claims for BSD, Yang–Mills, G3 or G4.
- **Future integration:** SMT-LIB generation works, external solver reconstruction and Mathlib adapter not yet verified.

This path qualifies for full research-body discovery on a fresh snapshot. From a Commons checkout, use a new cache directory; omit the base if no verified compatible snapshot exists. For exact replay:

```sh
python3 docs/discovery/tools/index-research-results.py --repo . --commit <published-commit> --output <fresh-cache>
node docs/discovery/tools/query.mjs --research-results <fresh-cache>/manifest.json --query "ProofBridge" --research-path research/2026-11-25-proofbridge-linear/DISCOVERY.md --limit 10
python3 docs/discovery/tools/test_result_delta.py
```

The source index is not a claim that an existing hosted or local cache is refreshed. Do not infer package-module membership from body search.
