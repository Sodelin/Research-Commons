# ProofBridge: exact integer linear certificates

The [first pilot](https://github.com/Sodelin/Research-Commons/tree/b2c0ba4bc831ecb975fa379f68a622e1ac026164/research/2026-11-25-proofbridge-pilot) is preserved. This extension accepts user-authored integer linear implications, not just one prewritten theorem. One record emits a short hand derivation, a Lean theorem with explicit assumptions, and SMT-LIB. It does not ingest arbitrary prose, prove the supplied assumptions, or address the analytic Goldbach conjecture.

Use Python 3 and an already-installed elan Lean 4.33.1 (commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6). The runtime does not need Mathlib for this fragment:

```
python linear.py render-hand goldbach-budget.json
python linear.py render-lean goldbach-budget.json
python linear.py render-smt goldbach-budget.json
python linear.py check goldbach-budget.json
python linear.py batch . --limit 2 --budget 120
python linear.py batch . --after combine.json --budget 120
```

Write one coefficient per variable, chosen in a fixed order. Each premise and the target have a vector `coeffs` and a bound `le`; all are inequalities of the form coefficients times variables <= bound. Supply one nonnegative integer multiplier per premise. Python verifies exact coefficient equality and the combined bound. Generated Lean independently derives the weighted sum of nonnegative slacks, then explicitly clears the original premises before `omega` checks the implication from the combined bound. This prevents the final tactic from quietly replacing a bad witness with a different proof from the original premises.

Tested: two different records were accepted as conditional theorems, with [propext, Quot.sound]. The changed 188 threshold was rejected by Python and by separately compiling its generated Lean; retaining the 187 target but dropping the margin multiplier also failed in Lean. Batch processed two sorted inputs, emitted a deferral, then resumed the third with `--after`. A nonzero batch exit signals at least one attempted failure. Preserve JSONL outside the input directory; resume after the last attempted file on a frozen list. No cache skips, directory recursion, or arbitrary agent actions. This uses an exact integer encoding of budget arithmetic only, not the original normalized real-variable analytic estimates.

`--smt` on `check` attempts a separate advisory Z3 call if its executable is installed. Providing SMT-LIB and accepting this API are not evidence of an SMT run: Z3/cvc5 were unavailable in the validating environment. No external solver, Mathlib adapter, arbitrary rational proof language or general autoformalization was verified here. [Lean omega](https://lean-lang.org/doc/reference/latest/Tactic-Proofs/Tactic-Reference/) does the last normalization; [Mathlib linear_combination](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Tactic/LinearCombination.html) is the next route for explicitly supplied rational combinations. [Lean-SMT](https://github.com/ufmg-smite/lean-smt) is a separate reconstruction path; use a compatible project pin and require all generated goals to close, then inspect axioms. A solver reporting UNSAT does not authorize a verification receipt.

## Five workstreams

1. **Typed authoring:** exact linear and one-rounding certificates; [stable theorem and premise handoff](ASSUMPTION-RELAY.md). Hand prose still needs a typed statement.
2. **Kernel:** [checked import](import-reduced.receipt.json) of a reduced theorem into a second module, with an exact weaker-provider rejection. No trusted cache skip.
3. **SMT:** [one-step rounding synthesis](ROUNDING.md) checked independently in Lean. Not a general SMT proof importer or Mathlib adapter.
4. **Cloud batch:** [mixed resumable replay](BATCH.md) with immutable manifest, per-entry receipts and generated module hashes. Automatic pickup and the larger backlog trial are pending.
5. **Discovery:** [theorem intake](../../docs/discovery/THEOREM-INTAKE.md) exports both supported types and attaches [typed replay evidence](rounded-discovery.receipt.json) without changing authored conjecture status.

## Cloud-verified narrow SMT route

`python3 smt_witness.py goldbach-budget.goal.json --lean /path/to/lean --z3-library /path/to/libz3.so --mutate` uses the [Z3 C API](https://z3prover.github.io/api/html/group__capi) to find nonnegative integer combination coefficients, then checks the actual coefficient witness in pinned Lean. See [success](smt-witness.receipt.json) and [no-witness](smt-no-witness.receipt.json). The goal record contains no coefficients. The 187 budget statement is conditional on its original supplied bounds; a changed witness failed Lean and the 188 target had no witness in this restricted system. No witness does not generally refute a theorem, and the code is not a general SMT-proof importer or a Mathlib route. Earlier notes above describe the pre-synthesis state.

For the mixed batch handoff of prior SMT witnesses into fresh Lean modules see [Batch replay](BATCH.md#mixed-legacy-and-integer-rounding-replay) and [integer rounding](ROUNDING.md).
