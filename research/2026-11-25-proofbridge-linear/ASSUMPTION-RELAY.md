# Assumption feedback without reading Lean

From this directory: `python assumption_relay.py assumptions-fixture.json`.

The relay kernel-checks the original conditional implication, removes every zero-weight premise from the supplied linear certificate, and kernel-checks a genuinely smaller theorem. It checks that the reported variable list and conclusion have stayed identical, then emits the old and new assumptions, axiom reports, and the reusable reduced certificate. This is deletion justified by the explicit certificate, not a claim that all remaining premises are necessary. With no zero weights the report says this method found none; a different proof may still use fewer. No arbitrary prose conversion, general hypothesis search, or Google Drive event wiring is asserted.

The worked example encodes integer budget arithmetic. It removes the two added nonnegativity assumptions for the charges (premises 4 and 5), while keeping the three actual budget bounds and exactly the same 187 conclusion. This is not a new analytic Goldbach estimate or a claim that an original research proof depended on the two demonstration premises. Both theorem receipts are kernel-checked using Lean 4.33.1 and list only propext and Quot.sound.

Next: use one pinned source statement and named premises, add a bounded leave-one-out proof search for used premises, and verify any replacement without the removed premise. Queue immutable source/candidate/receipt records privately in Drive; never execute a raw program from a mailbox item. Keep public code and private input permissions independent. Report a failed search as inconclusive, not as necessity.

## Source-bound premise handoff

`premise_handoff.py` adds a typed producer/consumer route without changing the original relay. The caller supplies the theorem ID from its register and the SHA-256 of independently pinned source certificate bytes. Each inequality ID uses a canonical sorted list of variable names and integer coefficients (including zero coefficients), plus its bound. IDs survive reordered premises or consistently reordered named columns, but they are not a test of logical equivalence. Exact duplicates are rejected rather than silently collapsed. The source hash deliberately changes if source bytes are reordered.

```sh
pin=11ee5daae50ecd0f02cf7ea846e8770b47976b8e6b54498a0662aa9351c8e3ff
id=goldbach.integer-budget-187
python3 premise_handoff.py produce "$id" "$pin" assumptions-fixture.json > handoff.json
python3 premise_handoff.py consume "$id" "$pin" assumptions-fixture.json handoff.json
```

The consumer reconstructs the expected retained and dropped IDs from the independently pinned source, refuses a changed target or ID, and replays the generated reduced proof in Lean. It grants no verification from the submitted producer receipts. Use `--lean /path/to/pinned/lean` before the operation with a trusted direct executable. [Replay and negative controls](premise-handoff.receipt.json) preserve the 187 target with three supplied budget bounds, removing only two added, unused assumptions. No global minimality or analytic Goldbach claim.
