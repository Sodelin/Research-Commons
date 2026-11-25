# Assumption feedback without reading Lean

From this directory: `python assumption_relay.py assumptions-fixture.json`.

The relay kernel-checks the original conditional implication, removes every zero-weight premise from the supplied linear certificate, and kernel-checks a genuinely smaller theorem. It checks that the reported variable list and conclusion have stayed identical, then emits the old and new assumptions, axiom reports, and the reusable reduced certificate. This is deletion justified by the explicit certificate, not a claim that all remaining premises are necessary. With no zero weights the report says this method found none; a different proof may still use fewer. No arbitrary prose conversion, general hypothesis search, or Google Drive event wiring is asserted.

The worked example encodes integer budget arithmetic. It removes the two added nonnegativity assumptions for the charges (premises 4 and 5), while keeping the three actual budget bounds and exactly the same 187 conclusion. This is not a new analytic Goldbach estimate or a claim that an original research proof depended on the two demonstration premises. Both theorem receipts are kernel-checked using Lean 4.33.1 and list only propext and Quot.sound.

Next: use one pinned source statement and named premises, add a bounded leave-one-out proof search for used premises, and verify any replacement without the removed premise. Queue immutable source/candidate/receipt records privately in Drive; never execute a raw program from a mailbox item. Keep public code and private input permissions independent. Report a failed search as inconclusive, not as necessity.
