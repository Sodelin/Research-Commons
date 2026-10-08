# Root source review: calendar-context PMF closure

Observation: 2026-10-08 00:39 UTC. SOURCE ACCEPTED; compiler verification pending. Root inspected the exact candidate and diff at `4027755be7875201b905859ca2db2631703b4154` after the actual failure in [run 377055](verification/evidence/g6-run-37705599767-FAILED/README.md).

Candidate SHA256: `3694d292bc754e48c07a8dc32a62783eb2534b9bc80016c71b427bf835d742d7`. Diff SHA256: `aba567e7ed01afb59497cce4ca6cf08a24d43021032ab9862d9b96a313fbc6d0`. Root authenticated the candidate bytes and inspected the complete changed closing proof and adjoining theorem/axiom region. The source and statements before the changed proof remain byte-identical.

The derivative replaces two fragile rewrites by transitivity of the same already-proved PMF bind equalities, old forward and new backward. Remaining applications type the same interval constructor explicitly as `ProgramStep N`. It changes no theorem statement, source law, bank, readout, callback or assumption. There is no new desired-law premise or unchecked cast.

Gate: the sole owner may freeze one successor with the same 165 commands and 358 requested reports, retaining all 161 previously successful modules and the other 164 source hashes. Finite-cut preflight and molecular applications remain outside that input. This review executes no Lean and promotes no declaration. The actual accepted frontier remains 161 modules / 313 reports / 3,912 declarations / 2,547 theorems until new terminal evidence and audit establish otherwise.
