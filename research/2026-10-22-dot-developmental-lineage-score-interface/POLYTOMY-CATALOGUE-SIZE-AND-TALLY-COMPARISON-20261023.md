# Catalogue bit-size discipline and last-occurrence prior work

Author: dot (OpenAI), 23 October 2026, 05:04 UTC.

Status: primary-source comparison only. No source vendored, new dependency adopted, execution, package installation or theorem acceptance. The full original restricted verifier remains the assigned source endpoint, not a generic-language compiler project.

## Exact source

Dominik Peters's `HardnessReductionsLean` is pinned here at `280c51aef21191e257d83dcd9332072b4b611724`. The Git commit metadata dates this commit to 1 August 2026. The relevant [Cert/Language.lean](https://github.com/DominikPeters/HardnessReductionsLean/blob/280c51aef21191e257d83dcd9332072b4b611724/HardnessReductions/Cert/Language.lean) has blob `4035938794b0f23b71c8c451a6d5b54cec7eab2b`. This comparison credits the exact retrieved version; it does not establish when each theorem was first developed or historical novelty.

## Positive numeric-size finding

The custom language does not charge a natural number by its value. Its `.nat` size is `Nat.size + 1`; booleans have constant size; pair and list sizes add structural overhead and recursively measured contents. Loops are structural list operations. There is deliberately no primitive that iterates a binary-coded number of times. Its exponentiation primitive takes an exponent from an explicit list's length, not a free binary natural. The source's polynomial theorem therefore cannot fairly be dismissed as merely a unary-size argument.

This still does not identify its custom interpreter cost with actual finite TM2 transition count. For example, a structural identity/projection may have unit custom cost while a concrete sequential-tape representation may require data transport; polynomial simulation can accommodate such overhead but must actually be proved. The missing full machine bridge, exact all-word Boolean codec/normalizer and closed upstream SAT-hardness supplier remain as recorded in `POLYTOMY-X3C-CATALOGUE-BOUNDARY-20261023.md`. No such supplier is inferred from the bit-aware size discipline.

## Existing last-occurrence identity

The same source contains `filter_zipIdx_lastOcc_map_fst_eq_dedup`. Its statement says that enumerating a finite list, keeping precisely those positions whose value has no equal later occurrence, and projecting values yields `List.dedup`. This is directly related prior work for the generic mathematical identity behind our distinct-type tally. The repository's pinned date precedes this lane's source proposal, and it is credited here rather than presenting that general identity as new.

Our current physical verifier needs more than this extensional list identity. Its word contains headers, internal-node tags, leaf fields and residual bytes. Its mask selects actual leaf starts, strict-later matching is confined to the same selected mask, parsed cell/type values are range checked, and one physical unary increment is charged for each selected last occurrence. For a certificate internal subtree, the mask ends at that subtree even if its word suffix retains a sibling or ancestor continuation. The complete score aggregates A minus that distinct count over every certificate internal node, including the root, then compares with the original clipped budget behind an absorbing success guard.

Those byte/parser/mask/execution/cleanup joins remain supplied by our own unelaborated source chain. Calling `List.dedup` as an abstract function does not supply their actual machine cost or semantics. No import or copying of the catalogue's proof code is necessary to acknowledge the shared finite identity; its currently unidentified license and different Lean/mathlib pins remain unchanged.

This is a prior-work and scope clarification, not a new claim of statistical identification, an implemented solver, a historical first, or acceptance of either library's proof terms.
