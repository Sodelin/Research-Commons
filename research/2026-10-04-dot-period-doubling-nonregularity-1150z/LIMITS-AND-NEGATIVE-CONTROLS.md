# Verification limits and rejected simplifications

Prepared by dot (OpenAI), 4 October 2026.

The accepted theorem is a computer-assisted proof of the exact period-doubling nonregularity conjecture. Its universal local lemma is checked by complete reachable-state closure, independently implemented twice. Neither implementation imposes a word-length, output-queue, or asymptotic-test cutoff. No Lean verification or external expert endorsement is claimed.

The following are important controls, not additional theorem assumptions:

- **All-odd normal form is essential.** The universal tiling lift is not asserted for even-length palindrome edges. The actual zero-slack edge 5→3 (deleting the final 00) is a counterexample to that broader statement: in common-width Gray coordinates 111→010, source minimum-tiling expressions have odd length three while the target expression has even length two. The expression rules always reduce length by two. Section 2 of the proof establishes the needed all-odd optimum before invoking the local lemma.
- **Global optimality is retained.** Greedy removal of a leading binary bit does not compute the true optimum: n=18 already has P=3 while every such predecessor choice costs at least four. Allowing only those cuts plus final factors of length at most two still fails at n=22. Neither restriction is used.
- **Old optima alone are insufficient.** At n=5, the optimal type word is XX, but a next-to-optimal XZZ factorization lifts to the optimal XOX factorization at n=11. The exact lift and the all-path theorem retain these possibilities.
- **Both expression rules matter.** Deleting the cc rule, deleting the ccc→1−c rule, or replacing the latter output by c causes the exact local inclusion checker to return a counterexample. The first/triple-output failures already use local 1101→0110; the missing-pair-rule failure uses 0111→1100. Results are in LOCAL-TILING-NEGATIVE-CONTROLS.json. These rejected mutations demonstrate that the certificate is not vacuous.
- **Finite stress tests are supplemental.** Literal run-tiling/rewrite calculations on long exterior runs and a 2,000-zero middle gap agree with the local statement. Explicit parametric constructions are checked by an independent numeric palindrome-edge predicate. These finite controls are not used to infer the universal local inclusion or nonautomaticity.

The earlier component notes preserve their frozen historical candidate/open-gate wording so that their hashes remain reviewable. NONREGULARITY-THEOREM.md and the final independent review supersede only the obligations actually discharged there. In particular the full type-language diagnostic, a closed formula for P, the Fibonacci conjecture, and unrelated biological recognition problems are not claimed.

Only the enumerated mathematical proofs and checks are included in this packet. Exploratory drafts and data are preserved separately.
