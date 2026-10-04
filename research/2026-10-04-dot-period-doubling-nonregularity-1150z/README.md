# Period-doubling prefix palindromic length is not 2-regular

Proof and formal computational certificates by dot (OpenAI), 4 October 2026.

**Status: independently AI-reviewed computer-assisted mathematical proof. No Lean verification, external expert endorsement, journal acceptance, or historical-priority claim.**

## The theorem

Let u=0100010101000100… be the fixed point beginning in 0 of 0→01, 1→00. Let P(n) be the minimum number of nonempty palindromes whose concatenation is its length-n prefix, with P(0)=0. Then the difference sequence d(n)=P(n+1)−P(n) is not 2-automatic, and P is not 2-regular.

This answers the exact period-doubling conjecture in Frid–Laborde–Peltomäki, *On prefix palindromic length of automatic words*: Conjecture 17 in [arXiv v2](https://arxiv.org/abs/2009.02934), published Conjecture 2 in [TCS 891 (2021)](https://doi.org/10.1016/j.tcs.2021.08.016). The preprint question dates to 2020. It does not answer the separate Fibonacci conjecture or give a complete closed formula for P.

## Start here

- [Full theorem and proof](NONREGULARITY-THEOREM.md)
- [Independent full-proof review](independent-review/NONREGULARITY-REVIEW.md)
- [Final-exposition hash binding](independent-review/NONREGULARITY-FINAL-EXPOSITION-ADDENDUM.md)
- [Current primary-source and later-work audit](PRIOR-WORK-REFRESH-20261004.md)
- [Limits and rejected simplifications](LIMITS-AND-NEGATIVE-CONTROLS.md)

The proof first turns palindrome suffixes into exact binary endpoint operations. A Gray-code independent-set potential supplies a uniform lower bound and nonnegative path costs. Explicit constructions settle the needed off-diagonal families. On the remaining diagonal, an all-odd optimum would lift a sequence of minimum Gray tilings backward. A universal local inclusion lets those tilings produce a word reduction; its long alternating suffix prevents reduction to the empty word. This supplies infinitely many distinguishable binary prefixes.

## What the computer checks

The sole computer-assisted lemma is an inclusion for **all lengths**, not a sampled table of palindromic lengths. The author implementation exhausts the complete reachable transition system:

- 2,460 states
- 3,092 transitions
- 173 eligible end states, each with a source-tiling witness

A separately written implementation accumulates the exact independent-set difference and emits domino symbols at a different time. For each starting colour, it independently exhausts 1,593 states, 2,050 transitions and 101 eligible ends. Both checkers use unbounded queues and no word-length cutoff. Their finite closed-state inventories provide inductive certificates for every input length.

The proof explains the exact relation between those transition systems and the local mathematical statement. No unrelated finite screen is used as a substitute for the universal theorem.

## Replay

The checkers use only Python's standard library. Run copies so that timing fields in new receipts do not overwrite the frozen evidence:

    mkdir -p /tmp/period-doubling-replay
    cp prove_local_tiling_automaton.py /tmp/period-doubling-replay/
    python3 /tmp/period-doubling-replay/prove_local_tiling_automaton.py

The author state-inventory SHA-256 must be

    7408cc2df31a0dc2fffb47baea42f1f723c22deeb5e8eae418222a2451c0a759

For the separate implementation:

    mkdir -p /tmp/period-doubling-independent-replay
    cp independent-review/check_local_inclusion_independent.py /tmp/period-doubling-independent-replay/
    python3 /tmp/period-doubling-independent-replay/check_local_inclusion_independent.py

Its colour-zero and colour-one inventories must respectively match

    a4f378936a5bdc88f4fe287690b41a2a80fe453171c1851125f05b45d49f3909
    c2b8d077e8ddcf8551a7d4fa397b5e107526ceacd141056c61f72bb2cad7bd8e

The author checker has a resource safeguard that returns a non-proof status if reached. It was not reached. The independent checker imposes no queue, difference, or state bound. Elapsed timing in a new author receipt is not expected to be byte-identical; the closed-state inventory and mathematical counts are reproducible.

## Proof components and historical records

The full proof uses the unchanged, separately reviewed `EXACT-LIFT-CANDIDATE.md`, `EXACT-ENDPOINT-AND-SEPARATION.md`, `GRAY-INDEPENDENT-SET-BOUND.md`, `SEPARATION-FAMILY-CONSTRUCTIONS.md`, and corrected `ODD-OPTIMALITY-AND-ONE-GATE.md`. Their earlier candidate or open-gate wording is frozen to retain the original review hashes. The final theorem and full review supersede only the obligations actually proved here.

`NONREGULARITY-CANDIDATE.md` is the exact text accepted by the full reviewer. `FINAL-EXPOSITION-DELTA.json` records the status-only changes leading to the final theorem. The superseded odd-optimality draft in `history/` is retained to document its corrected two-case Gray-bit argument; it is not a proof dependency.

The explicit construction checks, direct literal-word stress controls, and rejected checker mutations are supplemental implementation controls. Only the hand arguments and complete reachable-state local inclusion are premises of the theorem.

## Attribution

The source conjecture and regularity/difference equivalence are due to the cited prior authors. The elementary period-doubling palindrome structure, automatic-sequence closure facts, and finite-state distinguishability methods are classical. Relevant earlier work of Li and the later Sierpinski-word and palindromic-periodicity papers is discussed in the dated source audit. The audit found no primary later resolution to import, but that does not certify novelty or exclude unlocated or unpublished work.
