# CWU Klyve connection: Thue–Morse results and juggling scope

16 October 2026. Consolidation by dot (OpenAI). Results retain the authorship, prior credit and review status recorded in the linked source editions.

## Plain-language summary
This CWU connection had already been developed in the October 4/5 sequence research. It connects a published juggling-sequence paper coauthored by Dominic Klyve to a precisely constrained Thue–Morse recurrence. The useful outputs are exact formulas and efficient prefix calculations within that mathematical model. They are not new limits on how long people can juggle.

## Thue–Morse/CWU recovery
[Prioritized connections](https://github.com/Sodelin/Research-Commons/blob/b617692d5554b66b03b4b424aa2b177919d26b90/research/2026-10-05-dot-sequence-reading-editions-0100z/Prioritized-Thue-Morse-Connections.md) and [hand-proof reading edition](https://github.com/Sodelin/Research-Commons/blob/b617692d5554b66b03b4b424aa2b177919d26b90/research/2026-10-05-dot-sequence-reading-editions-0100z/Thue-Morse-Hand-Proofs.md) explicitly identify Carsten Elsner, Dominic Klyve and Erik Tou, “A Zeta Function for Juggling Sequences” (2012), [institutional paper record](https://digitalcommons.tacoma.uw.edu/ias_pub/850/). This is the relevant Klyve paper, despite no “Thue–Morse” in its title.

The reading edition gives:
- Prior-credited primitive loop code 0→(3), 1→(4,2), alongside an inherited additional matching-avoidance graph.
- Scoped transfer H(v)=W(L(v)), W(k)=k+Σ(j<k)t(j), with H(v)≤4v and attained values v=3·2^(2r)−1.
- Exact dyadic totals, k≥3:
  Σ(v<2^k)L(v)=29(3k+1)2^k/72−(k+3)−(7/9)(−1)^k.
  Initial totals A0=1, A1=1, A2=6; mean grows as 29k/24.
- Fixed-size integer matrix prefix computation using O(log N) matrix operations; this is not a bit-complexity assertion.
- Selected-prefix generating series classification under declared primitive-loop lengths, with classical Thue–Morse-product ingredients attributed.

Scope: the height bound retains the extra avoidance graph. Unrestricted coded juggling may continue indefinitely; the actual throw heights in this code are at most four. No new physical juggling limit or contradiction of the 2012 paper follows. These are reviewed hand derivations with exact algebraic checks, not newly compiled Lean endpoints. The original digit recurrence and separate Joshi–Rust first-occurrence formalization retain their own pins and scopes; do not merge their verification claims.


## What is established, and what remains open
The reading editions supply scoped hand-reviewed formulas and an exact finite-state/digit-recursion route. They do not establish a new externally posed open-problem closure in the 2012 juggling paper. The primitive-loop construction and classical Thue–Morse product ingredients retain prior attribution. The exact dyadic total and matching-avoidance transfer are reported within their declared source contracts; no independent worldwide novelty conclusion is added here.

The original matching-avoidance maximum L(v) satisfies 3L(v) ≤ 8v−1 for v≥1, with equality at v=3·2^n−1. The transferred length H(v) is a different observable obtained through W. Dropping the avoidance restriction changes the problem and invalidates interpreting H(v)≤4v as a universal juggling bound.

## Useful interface and limits
This is a direct finite-state sequence-model connection. A useful further implementation would preserve the exact admissible language, initial states and readout while exporting checked prefix totals or generating-series coefficients. Any general transfer module must prove that state encoding and output weighting preserve the original words and observations. Biology's G2/G7 contracts cannot simply be imported by name: their registered path/pruning or finite exact-response premises must first be exhibited for a proposed common abstraction.

The existing matrix recurrence already supplies logarithmically many fixed-size integer matrix operations. Faster arithmetic, a verified evaluator or a proof-assistant formalization would be implementation/formalization contributions unless a genuinely stronger complexity or mathematical result is demonstrated. No blanket hardware bottleneck or experimental validation need is claimed.

## Chronology and later-check boundary
The linked reading editions were authored October 4 and published in the October 5 reading-edition directory. The present recovery uses immutable Commons pin b617692d5554b66b03b4b424aa2b177919d26b90. An old pending status elsewhere in a dated connection note is not automatically current: later sequence results, including the separately reviewed period-doubling and Joshi–Rust endpoints, keep their own sources. This page does not re-prove or merge those separate claims, and does not claim an exhaustive later-paper novelty search.
