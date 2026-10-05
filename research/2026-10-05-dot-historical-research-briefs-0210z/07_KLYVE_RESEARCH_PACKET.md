# AI handoff for discrete mathematics review

For possible review by Professor Dominic Klyve

AI-generated research handoff prepared by dot (OpenAI)  
4 October 2026 · Discussion draft · No external endorsement implied

## Review request

This packet requests critique of one combinatorial statement, its proof record and prior-work status. AI systems contributed central arguments, code and Lean proofs. Linked sources retain their attribution; outside expert review is requested.

## Why this may be a useful mathematical conversation

[Storm and Klyve’s 2014 paper on graph-theoretic definitions of the Ihara zeta function](https://digitalcommons.cwu.edu/math/19/) unifies equivalent definitions and examines a formulation useful for calculations and proofs. That provides a methodological connection through precise graph definitions. The title’s word “formal” does not establish Lean proof-assistant specialization.

[Elsner, Klyve and Tou’s zeta function for juggling sequences](https://digitalcommons.tacoma.uw.edu/ias_pub/850/) offers a discrete-sequence connection, but no transfer to Thue-Morse matching heights is established. Current interest is unknown.

## One result that can be examined in isolation

Let t(n) be the parity of the number of ones in the binary expansion of n. For every w at least 2, a directed graph has an edge from w−1 to w labelled t(w), and one from w−2 to w labelled 1−t(w). There is no edge from 0 to 1. A matching path uses label t(k) on its kth edge, starting at k=0.

Let L(v) be the maximum matching-path length from the natural-number vertex v. The development gives an attained maximum at every start, a complete piecewise formula and a certified ten-coordinate integer recurrence that evaluates the same maximum from binary digits. In particular:

- L(0) = 1.
- For v at least 1, 3L(v) ≤ 8v−1.
- Equality holds exactly when v = 3·2^n−1 for a natural number n, with L(v) = 8·2^n−3.
- The leading coefficient 8/3 cannot be lowered even after allowing a fixed additive constant.

The claim concerns actual paths and proves both attainment and the upper bound. A finite scan or fitted recurrence is not its proof. Minimality of the ten-coordinate representation is not claimed. [Complete proof note](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/19544a4d/notes/FULL-HEIGHT-PROOF.md)

## Provenance and what the certificate establishes

The graph comes from a separate September 2026 classification manuscript by avg-netizen. That manuscript’s quantitative question is the target of this follow-up. Samuel A. Alexander’s earlier work supplies the original biological-unavoidability context. This project does not claim to have originated the classification or to have established worldwide priority for the quantitative result. [Pinned source manuscript](https://github.com/avg-netizen/biological-unavoidability/blob/3d6175e3e23f67bd68e7be591b5a9a6d04e496a3/paper.md)

The theorem FullHeight.height_isMaximum connects the formula to actual matching paths; height_formula and height_closed_form cover every natural starting vertex. DigitRecurrence provides the separate verified evaluator. The pinned proof checkpoint has a successful hosted Verify run. Its allowed standard axioms are propext, Classical.choice and Quot.sound. [Lean proof](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/19544a4d/lean/SamuelAlexanderResearch/FullHeight.lean) · [Digit recurrence](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/19544a4d/lean/SamuelAlexanderResearch/DigitRecurrence.lean) · [Hosted verification](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/actions/runs/36116271138)

The VibeMathed entry remains Candidate, review pending, with verification labelled Lean-checked, statement unaudited. The site reviewed the recorded checkpoint and endpoint descriptions but did not rebuild it or obtain an independent human statement audit. That is why a short external correspondence and prior-work review would matter. [Public record](https://vibemathed.com/problem/exact-thue-morse-matching-heights-in-an-avoiding-population)

## The wider project is still in progress

The broader ancestry-network programme has a public 825-source combined Lean checkpoint. Another 127 reviewed modules are public and sixteen further modules are reviewed locally; the combined 968-source build receipt is pending at this draft date. These counts are separate from the historical checkpoint above.

The full historical master Lean programme and practical solver remain unfinished. Some hand characterizations lack complete formal assemblies. Kernel checking, statement fidelity, prior work and usefulness remain separate questions.

## Questions for external critique

1. Does the matching-height statement suggest a known automatic-sequence or combinatorial framework that should be cited or compared?
2. Is there a clearer theorem presentation or independent small check that would help a mathematician assess the actual-path/formula correspondence?
3. Would this focused result make a sensible short note, or is there another route or colleague you would recommend before developing it further?

The evidence index follows, preserving original attribution, assumptions and dated verification boundaries.
