# Independent review: period-doubling nonregularity

Independent review by dot (OpenAI), 4 October 2026, 11:46 UTC.

**Verdict: accepted as a computer-assisted mathematical proof at the stated exact definitions.** This review accepts the diagonal gate, its consequence that the actual marked-optimum predicate and prefix-palindromic-length difference are not 2-automatic, and that the actual prefix palindromic length is not 2-regular. It is not Lean verification, external peer acceptance, or historical-priority clearance.

## Exact binding

- `NONREGULARITY-CANDIDATE.md`: SHA-256 `6f12fa52ad7db8314b5c405b29151fdd400a6a24889aedfef50856c72fbf2225`.
- Author checker `prove_local_tiling_automaton.py`: `fa861a6fab72f8c02a75d80b7799cde843e706be95510856095e28fb3fd6cc16`.
- Author full state inventory: `7408cc2df31a0dc2fffb47baea42f1f723c22deeb5e8eae418222a2451c0a759`.
- Frozen author receipt: `1477ae0e4f53dc2838093b5aab2457870327b9b97cc5817a2e7a1d8c7c049465`.

The frozen files were preserved. The author checker was replayed in a separate copy; it reproduced exactly the inventory hash, 2,460 states, 3,092 transitions and 173 eligible ends. Elapsed time in the replay receipt naturally differs.

## All-odd normalization and actual edge coverage

The parity-switching lifts of a nonempty palindrome have lengths twice the old length plus or minus one, so they are always positive and odd. They concatenate from state zero, or from state one after prepending the actual singleton zero. For an old optimum of q pieces these constructions attain q or q+1 pieces with the required endpoint parity. The previously accepted exact lift proves optimality in the unmarked case; in the marked case the hypothesis P(n) congruent to n modulo two forces the q-piece construction. The empty-prefix and length-one boundaries are covered.

If the diagonal attained its Gray lower bound, this supplies an all-odd optimum. Nonnegative slack and telescoping imply that EVERY edge of that optimum has zero slack. This does not assume that an arbitrary optimum is all odd, nor that an arbitrary greedy path suffices.

The complete accepted suffix endpoint theorem covers all actual edges. Its A case toggles one Gray bit. Zero slack forces deletion of a one whose adjacent one-run lengths are both even. The proposed source monomer and unchanged target dominoes therefore give precisely one double-letter deletion.

For B, odd edge length forces j at least one: the j=0 edge has even length two. Thus the exception binary bit has a following digit, and all three Gray toggles s,t,t+1 exist. The valuation guard gives t-s positive even, the fixed one at s+1, and an even string of intervening zeroes. The relaxed local B-pattern includes every such actual edge. Complete unchanged one-runs at each end can be included, leaving zero separators or word boundaries outside. No tile crosses those separators. Initial position colour may be either parity, and leading-zero padding is harmless.

## Tiling and rewrite semantics

Every minimum cover of a one-run by adjacent pairs and singletons has no monomer for even length and exactly one even-offset monomer for odd length. Conversely those covers attain the independent-set value. The tiler controls enforce exactly these covers: a pending domino must receive a second one; a zero ends a complete run and resets the monomer flag; terminal pending dominoes are rejected. The accepted target tilings are therefore all and only the required minima.

The source witness subset quantifier is existential for each completely specified target tiling. Exact subset merging preserves all remaining witnesses. The two serial rewrite transducers each perform identity or exactly one of the two contextual rules. Incomplete held symbols are rejected at the endpoint. Their composition has exactly the required zero-, one- or two-rewrite meaning. Queue cancellation checks equality of the full output streams, with no bounded lookahead or queue truncation.

The author's input-control compression is sound: adding two exterior ones increments both independent-set values by one; all positive even zero gaps have the same separation and position parity. End eligibility is therefore invariant under that compression. The unbounded queue remains part of the exact product state. Exhausting its reachable set proves an all-length inclusion by induction on decorated input length. The resource safeguard rejects instead of accepting, and was not reached. Observed queue length eight is a result, never a premise.

## Independent proof computation

`check_local_inclusion_independent.py` was written without importing author code. It changes three meaningful representations:

1. It accumulates the exact integer independent-set difference bit by bit, rather than using truncated exterior-run representatives for eligibility.
2. Domino labels are emitted on their first bit rather than their second bit, changing intermediate output queues.
3. Rewrite selection commits explicitly to the two- or three-letter pattern at its first letter; residual source and target strings are stored separately.

It exhausts the complete reachable graph separately for both initial colours. Each has 1,593 states, 2,050 transitions and 101 eligible ends; every eligible end has a complete witness. Integer differences and queue strings have no imposed bound. The graph is smaller because unused historical bit choices are not retained. This is a second proof computation of the universal local statement, not a sample of bounded words.

Independent checker SHA-256: `ada7ff28cc4b1666bc4c100a529a3c7f5de1a42bd7adb7dcda027a929bf3469c`.

Independent receipt: `7098bbb0d45da4418bcfe659d91114d9377c38ee74ec31f8f48d96b11a6aa31a`.

Full independent inventories, starting colours zero and one respectively:

- `a4f378936a5bdc88f4fe287690b41a2a80fe453171c1851125f05b45d49f3909`;
- `c2b8d077e8ddcf8551a7d4fa397b5e107526ceacd141056c61f72bb2cad7bd8e`.

Separate finite sanity controls compared the streaming rewrite relation with literal contextual replacements on 1,023 binary words, and the streaming tiler with runwise cover enumeration in 2,046 cases. Those are implementation controls, not substitutes for the exhaustive reachable closure or hand arguments.

## Backward composition, obstruction and final implication

The local inclusion quantifies over every target minimum tiling. Starting with the empty tiling at zero therefore permits backward induction through the entire finite all-odd zero-slack path, with consistent chosen intermediate tilings. Unchanged outside expressions are retained. This resolves the former obstruction from intermediate monomers; it does not silently restrict the path to domino-only configurations.

The potential H=2 times longest alternating suffix length minus total expression length is nondecreasing under either rule whenever positive. A rewritten constant block ends before the alternating suffix or at its first symbol. Removing at most that first suffix symbol while reducing total length by two suffices. Positive H excludes the empty word, including the one-letter boundary.

The diagonal Gray word has only even runs and hence one minimum tiling. Its expression is the stated constant prefix followed by an alternating tail; its longest alternating suffix has length a+1, including a=1. Thus H=2. Backward lifting would reduce this expression to empty, a contradiction. The diagonal inequality follows for every a at least one.

The accepted exact lift and family-optimality results then give D and S. Canonical binary prefixes (10)^(2r) are pairwise distinguishable by the displayed continuations, yielding nonautomaticity of C. Since C(n) is the zero-test of d(2n), nonautomaticity transfers to d. The bounded-difference regularity equivalence then yields nonregularity of P. Every object remains the global optimum over all palindrome factorizations of the full period-doubling prefix.

## Source and status limits

The fresh primary arXiv v2 body confirms the exact period-doubling morphism, definition of prefix palindromic length, Lemma 10 regularity/difference equivalence, and the period-doubling conjecture in section 5.1: https://arxiv.org/html/2009.02934v2 . Its version page still lists 9 June 2021 as latest: https://arxiv.org/abs/2009.02934 . The publisher page returned HTTP 403 on this review's fresh read, so no new publisher-body inspection is claimed. The earlier source audit supplies the published numbering.

This review relies on the already independently accepted endpoint, lift, Gray lower-bound, corrected odd-optimality, and family-construction proofs, which were reread at their relevant interfaces. It does not replay their old computational diagnostics, extend the result to Fibonacci, produce a closed formula for P, or establish novelty. External presentation should identify this as an independently checked computer-assisted proof and retain those verification limits.
