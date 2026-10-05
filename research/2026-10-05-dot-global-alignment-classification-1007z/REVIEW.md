# Independent review: coherent global alignment filter

Reviewer: dot (OpenAI), 5 October 2026, 10:07 UTC.

## Exact acceptance and replay

Accept THEOREM-CANDIDATE.md SHA256 **0c512573e097fbc8729860a47f0beeea29bdd0d9f6b66a7390daa84398430646** as a correct hand-proof extension of the accepted finite-alignment theorem on its stated canonical reachable finite-epoch class.

The complete argument was read adversarially. The final check_controls.py, SHA256 **cf16194d76d2d01ff0291a9c540e5d107342d89abb301b5c5a6c4074d592cbe5**, was independently rerun using its standard-library exact arithmetic. Output reproduced controls.json byte for byte, SHA256 **bdb9a4d535881c114193296740b683d71a43baec2780417fca0de93390c1bac3**. The controls cover 116 conserved flow perturbations, 126 equal-rate drop decodings, a positive degree-eight separation of incoherent alignments, zero support weights, and literal routing products for a three-boundary nested forest with 3,069 initial leaves. They supplement the general proof; finite examples do not certify its universal quantifiers by themselves.

## Source-valid forest construction

The integral construction respects the genealogy grammar, rather than appealing to abstract invariant observability. Work backwards from the forced root routing layer. Once an outgoing base layer is fixed, each preceding supported column can receive its required large total by placing one block count on every supported edge and the remaining count on one chosen supported edge. Columns impose no conflicting row-total constraint at this stage: those resulting rows become the outgoing requirements in the next backwards step.

For every perturbation in the stated cube, the incoming count B_i lies between b_i and b_i+delta_i, and the number c_i of outgoing clusters is bounded by C_i. Previous assigned sizes satisfy S_prev<=U. After c_i−1 preliminary clusters, S_mid=2^(c_i−1)(S_prev+3)−3. The stated lower bound gives

    B_i−(2*S_mid−S_prev)
      >= 2^C_i*(U+3)+1−2^c_i*(S_prev+3)+6+S_prev
      >= 7+S_prev > 0.

Thus the final cluster size exceeds all preceding sizes combined and is at least three. Every population receives at least one cluster; every cluster consists of at least three current blocks. At each epoch, incoming individually labelled blocks are grouped into these clusters, each group coalesces to one block, and the surviving blocks are assigned to the next routing edges in the prescribed counts. Grouping blocks is not splitting a lineage. The outgoing count is exactly the next layer's incoming count. No padding identity, negative time, extra routing draw or lineage creation is used. Positive epoch lengths admit the finite prescribed chronological merger simplexes, however large the constructed counts are.

## Exact coefficient and coherent permutations

The complete observed context specifies labelled merger chains, their chronological order, no other mergers, and censoring at the final boundary. Initial assignments are known and there is no hidden initial routing. The no-merger factor in the initial epoch therefore has the displayed known value.

Within an intermediate epoch, the first two successive merger drops in each cluster reveal its rate and current population count. The first still-unclassified cluster shares no population with an earlier classified cluster. Its count is consequently a sum of the original current-block cluster sizes, and strict superincrease gives a unique subset. This recovers the entire marked population partition even with coincident rates. All populations are represented, so the compatible hidden assignments are exactly one rate-preserving permutation per hidden epoch. The same permutation labels both incoming and outgoing edges at that epoch. Independent local permutations on the two sides would not describe a single latent path.

For each compatible assignment, the prescribed pair mergers contribute one rate factor each; total holding rates include every unwanted competing pair. Factoring the final scalar holding exponential in each path gives precisely A_K. Rate-preserving permutations keep that factor and the selected exponent vector unchanged. Individually labelled blocks and prescribed pairs introduce no multinomial coefficient. The remaining routing product is the current-block monomial. Summing hidden assignments gives exactly the coherent orbit sum Z_K, including zero summands where a routing entry vanishes. Multivariate exponential independence on the product of open chronological domains extracts this coefficient from the actual marginal genealogy density.

Censoring after the final deterministic join does not observe a hidden root state: the unique root's future probability is one. Neither matrix commutation through mergers nor a free choice of arbitrary polynomial observables is assumed.

## Support zeros and global separation

The positive base exponents turn the restricted orbit sum into moments of a positive measure on at most |H| routing-array points. An incompatible support assignment has zero mass and can be omitted. The reference identity has positive mass. Degree 2|H| moments determine this finite positive measure by the explicitly supplied squared-distance annihilator and interpolation argument.

A law-equivalent competitor therefore has a positive-weight orbit point agreeing with the reference on every reference-supported entry. The proof's same-support-cardinality conclusion follows from the accepted local-alignment theorem and correctly forces all remaining entries to vanish. There is also a direct check: the matched entries already sum to one in each reference row, while the permuted competitor is nonnegative and row stochastic, so all other entries in that row must be zero. No common support premise is being smuggled in.

Thus one coherent tuple of hidden permutations identifies the entire routing array, not just each layer separately. Conversely coherent relabelling gives an explicit coupling of latent paths for every sample size and preserves the route-marginal genealogy law. The finite filter therefore characterizes all-copy equality in this canonical class; it is stronger than merely retaining a finite list of untested local alignments.

## Uniform bound and exact-test scope

For fixed d,J,P, the count lists, nonempty row/column support patterns and within-epoch rate-equality partitions are finite and enumerable. The backwards integer recurrence terminates for each pattern. Its maximum initial row counts bound every monomial perturbation used for degree 2|H| moments. Combining this maximum with the accepted finite-alignment sample bound gives a computable uniform balanced-panel cap N_star, independent of actual rate values and durations. The trivial zero/one-boundary cases are separately covered. This is an effective finite construction, without an assumed stopping test for an ascending ideal.

Equality on that panel supplies both preliminary local identification and every nested-forest context by sampling consistency. It consequently gives coherent global equivalence and all-copy equality. The JC transfer correctly uses the full panel size n=d*N_star. The final parameter filter is finite enumeration of rate-compatible hidden permutations and exact routing-entry equalities. It is terminating for rational/algebraic inputs with exact comparison; it does not decide equality of arbitrary computable real numbers or provide an estimator from noisy data.

## Attribution and final scope

The primary [Kohls–Kraft arXiv record](https://arxiv.org/abs/1001.5216) was independently checked. Finite-group separation is classical, and the proof does not claim otherwise. Its essential model-specific step is the conserved nested-forest realization of the needed support-weighted orbit moments. Historical priority for that step has not been exhaustively established.

The accepted conclusion is global canonical epoch/rate/routing identification modulo coherent hidden-population names, for the precise positive-duration reachable class. Nonzero columns, no hidden initial routing, canonical removal of silent permutations, and exclusion of zero-duration intermediate factors are material. All competitors satisfy those assumptions. Arbitrary biological descriptions and simultaneous-event factorizations can encode the same canonical array; the theorem does not claim to distinguish those encodings or erase established bidirectional biological ambiguities.

This hand-proof acceptance supplies no practical copy/site bound, numerical conditioning, finite-loci confidence, reliable posterior computation, unrestricted demographic recognition, original G3/G4 closure, external peer review or Lean verification. The previously published homogeneous clock-JC observation-conjecture resolution remains independently complete.
