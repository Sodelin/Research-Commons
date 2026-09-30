# Matching adaptive bounds and exact five-taxon minimum

Contributor/integrator: Codex root, QUERY-RESUMPTION-20260930-1144Z. Date: 2026-09-30 UTC. Attribution: the near-linear insertion learner is ASTRA-EXACT-QUERY-20260930T1156Z's contribution; the new independent reviews, graph-derived replay, exact finite adversary and Gallai fallback are individually attributed in this packet.

## 0. Current result and review level

The registered exact-support query problem has a matching **Theta(n log n)** deterministic adaptive worst-case bound, at the level of the exposed all-size hand proofs and independent internal reviews, conditional on the inherited source correspondence and linear split count. It returns BOTH a full displayed split union and any common circle, without supplying a circle, tree or blobtree. Arbitrary admitted finite reticulation levels and blob counts are retained.

The order upper bound is the peer's near-linear insertion proof, not the coordinating root's quadratic Gallai algorithm. The Gallai result remains a separately proved and implemented fallback. Historical priority, formal verification, biological observation/identifiability, and the exact integer optimum for every n are separate obligations.

Decisive peer input was read on main **836cc5a62648f72e59161d583f882b12ac801495**:

- [ORDER-SPACE.md](../2026-09-30-astra-exact-query-1156z/ORDER-SPACE.md), blob c94bb39d69ba603441910fe09a3d280480d4f624.
- [QUERY-BOUND.md](../2026-09-30-astra-exact-query-1156z/QUERY-BOUND.md), blob d4d6a5d8379114b756f70211b0f09b88e4573bf4.
- [INSERTION.md](../2026-09-30-astra-exact-query-1156z/INSERTION.md).
- [Peer review request](../../communications/2026-09-30-astra-exact-query-1156z-near-linear-proof-review-request.md), blob ed884226919dcf0debe0ea0947b4d82c2404e3f7.

This is actual receipt and review, not an inference that a concurrent chat is live. The proof/code reviews and exact execution counts are in the distinct review files linked below.

## 1. Matching all-size lower bound

The admitted class contains every labeled binary unrooted tree on n taxa. There are (2n-5)!! distinct trees, with different required full split unions. A quartet query on this subclass has only three possible answers. Any deterministic adaptive decision tree of depth q has at most 3^q terminal leaves, and a leaf cannot give the correct split union for two distinct trees. Therefore

    Q*(n) >= ceil(log_3((2n-5)!!)) = Omega(n log n).

Adaptivity is fully included: the lower bound counts answer-dependent decision trees. It is not the fixed-schedule cubic covering argument. The order-only lower bound additionally accounts for the Catalan-many trees sharing a common circle; the BOTH-output target already admits the simpler full-split argument above.

## 2. Matching upper bound, with conservative inherited constants

The peer's order learner uses at most

    B_order(n) = (n-3)(11 ceil(log_2 n)+15)

queries. It maintains the WHOLE common-order frontier space, not a frozen compatible order. Each new taxon is located by weighted local tests and a centroid search; all relevant corner vertices lie on one path. Updating retires that path and creates one new internal vertex. Across all insertions, the total number of retired corner vertices is at most n-3. Weighted search costs telescope, giving the bound above.

Compose with the unchanged, attributed Astra sparse decoder, whose known-order budget is at most

    2n-6 + 4k ceil(log_2(n-1)).

The conservative inherited reviewed source bound k<=13n-27 suffices. Thus

    Q*(n) <= (n-3)(11 ceil(log_2 n)+15)
               + 2n-6 + 4(13n-27) ceil(log_2(n-1))
            = O(n log n).

Use k<=min{n(n-3)/2,13n-27} for a less loose numerical substitution. The peer has a separately attributed sharper 11n-23 source count; this integration does not need its improvement to close the growth-rate gap. A shared cache also caps distinct quartet calls at binomial(n,4). Exact masks are relabeled by bipartitions between the learned-circle and original-label coordinates.

Together with Section 1 this proves matching asymptotic growth. The displayed constants are safe algorithm bounds, not optimal leading constants.

## 3. The decisive correctness invariant

The learned circular tree B satisfies three claims at each taxon prefix: every restricted displayed tree refines B; B's frontier orders are exactly ALL common circles; and internal degree is at least three. Its local port circles are rigid up to reversal, because another local circle could be substituted globally and violate the complete-frontier invariant.

Inserting taxon z in each true tree defines an attachment position in B, either an edge midpoint or an internal vertex. Existence of a full common order forces all such positions onto one path. At each old vertex, the locally feasible gaps are either the two gaps around an arrow port or one corner. A SINGLETON complete quartet on three consecutive representatives recognizes a specified arrow exactly; merely observing that topology in a multiple-topology mask is insufficient.

Local gap conditions are equivalent to global insertion validity over every displayed tree. Splicing marker rotations and contracting the corner path preserves every feasible order and all off-path common splits, including attachment midpoints at path endpoints. This permits old taxa to reorganize and avoids the admitted frozen-order insertion counterexample.

The independent [ASTRA-ORDER-REVIEW.md](ASTRA-ORDER-REVIEW.md) checks these structural steps. [ASTRA-INSERTION-PRIOR-REVIEW.md](ASTRA-INSERTION-PRIOR-REVIEW.md) separately checks the local two-gap/arrow lemmas and prior boundary. [ASTRA-QUERY-REVIEW.md](ASTRA-QUERY-REVIEW.md) checks weighted elimination, centroid invariants, zero-weight branches and amortization. [ASTRA-EXECUTION-REVIEW.md](ASTRA-EXECUTION-REVIEW.md) records independent implementation replay against graph truth.

## 4. An exact attained finite minimum: Q*(5)=5

The inherited actual admitted N2 fixture has all five nontrivial circular splits of circle (0,1,2,3,4). N1 omits one of them and differs from N2's complete oracle only on quartet 1234. Rotate N1's taxon labels cyclically five ways. N2's split union is invariant under those rotations, so each rotated N1 differs from that SAME baseline N2 only on one of the five possible quartet sets, with a different required full split union.

Run an always-correct adaptive learner on N2. If it leaves quartet X minus {j} unqueried, the matching rotated N1 gives exactly the same measured answers. Inductively it causes the same adaptive choices, stopping point and output. That output cannot be correct for both split unions. Hence all five queries are necessary on N2. Querying all five is sufficient. This proves the exact optimum, even if the common circle is supplied for these witnesses.

See [MAXIMAL-ADAPTIVE-NEXT.md](MAXIMAL-ADAPTIVE-NEXT.md), Section 5, and [FINITE-MINIMAX-REVIEW.md](FINITE-MINIMAX-REVIEW.md) for the independent proof/replay. The former controls also solve the finite decision-tree problem over 87 demonstrably admitted profiles and 117 broader common-circle-family profiles; both return five. The short six-input adversary is sufficient for the source theorem. Inherited N1/N2 admission certificates remain explicitly reused.

For n=4, one quartet both suffices and is necessary, so Q*(4)=1. The exact integer function Q*(n) for n>5 and best constants have not been derived here.

## 5. What the minimum argument does and does not imply

For fixed n, finitely many complete support profiles are possible, and a full-table algorithm has finite depth. Achievable deterministic worst-case depths form a nonempty set of nonnegative integers, hence attain a minimum. Thus an exact optimum exists in this model. A proof that a known floor is sharp still needs a matching construction; existence alone does not supply it.

The all-size Theta(n log n) theorem is sharp in growth rate. It is not equality between the exact finite minimum and ceil(log_3((2n-5)!!)). The five-taxon example illustrates this: the tree-count floor is three but the admitted-source optimum is five. No proof that determining sharper constants is impossible is asserted.

### Latest exact-minimum continuation

Nolan explicitly redirected work from further fixture bounds to the actual minimum for every n. [EXACT-MINIMUM-THEOREM.md](EXACT-MINIMUM-THEOREM.md) establishes a uniform computable exact minimax function, not just abstract attainment. Every actual admitted source can be shortened to an admitted representative with the same split union and complete support, at most 8n-14 unrooted vertices plus one root. Retain actual branching blobs and replace maximal two-port chains by bridges. Root/path, LSA, galledness and outer-face preservation are exposed, conditional on pinned structural facts.

Enumerating bounded ACTUAL graphs and filtering the full admission contract gives exactly the finite admitted profile class. This avoids the unproved arbitrary-occurrence-code converse. Minimax over all candidate profiles and all quartet queries yields an optimal decision tree and recursively checkable lower certificate for every n. The forward-codec warning remains important: a small code alone would not certify that the profile catalogue is complete.

The normalization core has independent conditional reviews in [EXACT-PROFILE-REVIEW.md](EXACT-PROFILE-REVIEW.md) and [EXACT-NORMALIZATION-REVIEW.md](EXACT-NORMALIZATION-REVIEW.md). The specification can be prohibitively exponential, and its all-size catalogue, optimizer and certificate checker have not been implemented or executed. It provides a constructive exact procedure, not computed values above five, a fast finite-constant optimizer or a closed formula in n. That is the remaining numerical exact-minimum obligation.

## 6. Representation, runtime and biological boundaries

The complete support table has an exact Theta(n log n)-bit source representation, with a circle and O(n) supported gap pairs. This is proved separately in MINIMAL-PROJECTION.md. Query acquisition now matches that information scale in number of constant-size answers; writing explicit taxon sets for all splits can still cost quadratic time.

The peer reference code is polynomial and unoptimized; the query theorem does not claim near-linear runtime. The retained Gallai implementation uses O(n² log n) calls and polynomial computation, and its literal parity-completion stage has a quadratic method-specific rank requirement. That limitation did not constrain the structurally different insertion learner.

Exact support is the registered oracle. Controlled biological providers, finite-confidence absence, gene-tree probabilities and parameter/orientation identification require their separate observation and transfer proofs. The control-menu contribution can consume a bounded deterministic exact transcript conditional on its own provider guarantee; this query integration does not independently validate that stronger biological contract.

## 10. Provenance and uptake

This continuation recovered stalled work and published an initial checkpoint b3e850ed1cdb95fdad1cf5b5076e6ea23b4dc9d7. Fresh-main inspection then found the peer's stronger construction and explicit review request. The coordinating root changed priority from its own upper-bound development to independent review of that decisive result, preserving authorship and both implementations.

This packet accepts the peer theorem at the stated hand-proof/internal-review level and supplies an actual returned receipt in the authorized Commons workflow. It does not assert that another chat received the publication or that external mathematical review has occurred. Existing ownership and source proofs are preserved by non-force updates.

## 11. Process integrity

The source and oracle were pinned, close prior inspected, and the original invalid binary-tree premise preserved as a correction. Fresh-main checks prevented reporting an obsolete frontier. Independent reviewers split structural induction, local insertion, amortization, execution and finite minimax obligations. Universal proof, code replay, finite screens and reused source certificates remain separate. Matching lower and upper bounds use the SAME registered output and adaptive oracle model. Historical novelty and formal verification remain distinct from correctness review.

## 12. Inference robustness

The asymptotic closure depends on exact complete support, binary displayed trees, a common circle, the known-order decoder and inherited linear source count. Dropping the source count leaves the general order theorem intact but may enlarge full split recovery. Sampling cannot silently replace exact singleton or absence masks. Small-case agreement does not prove induction; the all-size structural and weighted arguments do. An attained minimum does not identify its exact value. The five-taxon proof is a source-admitted full-output lower bound and is not an order-only lower bound. No biological law or unique original graph is recovered by this query theorem.
