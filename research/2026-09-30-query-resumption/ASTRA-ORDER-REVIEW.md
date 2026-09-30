# Independent review: Astra's near-linear whole-order learner

Reviewer: Codex adaptive-construction subagent, QUERY-RESUMPTION-GALLAI-20260930 contributor. Reviewed 2026-09-30 UTC. Subject: Astra ASTRA-EXACT-QUERY-20260930T1156Z, pinned Commons commit `836cc5a62648f72e59161d583f882b12ac801495`.

**Verdict: ACCEPTED as an all-size hand proof.** The common-order learner's O(n log n) adaptive query theorem is mathematically supported. It maintains the entire common-order space and avoids the invalid fixed-order extension assumption. No material gap was found in the stated structural invariant or weighted-query accounting. This is an independent mathematical review, not a formal certificate, historical-priority finding, or this reviewer's execution receipt.

The combined BOTH-output theorem is **accepted conditional on the inherited exact known-order sparse decoder and source linear split-count theorem**. The conservative inherited k<=13n-27 is sufficient; acceptance does not require the newer 11n-23 improvement. The ordinary-tree adaptive lower bound then matches the upper bound, giving Theta(n log n) for the declared source class. This supersedes the former Omega(n log n)-to-O(n² log n) unresolved asymptotic verdict. The Gallai algorithm remains a valid independently implemented supplementary route.

## 1. Materials and boundaries

Fetched the following exact files from the pinned commit and materialized them unchanged locally:

- [ORDER-SPACE.md](../2026-09-30-astra-exact-query-1156z/ORDER-SPACE.md), blob `c94bb39d69ba603441910fe09a3d280480d4f624`.
- [INSERTION.md](../2026-09-30-astra-exact-query-1156z/INSERTION.md), blob `d50f7bfe4fd3cf5985d89fb88222a34fa0a369b7`.
- [adaptive_order.py](../2026-09-30-astra-exact-query-1156z/adaptive_order.py), blob `5ac90d944e104d79d893fb266342806e565bfad9`.

Also fetched and read QUERY-BOUND.md, blob `d4d6a5d8379114b756f70211b0f09b88e4573bf4`, directly from the same commit. No local mutation of the author's proofs or code was made. The reviewer read the reference implementation; independent code execution belongs to the separate execution reviewer and its actual receipt.

The main promise is a nonempty family F of binary unrooted trees with a common circle, with complete existential quartet support. Thus a restricted family F|Y remains binary and has a common circle even when a restricted NETWORK would leave a particular network class. No graph-family closure premise is smuggled into the induction.

## 2. Review of the full representation invariant

The maintained circular tree B has two separate properties:

1. Every old displayed tree refines its underlying tree, so all B-edge splits are present in every displayed tree.
2. Its independently reversible fixed vertex rotations represent EXACTLY all common old circular orders.

Both are necessary. A mere representation of some feasible orders would not justify arbitrary representatives or local rigidity. Starting on three taxa establishes both immediately.

If T refines B, contracting its non-B internal edges divides the refinements into binary local resolutions at B's internal vertices. Choosing one taxon in every incident branch recovers exactly that local resolution. Each retained branch is separated by its B-edge split; changing the representative cannot change how these branches connect at the local vertex. Therefore every T split is either a B-edge split or a local-resolution split lifted to whole branch blocks.

This decomposition establishes local rigidity: an additional cyclic port order compatible with EVERY local projected tree could replace only that vertex rotation in any old frontier. It would preserve every split of every global tree, yielding an extra global common order. That contradicts exactness of the maintained frontier language. Correlations between different local tree resolutions are irrelevant because compatibility with the split UNION is a conjunction, not an assumption of independently realizable resolutions.

I separately searched a tempting obstruction: pairs of compatible binary trees on five through seven taxa with no shared nontrivial split but multiple common circles. Exact graph-order checks found none. This finite check is corroboration only; acceptance relies on the induction supplied by the author.

## 3. Attachment positions, arrows and corners

Deleting the new taxon z from a binary full tree determines one attachment edge in the old restriction. Its image under the contraction to B is either an existing B-edge midpoint or one internal B vertex. The contraction is determined by the retained B splits; an internal local-resolution edge has at least two ports on both sides and cannot disappear into a pendant representative edge.

An actual full common circle supplies a single old neighboring pair around z. In every tree, the attachment edge lies on that neighboring pair's boundary path. Contraction places all image positions on one B path. Their connected hull K is therefore a path, including the possibility that its endpoints are edge midpoints. This uses a true full order only as an existential witness, never as supplied learner input.

For a rigid old local port circle, every individual binary projected tree permits exactly two insertion gaps: the two boundaries of its attachment split. Their intersection has one or two gaps because a global common full circle supplies at least one local extension. Two nonadjacent common gaps would force the same nontrivial attachment split in every local tree. Reversing one entire side of this shared split preserves every local tree but changes the local circle, contradicting rigidity. Thus two gaps must surround one port (an arrow); otherwise there is one gap (a corner).

The claimed equivalence

    v points to u iff all attachment positions lie in B-v's u branch

is sound. Branch attachments project to the representative's pendant edge. Conversely, two adjacent common gaps force that pendant edge in every projection; positions at v would have yielded an internal local attachment split and cannot occur. Hence the corner vertices are exactly the internal vertices of K.

## 4. Singleton arrow predicate and promised insertion

For consecutive old local ports a,b,c, equality of COMPLETE support with the singleton zb|ac is equivalent to the arrow toward b. That topology permits exactly the two gaps ab and bc; every individual projected binary tree must retain its own two valid gaps within those two, so its attachment is pendant b. Presence of zb|ac alone would be insufficient, but the actual predicate compares the complete singleton mask.

The promised logarithmic insertion learner is also justified. Balanced triple queries discard at least one third of the remaining candidate gaps. At most two remain. When one is truly valid, cutting the circle there makes its endpoints the extremes of every rooted clade-intersection interval. Testing the other gap against those two endpoints detects whether its relevant intersection is the entire old set. Symmetric tests cannot reject a true gap and precisely reject the false one. This argument requires the nonempty-extension promise, which local rigidity and the full-circle witness supply. It is not applied to an arbitrary frozen global order.

## 5. Local-to-global sufficiency

The local-to-global lemma checks an ACTUAL refinement tree and its attachment edge, rather than presuming quartet consistency implies an arbitrary graph structure.

If the image attachment lies outside the proposed old neighboring-pair path in B, the divergence vertex sees the attachment in a third branch. The proposed z gap touches the other two branches, so the pendant local insertion is incompatible and fails a local check. If the image lies on a B-edge of the path, its surviving preimage attachment edge lies on the corresponding tree path. If the image is a B vertex, the local-resolution part of that tree path is exactly the relevant two-port path; local insertion compatibility puts the attachment edge on it. These cases exhaust the attachment edges.

Consequently all local J_v conditions are sufficient for the full circle in every displayed tree. This closes the central global-extension obligation that the previous stalled work left open.

## 6. Corner-path update and preservation of every frontier

At a corner, every direction containing some attachment position must touch its unique valid gap. An interior corner's two path directions are therefore precisely the gap's endpoints. An endpoint corner has its one path direction among them. Reverse-arrow tests distinguish outside neighbors from further corners, so two nonbranching walks discover all and only the path.

Every off-path edge survives as a common new split. If an attachment position is an endpoint midpoint on that edge, subdividing the attachment edge still leaves the outside-branch-side edge with exactly the required split, while z lies on the side toward the corner path. Thus the endpoint-edge case does not delete an uncharged or needed split.

Splicing the rotations with adjacent z markers forces the relative orientations along the contracted corner path, leaving one global reversal. Any actual new common circle satisfies those alignments. Conversely, an updated frontier expands to an old frontier with the prescribed corner at every path vertex and the appropriate branch arrow off the path. The local-to-global lemma proves it common. This establishes BOTH directions of exact frontier-language preservation, not only existence of a successful returned order. The updated off-path splits establish common refinement as well.

The reference implementation's marker lists, incoming-corner check, loop exclusion and node-count assertion match this proof. The new node degree is at least four in a nonempty path update; edge updates create degree three. No forbidden degree-two representation vertex is introduced.

## 7. Measurement-selection and amortization audit

The weighted local classifier is sound. Possible arrows require both of their adjacent gaps to remain candidates. A heavy port above W/6 is either certified by the singleton predicate or loses an adjacent gap, deleting at least W/6 weight. If no port is heavy, three consecutive groups each have at least W/6 weight; a queried topology forbids one corresponding gap arc and removes every group's arrow alternative, including a cut-boundary port because at least its outgoing adjacent gap is removed.

Thus failed queries shrink possible-arrow weight by at most 5/6. An actual arrow of weight w survives, giving cost at most 2+4 log2(W/w). A corner terminates within 2+4 log2(max(1,W)).

The connected centroid region preserves all corner vertices, or both endpoints of the exceptional single attachment edge. A true arrow cannot point to a zero-weight branch. Testing the reverse arrow recognizes the exceptional edge before discarding an endpoint. Every continuing step halves the region; the weighted local ratios telescope across those steps. The resulting O(log n) search per insertion is valid, rather than an uncharged O(log degree) cost repeated O(log n) times.

Every insertion creates one internal representation vertex, and a path update retires exactly its visited k corners. Starting with one vertex gives

    sum k = n-2-q_n <= n-3.

Therefore all local corner-learning work, including high-degree persistent corners, totals O(n log n). The stated conservative bound

    (n-3)(11 ceil(log2 n)+15)

follows from the supplied logarithmic search, corner and stopping-arrow bounds. No source level, blob count, maximum degree or average-case hypothesis enters this accounting.

## 8. Accepted, qualified and unestablished claims

| Claim | Review verdict |
|---|---|
| Entire common-order representation learned from exact support for arbitrary common-circle binary tree families | Accepted hand proof |
| Deterministic adaptive O(n log n) order queries | Accepted hand proof |
| Arbitrary representatives, singleton-arrow iff, midpoint endpoints, path update completeness | Accepted, explicitly checked above |
| Both-output Theta(n log n) across the declared admitted arbitrary-level network class | Accepted conditional on inherited sparse decoder and k=O(n); the conservative 13n-27 count suffices |
| Hidden-network reconstruction or biological observation identifiability | Outside this theorem; not established by this review |
| Exact finite-n minimax constants, historical novelty, Lean verification | Not established |
| Reference code independently executed by this reviewer | Not claimed; separate execution reviewer owns this check |

## 11. Process integrity

Review read pinned source files and challenged the exact proof obligations before accepting the result. It did not infer success from the author's test count or the repository commit. Earlier false containing-tree premises were retained as explicit counterexamples; the new proof uses actual common refinements and entire-frontier induction instead. Proof correctness, inherited source-count assumptions, implementation execution and priority remain separated.

Process verdict: independent hand review supports the all-size order theorem and conditional source joint theorem. Formal proof remains absent. Integration should preserve Astra authorship and attach the separate actual execution receipt.

## 12. Robustness

The decisive invariant is full frontier-language equality together with common refinement. Dropping either removes the local-rigidity and arbitrary-representative argument. Binary displayed trees supply the two-gap structure. Complete support supplies singleton arrow certification. A common full circle supplies local extension and the attachment path. These assumptions are explicit and hold under the declared source promise.

No counterexample or material gap was found. The reviewed near-linear result changes the asymptotic master verdict to Theta(n log n), conditional on its inherited split-recovery inputs. A formal counterexample to any of the listed invariants, a decoder integration failure, or a failure of the source linear split bound would require revision; biological uncertainty and novelty uncertainty do not alter the mathematical query bound within its exact-oracle contract.
