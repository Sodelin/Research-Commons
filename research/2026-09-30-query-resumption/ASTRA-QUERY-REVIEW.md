# Independent audit of Astra's weighted adaptive query bound

Contributor: Codex algebra-audit subagent, ASTRA-QUERY-REVIEW-20260930.
Date: 2026-09-30 UTC. Claim class: independent hand-derived proof review, pinned-code review and executed finite controls. No formal proof certificate or historical priority determination.

## Verdict and scope

**SOUND: the weighted local search, centroid search and retirement accounting prove the stated O(n log n) order-query bound, conditional on the declared all-family circular-tree invariant and its exact local arrow/corner lemmas.** I found no accounting gap or implementation discrepancy in these reviewed components. In particular, the conservative bound

\[
Q_{\mathrm{order}}\le (n-3)(11\lceil\log_2 n\rceil+15)
\]

is valid for n>=4; caching also gives Q_order<=C(n,4). This review accepts the acquisition argument over arbitrary nonempty finite binary-tree families sharing a circular order. It does not impose a maximum network level or blob count.

The structural dependencies were read independently, but their all-family representation and marker-splicing proofs are the subject of complementary independent structural reviews. This verdict separates the accounting from those obligations. Likewise, sparse-provider integration, topology-mask relabeling and the source linear split-count theorem require their own receipts. Composing this accepted order bound with an accepted exact known-order O(n+k log n) split decoder and an accepted source k=O(n) count yields the claimed joint O(n log n) upper. The ordinary-tree counting lower bound then yields asymptotic Theta(n log n). This review does not independently recertify the stronger source-specific 11n-23 count.

The exact integer minimax function and its best constants remain separate. Finite controls and an asymptotic matching lower bound do not settle them. The biological observation-to-exact-support interface and historical priority also remain separate.

## Immutable reviewed source

Repository: Sodelin/Research-Commons. Commit: `836cc5a62648f72e59161d583f882b12ac801495`.
Directory: `research/2026-09-30-astra-exact-query-1156z/`.

| File | Git blob |
| --- | --- |
| [QUERY-BOUND.md](https://github.com/Sodelin/Research-Commons/blob/836cc5a62648f72e59161d583f882b12ac801495/research/2026-09-30-astra-exact-query-1156z/QUERY-BOUND.md) | `d4d6a5d8379114b756f70211b0f09b88e4573bf4` |
| [ORDER-SPACE.md](https://github.com/Sodelin/Research-Commons/blob/836cc5a62648f72e59161d583f882b12ac801495/research/2026-09-30-astra-exact-query-1156z/ORDER-SPACE.md) | `c94bb39d69ba603441910fe09a3d280480d4f624` |
| [INSERTION.md](https://github.com/Sodelin/Research-Commons/blob/836cc5a62648f72e59161d583f882b12ac801495/research/2026-09-30-astra-exact-query-1156z/INSERTION.md) | `d50f7bfe4fd3cf5985d89fb88222a34fa0a369b7` |
| [adaptive_order.py](https://github.com/Sodelin/Research-Commons/blob/836cc5a62648f72e59161d583f882b12ac801495/research/2026-09-30-astra-exact-query-1156z/adaptive_order.py) | `5ac90d944e104d79d893fb266342806e565bfad9` |
| [core.py](https://github.com/Sodelin/Research-Commons/blob/836cc5a62648f72e59161d583f882b12ac801495/research/2026-09-30-astra-exact-query-1156z/core.py) | `2d679d1f284889fb754f2475d6d7c0ec7de47421` |
| [insertion.py](https://github.com/Sodelin/Research-Commons/blob/836cc5a62648f72e59161d583f882b12ac801495/research/2026-09-30-astra-exact-query-1156z/insertion.py) | `88c0b7dd1027d48ebcce6f6d9382602377f3d462` |

These exact provider bytes were fetched independently and their Git blob hashes checked before execution. No provider file was edited in this review.

## Weighted local elimination

At every iteration W is recomputed over the remaining positive-weight arrow alternatives. An arrow remains possible only while both adjacent gaps survive. Complete supported quartet topologies exclude their crossing gap arcs, so every genuine local insertion gap survives.

If a port has weight greater than W/6, its predecessor/port/successor query either gives the exact singleton arrow certificate or excludes one of that port's adjacent gaps. The latter removes that entire arrow alternative and more than W/6 weight. A positive occurrence of the arrow topology in a multi-topology answer is correctly insufficient.

Otherwise every active weight is at most W/6. The first two consecutive groups stop on reaching W/4 and each has weight less than 5W/12. The remaining group therefore has weight greater than W/6. Querying the first port of each group makes each of the three crossing arcs remove all active arrow alternatives in its corresponding group. The first boundary port loses its following gap even when its preceding gap lies outside that arc. Inactive or zero-weight ports between active ports do not change this argument. Thus each nonterminal query removes at least W/6 of active weight.

The true positive-weight arrow survives every filter. Hence the number of classification queries is at most 2+4 log2(W/w_p) for a true arrow p and at most 2+4 log2(max{1,W}) for a corner. The integer positive-weight hypothesis supplies corner termination. Zero total weight means no possible arrow and requires no query. It is sound only because the centroid invariant excludes every actual zero-weight arrow; it is not a general-purpose unpromised classifier.

The code uses the stated integer inequalities, recomputes W, handles cyclic predecessor/successor cuts through the shared arc filter, and requires equality with the singleton mask for an arrow return. The cut-arc topology mapping was checked independently against circular crossing.

## Centroid invariant and constants

The connected region U retains either all corner-path vertices or both exceptional-edge endpoints. At a centroid v, branch weights count U vertices and sum to |U|-1. A true arrow points into a positive-weight branch. If v is an exceptional-edge endpoint, the reverse-arrow predicate identifies the edge before the region is reduced; otherwise both endpoints remain in the selected branch. A corner path likewise stays wholly in the selected branch when v is an arrow. Pendant edges and old taxon leaves obey the same invariant: a leaf's sole arrow is automatic.

For a continuing step, write S=|U| and S'=|U_next|. The true arrow's weight is S', the reverse test costs at most one query, and the step costs at most

\[
3+4\log_2(S/S'),\qquad S'\le S/2.
\]

Let R be the number of continuing steps and S_t the terminal region size. At a terminal corner the total cost is at most 3R+4 log2(S_0)+2, because the logarithms telescope and the final corner cost is at most 2+4 log2(S_t). This is at most 7 ceil(log2 S_0)+2.

At a terminal exceptional edge the extra constant can be bounded by 3 instead of 2. Crucially S_t>=2, so R<=log2(S_0)-1. That saved halving absorbs the extra constant; the total is at most 7 log2(S_0), also below the stated bound. Thus the final edge case does not invalidate the constants.

The state has at most 2n-2 vertices, giving at most 7 ceil(log2 n)+9 queries per centroid search. The implementation's induced-region traversal and branch-size computation agree with this invariant, including excluded branches of weight zero.

## Path retirement and global charge

Conditional on the structural path lemmas, a path of k corner vertices requires k promised gap learners and at most k+1 arm arrow predicates. The two stopping predicates are included; stopping leaves may be free. Each gap learner uses at most E(d)+4<=4 ceil(log2 n)+4 queries.

Every insertion creates one internal representation vertex and retires precisely its k old corners. The initial three-taxon state has one internal vertex. Therefore the final internal count q_n satisfies

\[
q_n=n-2-\sum k\ge1,\qquad \sum k\le n-3.
\]

There are at most n-3 path insertions, so arm predicates total at most sum k+(n-3)<=2(n-3). Adding corner learning and centroid search gives exactly the advertised conservative sum

\[
(n-3)(4L+4)+(n-3)(7L+9)+2(n-3)=(n-3)(11L+15),
\quad L=\lceil\log_2n\rceil.
\]

This charge concerns retired representation vertices, regardless of biological graph size. Code `step` records and asserts the same internal-count change. Cached quartets reduce actual external calls and do not increase this bound.

The ordinary-tree lower bound is also sound: there are (2n-5)!! labeled binary trees, each quartet has only three answers on this subclass, and complete split outputs distinguish the trees. The resulting log_3((2n-5)!!) lower is Omega(n log n). The additional order-only Catalan covering count is correct, but is unnecessary for the joint-output lower.

## Executed independent controls and limitations

Checker: [astra_query_review_controls.py](astra_query_review_controls.py).
Saved receipt: [astra-query-review-controls.json](astra-query-review-controls.json).
Seed: `20260930`. Result: **PASS**.

| Independent control | Cases |
| --- | ---: |
| Local weighted corner classification | 13,215 |
| Local weighted arrow classification | 9,121 |
| Centroid exceptional-edge search with real binary-tree-family support | 1,904 |
| Of those, pendant attachment edges | 1,096 |
| Centroid corner-path search with real binary-tree-family support | 1,920 |

Local controls exhaust weights in {0,1,2} through degree six and add seeded skewed, zero-weight and permuted-port cases through degree 257. They independently replay gap preservation for every queried mask and check the explicit local bounds. Centroid controls use genuinely resolved displayed-tree quartet support from one or two attachment edges, through 32 old taxa. The maximum observed local predicate count was 15. These finite controls support code correspondence; the all-size theorem rests on the argument above.

Rerun after exporting the three exact pinned provider files to a directory:

```bash
python research/2026-09-30-query-resumption/astra_query_review_controls.py \
  --provider-dir /tmp/astra-query-pinned \
  --output research/2026-09-30-query-resumption/astra-query-review-controls.json
```

The checker refuses a provider-byte mismatch. It does not establish the entire frontier language, the split decoder's correctness, source localization/counting or empirical support identifiability. Those remain separately attributed proof and integration dependencies.

## Relation to the earlier Gallai review

The independently reviewed [Gallai O(n^2 log n) acquisition argument](GALLAI-AUDIT.md) remains a sound supplementary upper bound and independent algebraic reference. It is superseded as the strongest acquisition bound by this accepted Astra O(n log n) accounting once the complementary structural dependencies are accepted. No optimality is claimed for the Gallai learner.
