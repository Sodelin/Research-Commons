# Independent local review of Astra's path-insertion argument

Reviewer: Codex delegated primary-prior researcher, QUERY-RESUMPTION-PRIMARY-20260930. Date: 2026-09-30 UTC. Reviewed packet: `2026-09-30-astra-exact-query-1156z/{INSERTION,ORDER-SPACE}.md`, supplied by the coordinating agent from the newer main packet. Status: independent all-size local argument audit and independently executed finite graph controls; no publication, navigation edit, formalization, or historical-priority claim.

## 1. Verdict and limits

**PASS for the requested local claims.** I found no counterexample or missing premise in the complete-singleton one-quartet arrow test, the prohibition on two nonadjacent local gaps, or local common-refinement rigidity. The fixed-order insertion certificate and promised two-candidate endpoint test are also sound. Their premises must remain explicit: binary displayed trees, a compatible old local order, complete support masks, and, for the logarithmic endpoint procedure, a nonempty-extension promise.

The local rigidity premise is established from the maintained shared-refinement and exact-frontier invariants; it need not be imported from a level-one network theorem. This is the distinction that makes the new whole-order-space argument avoid the admitted frozen-order extension obstruction.

I also checked the geometric arrow characterization and local-to-global path-membership argument. They are sound once those invariants hold. This review does **not** independently certify the centroid search, the complete global update implementation, the total adaptive query accounting, or the source-specific sparse split-recovery stage. Other reviewers own those obligations. Passing these local claims alone is not a full master closure.

## 2. Common-refinement local rigidity

Assume the old binary trees all refine the same underlying tree `B`, and the frontiers of the fixed-rotation circular tree `B` are exactly their common circles. For an internal vertex `v`, the connected preimage of `v` under any tree contraction is its binary resolution on the incident ports. Every edge within that preimage cuts complete port blocks. Edges outside it are either surviving `B` edges or resolution edges at other vertices.

Restricting to one representative per incident component recovers the resolution on the ports: paths inside a branch merely subdivide its pendant port edge and disappear under suppression. Changing the selected representative within a branch cannot change this local topology. This uses genuine refinement; it would be false if representatives were selected from an arbitrary learned graph lacking that invariant.

Every displayed split of an old tree is therefore a `B` edge split or a lifted local resolution split at one vertex. An order that preserves the `B` branch blocks meets all tree constraints exactly when its port order at every vertex meets the corresponding local constraints.

Suppose the restricted local tree family at `v` admitted a circle different from `B`'s fixed port circle and its reversal. Start with any old frontier, keep every other vertex and every branch's internal order, and substitute the alternative port order at `v`. All `B` edges remain intervals. All local splits at other vertices remain intervals, and the new local order makes every split at `v` an interval. This single global order is consequently compatible with **every** old tree, while its projection at `v` prevents it from being a frontier of `B`. That contradicts exact-frontier invariant (B).

This is a simultaneous conjunction of constraints from the actual trees. It does not require that their local resolution choices occur independently or that a Cartesian product of displayed trees exists in the source. The proof also applies when there are only three ports, whose cyclic order is unique up to reflection.

## 3. Individual trees have exactly two insertion gaps

Deleting the new leaf `z` from one binary tree and suppressing its neighbor identifies a unique old attachment edge. For any compatible old circle, that edge's two sides are intervals, and the two gaps at their boundaries are precisely the insertion gaps compatible with the full tree.

A direct justification is useful: reinsertion adds both splits `A | (B∪{z})` and `(A∪{z}) | B` obtained from the subdivided attachment edge, in addition to the surviving old constraints. These are jointly circular exactly when `z` is put at a boundary between `A` and `B`. The assertion includes pendant edges, whose boundary gaps are the two gaps adjacent to their taxon. Binary resolution is essential: unresolved trees can allow more gaps.

Intersecting these two-element sets over a nonempty tree family gives at most two common insertion gaps. For a rigid local old circle the extension is nonempty: restrict an actual full common order to the local representatives and `z`; if its old projection is the reversed circle, reflect the projection. Thus the logarithmic promised insertion subroutine is legitimately invoked locally, even though a previously chosen **global** old frontier might not extend.

## 4. Why two nonadjacent local gaps contradict rigidity

If the family has two common insertion gaps, then each individual tree's entire gap pair equals that common pair. The two gaps uniquely determine an old bipartition `A | B`, and it is the attachment-edge split in every local old tree. If the gaps are nonadjacent, both parts contain at least two ports.

Reverse the order within `A`, keeping the order within `B`. Since the same attachment split occurs in every tree, reflecting the whole `A` side across its edge preserves compatibility with each tree. The resulting circle differs from the original and its full reversal: the two boundary cross adjacencies change, and neither part is a singleton. Hence the local family has an additional common circle, contradicting Section 2.

The conclusion is exactly the advertised dichotomy: a nonempty local gap set is one corner, or the two gaps adjacent to one port. The stronger, previously attempted statement that an arbitrary all-transitive partial parity space sits inside one binary-tree embedding space is not used.

## 5. One quartet recognizes the specified arrow

Let `a,b,c` represent three consecutive ports in that cyclic order, with `b` at the candidate arrow port. For a given binary tree compatible with the old local circle, the quartet `zb|ac` is circular precisely when `z` lies on the two old gaps adjacent to `b`. The complementary arc from `c` back to `a` contains all other gaps. This geometry relies on consecutivity of the three ports, not just an arbitrary choice of representatives.

If the **complete support** on `{z,a,b,c}` is exactly `{zb|ac}`, every family member displays that topology. Both of each member's true insertion gaps must lie among the two allowed gaps. There are exactly two such true gaps, so its gap pair equals those two gaps. Consequently the whole family's valid set is the two gaps adjacent to `b`.

Conversely, if those two gaps are valid for every member, projecting either insertion order to the four taxa gives `zb|ac`; no member can display a different topology. Thus the complete support is that singleton.

This implication is actually valid before imposing local rigidity or nonempty common extension: only individual compatibility of the old circle and binary trees is needed. Rigidity is needed to classify **all** possible local outcomes as arrows or corners. Presence of `zb|ac` alone would be insufficient, and nonconsecutive `a,b,c` would leave additional allowed gaps.

To connect the gap condition to geometry in `B`, an attachment position in the `b` branch projects to a pendant attachment at its representative. This remains true if the representative's path does not pass through the attachment: the projection joins their paths within that branch and suppresses the intervening paths. If the position equals `v`, the attachment edge lies in the binary resolution of `v`; it splits at least two ports on each side and survives restriction to one representative per port. It therefore cannot project to a pendant attachment. Positions in other branches project to their respective pendant ports. This proves

`v→u  iff  all attachment positions lie in the u-component of B−v`.

It follows that `v` is a corner exactly when it lies in the minimal subtree `K` spanning the attachment positions. For adjacent `v,u`, both opposite arrows hold exactly when every position is the midpoint of their common edge. Leaves can be handled without queries because attachment positions never equal leaves.

## 6. Fixed-slot and promised endpoint certificates

For an old gap `(b,c)`, inserting `z` there is valid exactly when no old taxon `a` outside the endpoints witnesses `za|bc`. Necessity is crossing geometry. For sufficiency, if a particular tree's attachment split has both `b,c` on one side, choose any old `a` on the other side. One edge next to the new attachment vertex displays `za|bc`. Therefore every invalid gap has such a witness.

For two surviving candidate gaps `g=(u,v)` and `h=(b,c)`, assume at least one is truly valid. If `g` is valid, cut the old circle there, giving linear-order endpoints `u,v`. Root each displayed tree at the neighbor of `z`. Its LCA clade of `b,c` is an interval in this linear order; their intersection `I_bc` is also an interval and contains `b,c`. The second gap is valid exactly when every such clade is the full old set, equivalently `I_bc` is the full set. An interval is the full set exactly when it contains both endpoints. Membership of an endpoint `a` distinct from `b,c` is exactly absence of `za|bc`; repeated endpoints need no query because they already belong to `I_bc`.

Thus two endpoint tests decide `h` when `g` is valid. The symmetric tests retain a genuine gap and reject a false one. Two false candidates are outside the promise and can falsely certify each other; the promise cannot be dropped. Balanced three-arc elimination preserves every true gap and removes at least `floor(s/3)` of `s≥3` candidates per complete query, so the logarithmic promised bound is justified locally.

## 7. Local-to-global path membership

For a proposed insertion between old neighbors `b,c`, fix one actual full tree and its old attachment edge `e_T`. Binary-tree embedding geometry says validity is equivalent to `e_T` lying on the old tree path from `b` to `c`.

If the image position in `B` lies outside `P_B(b,c)`, the first internal vertex where its branch leaves that path sees three distinct directions: toward `b`, toward `c`, and toward the attachment. The proposed local insertion is between the first two ports, whereas that tree projects to pendant attachment in the third. Its local constraint rejects the insertion.

If the image is a surviving edge midpoint on the path, the unique surviving preimage edge also lies on the old tree path. If the image is a vertex on the path, the path's segment through the binary resolution at that vertex is the path between the two relevant port representatives. The local insertion condition puts `e_T` on that segment. Hence it lies on the whole old tree path.

This proves sufficiency tree by tree, and necessity is restriction. No assumed quartet extension or unproved independence of local source choices enters the argument. I found no flaw in this lemma. Exact path splicing, all-frontier preservation, and query accounting should nevertheless retain their separate reviewer receipts.

## 8. Independently executed finite controls

Executed Python 3.13.5 with assertions enabled. Files: `astra_local_prior_review_controls.py` and `astra-local-prior-review-controls.json`. The new checker imports the earlier root verifier's credited binary-tree generator and graph-edge-cut split routine; it imports **no** Astra insertion, arrow, or update implementation. True old circles and true new insertion gaps are determined directly from all tree splits and exhaustive leaf-order enumeration. Quartet masks are independently derived from graph cuts.

| Old taxa | Canonical-compatible full trees | Family cases | Rigid-old-circle cases | Rigid cases with extension | Arrow checks | Fixed-slot checks | Two-candidate endpoint checks |
|---:|---:|---:|---:|---:|---:|---:|---:|
| 3 | 3 | 7 | 7 | 6 | 21 | 21 | 9 |
| 4 | 10 | 1,023 | 961 | 80 | 4,092 | 4,092 | 302 |
| 5 | 35 | 630 | 245 | 160 | 3,150 | 3,150 | 1,470 |
| 6 | 126 | 8,001 | 2,754 | 1,518 | 48,006 | 48,006 | 20,340 |
| 7 | 462 | 106,953 | 33,033 | 15,757 | 748,671 | 748,671 | 286,825 |

All **116,614 family cases** passed. The first two rows exhaust all nonempty families compatible with the canonical old circle. The later rows exhaust singleton and pair families, not all larger families. There were 37,000 rigid-old-circle cases and 17,521 rigid cases with nonempty extension; every two-gap rigid case had adjacent gaps. All 803,940 arrow equivalence checks, 803,940 fixed-slot checks, and 308,946 promised two-candidate checks passed.

These controls include families with no full common circle, used to test zero-extension behavior. They are not claimed to be admitted network witnesses. Nor do local finite checks test the whole updated frontier language, centroid search, or sparse recovery. The all-size conclusions in Sections 2–7 depend on their proofs, not these counts.

## 9. Closest primary prior and transfer boundary

Frohn, Holtgrefe, van Iersel, Jones & Kelk (2025), *Reconstructing semi-directed level-1 networks using few quarnets*, DOI [10.1016/j.jcss.2025.103655](https://doi.org/10.1016/j.jcss.2025.103655), [primary full text](https://arxiv.org/html/2409.06034v2), is close prior: Theorem 14(c) already gives `O(n log n)` displayed-quartet reconstruction of most of a **semi-directed level-one** network. Lemmas 7–9 use leaf insertion, pointing edges, and a weak stem path; Lemma 12 uses centroid and cycle-spine balancing. These ideas deserve explicit credit. Their theorem does not directly establish Astra's arbitrary binary-tree-family promise: its invariant is a canonical network, and its stem/path tests use level-one structure and known reticulation information. Astra instead learns an exact whole-frontier circular tree and proves its arrows from consecutive representatives. No inspected adaptation theorem automatically makes the two contracts identical.

Keijsper & Pendavingh (2014), *Reconstructing a phylogenetic level-1 network from quartets*, DOI [10.1007/s11538-014-0022-z](https://doi.org/10.1007/s11538-014-0022-z), [primary full text](https://arxiv.org/html/1308.5206v1), is also close prior. Its Lemma 4 relates split-side reversal to compatible order spaces, Theorem 2 gives affine order-space structure, and Theorem 3's proof already reasons about leaf insertion along a boundary path. Its supplied quartet reconstruction is cubic; it does not charge the new whole-frontier acquisition algorithm's adaptive measurements. The earlier all-family intersection corollary remains attributed in `PRIMARY-PRIOR.md`.

C-node/PC-tree frontier representations and explicit constraint updates are established data-structure prior, as recorded in the earlier primary audit. They do not independently supply the hidden complete-support oracle's sparse measurement strategy.

Primary full texts and exact passages were inspected, rather than inferred from titles. Frohn receipts: full `turn46view0`, Lemma 12 `turn47view0`/`turn47view2`, stem details `turn47view3`, exact Theorem 14 `turn48view0`, Lemmas 8–9 `turn48view1`. Keijsper receipts: full `turn46view1`, Lemma 4 / Theorem 2 / boundary-path argument `turn48view2`. Persistent citations are the URLs/DOIs above.

Additional bounded searches used `"common circular orders" trees quartet PC tree reconstruction`, `"circular ordering" "quartet" "insertion" logarithmic`, `"phylogenetic" "quartet" "frontiers"`, and stronger-engine checks with circular/quartet/`O(n log n)` and common-circle/path-insertion terms. Most returned irrelevant exact-word hits or already known network methods. No exact arbitrary-family acquisition theorem was located. This is a bounded prior comparison, not systematic coverage or a historical novelty guarantee.

## 10. Handoff

The coordinating agent received the local PASS verdict before this file was completed. The relevant improvement is substantive: local extension exists because the old **entire** common-order language is rigid at each learned vertex, while the algorithm is free to replace old global orientations along a corner path. The frozen-order obstruction remains true and is respected.

Before a full upper bound is registered, combine this receipt with the independent global-splicing, centroid-search, all-query accounting, and source split-output reviews. Retain complete masks and binary-tree premises in the theorem statement. Do not identify the learned circular tree with the original network or infer the full split union from it without the separate recovery theorem.
