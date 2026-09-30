# Independent internal review: support quotient and graph-informed controls

Reviewer: `menu_combinatorics`, Codex Work subagent. Date: 2026-09-30 UTC.
Scope: read-only mathematical review followed by this attributed receipt; no repository publication or ownership reassignment.

Read: the existing control-menu `PIPELINE-THEOREM.md` and `REPORT.md`, the pinned canonical `ALL-LEVEL-PROOF.md` (Sections 1, 2, 7, 8), and the observation owner's `NORMALFORM-CANDIDATE.md`, materialized in `/tmp/normalization-effects-sources/`. The conclusions below inherit the canonical admission, paired-tip, capping and split-localization premises. Internal review is not external peer review or Lean certification.

## 1. Switching-wise support erasure passes

In a switched global tree, a blob's minimal subtree connecting its nonempty taxon ports is a tree. With two ports its reduced unrooted topology is a path; with three ports it is the unique tripod. Replacing every at-most-three-port blob by the corresponding edge or tripod therefore preserves **each individual switching's complete unrooted quartet and split system**, not only the union over switchings. Root/degree-two suppression changes no such bipartition. A replacement drawn inside the old blob preserves port order and exterior planarity; tree replacements add no reticulation cycles. A root inside a replaced piece can be located on a replacement edge; nonempty port components provide the rooted binary LSA partner. These admission statements inherit the original block/capping arguments, rather than a new general source-admission theorem.

Let active IDs be the original hybrids in blobs with at least four taxon ports. The switched support output factors through those coordinates. Deleting neutral literals from any sufficient original size-at-most-two certificate leaves a sufficient certificate: complete the erased coordinates to the old certificate, use its sufficiency, then use support independence from those coordinates. A menu on active IDs lifts by forcing those same original IDs and leaving erased IDs natural.

This support lift does **not** require equality of normalized controlled gene-CF laws. The existing common-inheritance provider runs on the original graph, with its original switched-quartet length floor `tau`. Neutral choices can continue changing quartet lengths and CFs; they do not spoil the support-mass guarantee or its original-graph contrast proof. It would be incorrect to claim preservation of a normalized metric/CF law or a normalized length floor without another argument.

## 2. Sharpened count upper bound passes

For retained blobs write `p_B >= 4`, `h_B` for hybrid count and `b` for the number of retained blobs. Each hybrid has a distinct pendant port in the capped blob, so `h_B <= p_B`. Every blob entered from an external root has a nonhybrid rootward port, giving `h_B <= p_B - 1`. At most one retained blob can contain the root.

The tree of blobs satisfies `sum_internal(degree - 2) = n - 2`; hence

```math
\sum_B(p_B-2)\le n-2,\qquad b\le\lfloor(n-2)/2\rfloor.
```

For `n >= 4`, the number `s` of retained original IDs therefore obeys

```math
s\le\sum_B(p_B-2)+b+1
\le\lfloor3n/2\rfloor-2.
```

If the root belongs to no retained blob, omit the `+1`. This receipt verifies an **upper bound**; it does not assert its sharpness on actual admitted networks.

## 3. Facial adjacency and three-environment upper bound pass

Opening a hybrid produces the two adjacent copies of its capped port. Their connecting tree path is the tree-edge part of that hybrid's unique bounded-face boundary. The pair straddles an opened-tree edge exactly when that path contains the edge. If two pairs straddle an edge, their bounded faces are the two incident bounded faces and are adjacent in the simple weak dual `D`. Suppressing a degree-two/root path preserves this pair set; one may use an original edge segment.

Every bounded face has a hybrid boundary edge incident to the exterior. In the plane dual, deleting the exterior vertex therefore exposes every remaining vertex to one common face; after removing parallel edges/loops, `D` is outerplanar and thus three-colorable.

Assign the three colors the column signatures `(0,1,*)`, `(0,*,1)`, and `(*,*,*)`. Different colors cover all four parental assignments with at least one matching force and no conflict. Singleton certificates are safe even in the all-star class, because their natural probability is at least `g`; zero-literal certificates are certain. Global displayed splits localize in one capped blob, while bridge/low-port splits are mandatory. A displayed quartet may inherit a certificate from a complete displayed split witnessing its topology. Thus this proves a conditional **at-most-three-environment** upper bound, throughout the inherited source class, with graph and original ID correspondence supplied.

Choose the largest color class passive. Each row forces at most `floor(2s/3)` IDs; the total number of forced assignments in the three rows is at most `2 floor(2s/3)`. Combining with the count above gives

```math
\text{maximum controls per row}\le n-2,
\qquad\text{total forced assignments}\le2n-4.
```

If `D` is edgeless, passive observation suffices for the occurrence guarantee. If `D` is bipartite, two environments suffice by forcing both values on a smaller color class and leaving the other class natural.

## 4. Actual finite evidence and boundary

This reviewer executed switching-wise projection checks on **336** padded admitted-gadget fixtures, with `r=2,...,8`, all active-ID pairs and all four required assignments, examining **45,040** original switchings. Complete unrooted quartet/split outputs agreed whenever the active bits agreed. This is finite corroboration of the two-port padding case, not an exhaustive low-port normalization proof.

A nontrivial three-port triangle was also checked directly: root arcs `R->D,R->P`; tree arcs `P->Q,Q->b0,b0->B,b0->C,H->A`; hybrid `H` has parents `P,Q`. Both switchings display the same quartet `AD|BC` and split. With every original edge length `log(2)`, the switched quartet internal lengths are respectively `2 log(2)` and `log(2)`, and the exact CF vectors are `(1/12,1/12,5/6)` and `(1/6,1/6,2/3)`. Thus support erasure genuinely does not imply preservation of every original controlled CF law. The original positive length floor remains valid.

**Unresolved here:** whether three environments are necessary for some actual graph-informed source-network target family. A nonbipartite weak dual establishes a lower bound for the stronger all-four-patterns-on-every-dual-edge coverage contract; it does not alone prove that every such pattern is indispensable for the actual displayed target union. No actual-source three-environment lower bound is promoted by this receipt. Physical controls, independent-lineage partial inheritance and historical novelty likewise remain outside the reviewed theorem.
