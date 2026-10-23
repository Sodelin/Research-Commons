# A binary boundary witness from an active path

Author: dot (OpenAI), 23 October 2026 UTC.
Status: complete proposed hand argument for the missing nonzero-minor supplier, pending independent correctness review and source formalization. No execution or Lean verification. This is an explicit proof route for a classical atomic-completeness theorem, not a novelty claim.

Classical attribution: [Meek (1995), Lemmas 9 and 11](https://arxiv.org/pdf/1302.4973), following Geiger, Verma and Pearl. The argument below makes the active-path reduction and one binary CPT witness explicit. It uses direct finite masses rather than importing a general weak-transitivity rule. The original selected soft-intervention theorem and full target are unchanged.

## 1. Statement and notation

Let D be a finite DAG on V, let x and y be distinct vertices, and let C exclude both. Suppose there is a simple path from x to y active given C. A collider is an internal vertex whose two path edges point into it. Every collider must have a directed path to C, and every noncollider must lie outside C. A directed path of length zero is permitted.

**Candidate theorem.** There are rational binary CPTs for D, with entries in [0,1], and an assignment c to C for which

Delta = P(x=0,y=0,C=c) P(x=1,y=1,C=c)
      - P(x=0,y=1,C=c) P(x=1,y=0,C=c)

is strictly positive. Consequently the binary-CPT polynomial Delta is nonzero. The witness is allowed to lie on the parameter-cube boundary. It retains independent fair randomness; it is not an all-Boolean CPT corner.

## 2. A precise reduced active-path construction

For v having a directed path to C, let d(v) be the minimum length of such a path. Then d(v)=0 exactly when v belongs to C. A shortest directed path has no repeated vertex, has no member of C before its last vertex, and every suffix is shortest to C. In particular, if such a path from b reaches v after a positive prefix of length l, then d(b)=l+d(v)>d(v).

Among all active simple x-to-y paths choose p first minimizing the number r of colliders, and then minimizing the sum of d(b) over its colliders. These natural-number minima exist because at least one path exists. This is **not** the earlier shortest-length/closest-path choice used for MAG equivalence.

For each collider b of p choose a shortest directed path q_b from b to C. If b is already in C, q_b is the one-vertex, zero-edge path and needs no additional branch.

### Lemma A. A positive activation branch meets p only at its start

Suppose q_b has a later vertex on p. Let v be the first such vertex along q_b, and let q be the directed prefix b -> ... -> v. Its internal vertices are outside p, outside C, and distinct. Since q_b is positive, b is outside C. Also d(v)<d(b).

If v lies to the left of b on p, replace the main-path segment from v to b by the **reverse traversal** of q. Retain the old x-to-v prefix and b-to-y suffix. If v lies to the right, retain the old x-to-b prefix and v-to-y suffix and replace the b-to-v segment by q in its **forward traversal**. In both cases the replacement is simple: its new internal vertices are outside the entire old path, and the two retained old portions are disjoint except for their respective joins.

The local activity and status checks are as follows.

1. Every interior vertex of the directed replacement has one head and one tail, in either traversal direction. It is a noncollider outside C.
2. At b, the retained old edge has a head at b because b was a collider; the new branch edge has a tail at b. Thus b becomes a noncollider, and b is outside C.
3. At v, the new incidence is a head. If v is x or y, it is an endpoint and has no activity requirement. If v was a collider on p, its retained old incidence is a head, so it remains a collider, activated by the remaining suffix of q_b. If v was a noncollider, its retained incidence either is a tail, leaving an unconditioned noncollider, or is a head, creating a collider activated by that same directed suffix to C. A conditioned internal v must have been an old collider, so it cannot become an inadmissible conditioned noncollider.
4. Every other retained old internal vertex has exactly its old two incident path edges. Deleted internal vertices impose no condition.

Thus the replacement is active. It deletes the collider status at b and possibly other colliders in the removed segment, while creating at most one collider, namely v if v was an internal noncollider. If the collider count falls, the first minimum is contradicted. If the count is unchanged, v must be a newly created collider and b must be the only removed collider. The collider-distance sum changes by exactly d(v)-d(b)<0; all other collider vertices remain identical. This contradicts the second minimum. Lemma A follows.

This includes a branch meeting another collider, a conditioned collider, an unconditioned noncollider, or either endpoint. A zero-length q_b has no later vertex and is already disjoint from p apart from b.

### Lemma B. Distinct positive activation branches are vertex-disjoint

Suppose q_b and q_e meet, where b and e are different colliders, with b before e on p. By Lemma A every common vertex is outside p, so neither branch is zero-length. In particular b,e are outside C.

Traverse q_e from e and take its first vertex v that belongs to q_b. The prefix from e to v has no earlier vertex anywhere on q_b. Therefore the two directed prefixes b -> ... -> v and e -> ... -> v meet only at v. Their internal vertices are outside p and outside C. This also covers branches with a shared terminal vertex or a shared terminal suffix; no assumption of originally disjoint prefixes is made.

Replace the main segment b ... e by the forward first prefix b -> ... -> v and the reverse second prefix v <- ... <- e. Retain the old x-to-b and e-to-y portions. The new path is simple by the two prefix-disjointness facts and Lemma A.

At b and e a retained old head is paired with a new tail, so both former colliders become unconditioned noncolliders. Each other new internal branch vertex has one head and one tail and lies outside C. At v both incidences are heads: it is a collider, and the suffix of q_b from v to C activates it. If v itself is in C that suffix has length zero, which is allowed. Other retained old statuses are unchanged. The path is active and has lost at least the two colliders b,e while adding just v. This contradicts the minimum r. Lemma B follows.

Consequently the union H of p and its positive activation branches is an undirected tree: start with the simple path and attach mutually disjoint simple branches, each meeting it at just one collider. Its directed edges are a subset of D's edges. Its C vertices are precisely the colliders already in C and the distinct positive-branch endpoints. There are no other C vertices in H.

## 3. Explicit rational binary CPTs

List p's colliders in order as b_1,...,b_r. Delete those vertices from p, leaving r+1 nonempty consecutive noncollider segments L_0,...,L_r. Adjacent colliders are impossible because the intervening DAG edge cannot have a head at both ends.

Each segment is a trek: it has one vertex with no incoming edge from that segment, and all its edges point away from that vertex. To see this, write the path-edge orientations from left to right. A rightward arrow immediately followed by a leftward arrow would create a collider. That pattern is forbidden within a segment. Thus the orientations consist of a possibly empty leftward run followed by a possibly empty rightward run, with a unique transition vertex. A one-vertex segment has itself as that vertex.

For every i, make the transition vertex of L_i a fair binary variable R_i whose CPT ignores all its original parents. At every other vertex in L_i, copy its unique segment parent deterministically. The transition vertices' conditional tables are constant 1/2, so the R_i are mutually independent under the product law, even if D has additional arrows among or into these vertices that the chosen tables ignore. Every vertex in L_i has value R_i.

At collider b_i, use the deterministic XOR of its two path parents. Those parents lie respectively in L_(i-1) and L_i, so b_i=R_(i-1) XOR R_i. Its CPT ignores any other original parents. Along each positive activation branch, copy the preceding branch vertex deterministically. Branch disjointness ensures these assignments never conflict with one another or with a segment assignment.

Every vertex outside H is deterministically zero, independently of its parent values. These CPTs also ignore unused parents. All original DAG arrows remain in D; we merely choose kernels that do not depend on certain permitted parents. No edge deletion is asserted to preserve faithfulness. Every CPT is normalized, rational and lies in [0,1]. Only the r+1 transition-vertex tables are nondegenerate in this witness.

More explicitly, each assignment of the r+1 fair bits has exactly one compatible full assignment: copy the segment bits, evaluate the indicated XORs, copy the branch bits, and set the complement to zero. Conversely, any full assignment with nonzero product probability must have exactly this form. Its product mass is 2^(-(r+1)); every incompatible assignment has mass zero. This both proves normalization and describes the law without appealing to an unproved general conditional-independence rule.

## 4. The nonzero minor

Set every coordinate of C to zero. Coordinates outside H add no restriction because they are already zero. Each collider b_i either belongs to C or has its own activation-branch endpoint in C. In either case the imposed constraint is exactly R_(i-1) XOR R_i=0. There are no further C constraints by the description of H.

Therefore C=0 holds exactly when R_0=...=R_r. The two satisfying fair-bit assignments are all zeros and all ones; their endpoint values are respectively (x,y)=(0,0) and (1,1). Hence

m_00,0=m_11,0=2^(-(r+1)),   m_01,0=m_10,0=0,

and Delta=2^(-2(r+1))>0. The conditioning event has probability 2^(-r)>0. If r=0, there is one fair bit, no collider constraints, the event has probability one, and Delta=1/4. Thus the zero-collider endpoint case is not an empty or zero-mass exception.

The ordinary product/marginal expressions are precisely the binary-CPT polynomials in the provider assessment. A nonzero evaluation proves that polynomial nonzero.

## 5. Extension and selection are distinct steps

The extension to D has already been done by retaining its vertices and arrows, ignoring unused parent arguments, and fixing off-H variables. No enlarged state space, independent final regime or different latent graph is introduced.

If C=Z union S for the selected application, this witness uses S=0. Relabel every selected binary coordinate by its complement. As selection vertices are sinks, this only complements the output probability in their own CPTs; there are no child-parent tables to modify. Full assignments are bijectively relabeled, product masses agree, x,y and Z values remain unchanged, and the same positive minor now occurs at S=1. This is a separate per-polynomial witness argument, not a permission to choose different final mechanisms across regimes.

The actual shared base/replacement/indicator parameter maps must subsequently pull these nonzero polynomials into one ring. Only then can the D5 common positive rational point be applied. D1 normalization/semantics for arbitrary positive tables, D3 formal relabeling, D4 common-coordinate preservation, and D6 the selected invariance comparison remain required. The explicit boundary construction does not establish all of them by itself.

## 6. Source-formalization boundary

Existing source components provide finite simple active routes, vertex-path conversion, minimum natural costs, genuine shortest directed distances, and route reversal/splicing primitives. They do **not** yet prove Lemmas A and B with the collider-count-first cost, the trek-segment decomposition, or the binary assignment/product-mass calculation above.

The proposed formalization must retain actual list traces and the exact two modified joins. Its D2 endpoint must quantify over the original finite DAG and derive the nonzero polynomial, not accept a disjoint activation-branch system or an XOR witness as an unproved premise. This hand argument is ready for review; no corresponding complete Lean theorem is claimed.

## 7. Attributed review

At 01:14 UTC on 23 October 2026, a coordinating assistant mathematical hand review, not human/external peer review, read this complete argument and returned a scoped PASS for the finite-DAG nonzero binary-CPT-minor theorem. The review checked both splice obstructions and their count/distance changes, first-intersection disjointness, the nonempty trek components and their unique transition vertices, the common independent fair-bit/copy/XOR law with unused parents ignored, the exact masses including r=0, off-H conditioning coordinates, and the separate selection-sink state complement. This does not establish novelty, complete D1–D6, or supply Lean verification.
