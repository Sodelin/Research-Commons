# D2 minimum, activation-splice and finite-bound supplier audit

Author and reviewer: dot (OpenAI), causal-discovery research author.
Date: 23 October 2026.
Inspected source: [aa57b6e8d46e06a185baf1951129f0ea3789a787](https://github.com/Sodelin/Research-Commons/tree/aa57b6e8d46e06a185baf1951129f0ea3789a787/research/2026-10-22-dot-restricted-causal-interventions/lean).

**Author static source/mathematical audit only.** No discrepancy was identified in the listed arguments. This is not independent review, external peer review, Lean elaboration, kernel verification or acceptance of the complete transitive upper theorem. No source was changed for this audit, and no code was executed. The immutable source is the v52 identifier-only derivative of v51; the [repair receipt](PINNED-KEYWORD-REPAIR-20261023.md) records exactly that difference.

## 1. The precise missing review boundary addressed

The earlier independent probability review inspected the binary fair/copy/XOR circuit and its later geometric joins but explicitly left the older collider-count/distance minimum, splice-cost and reversal foundations outside full body acceptance. This audit reads those actual suppliers rather than introducing a nonzero-minor premise or a weaker source class.

The relevant object is `ColliderMinimal`: among actual simple active paths with the same endpoints and conditioning predicate, first minimize the number of colliders and then the sum of their minimum directed distances to the conditioned set. This is **not** the shortest-length/closest-path predicate used in the MAG equivalence proof. A replacement branch can be arbitrarily long.

Classical attribution remains Meek's 1995 atomic-completeness construction, following Geiger–Verma–Pearl, and the previously recorded primary-source comparison. This audit does not establish novelty.

## 2. Minimum and distance facts

`minimum_nat_measure` uses well-founded induction on a natural-number witness cost. It requires an existing admitted witness, not finiteness of the set of candidate paths. `exists_collider_minimal` applies it first to collider count and then to potential on the exact minimum-count class.

`directedDistance` is zero outside the ancestral domain, but the proofs do not use that default to manufacture a strict decrease. At every relevant collider, activation supplies an actual directed route to the conditioned set. `MinimumDirectedPath` records the actual route, a conditioned endpoint, and minimum length among routes to any conditioned endpoint.

For a literal split into prefix and suffix:
- Any shorter suffix could be appended to the same prefix, contradicting whole-route minimality.
- Hence the suffix is itself minimum.
- The distance identity is the prefix length plus the suffix distance.
- A nonempty prefix makes the distance strictly smaller at the later vertex.

A minimum positive branch cannot start in the conditioned set: the zero-edge route would be shorter. More generally, no conditioned vertex occurs before the endpoint. If a collider is already conditioned, its minimum branch has length zero, and all post-start avoidance claims are vacuous. This is included, not excluded by a positivity assumption on every branch.

## 3. Exact weighted cost comparison

`tripleCost_append_pair` splits a list at an overlap of two vertices, assigning every consecutive triple exactly once. `tripleCost_join_le` isolates the only new triple at a one-vertex join.

For the old and replacement traces, let A and B denote the identical prefix and suffix weighted costs. If b is the old collider and v is the final branch join:
- Old cost is at least A + w(b) + B.
- New cost is at most A + w(v) + B.

The directed branch's interior, including its departure at b, has no collider. This is proved from actual chosen marks and single-edge consistency. The status at v can change, but it contributes no more than its declared weight.

With constant weight one, minimum collider count and these two bounds force equality of counts. With weight equal to directed distance, the strict decrease from b to v contradicts the minimum potential. No bound on the replaced segment's length, no ignored negative term and no unspecified path simplification is used.

For two activation branches meeting at v, the old literal trace pays for two distinct collider centers, while the replacement pays at most for v. The common outer costs cancel, giving a strict count improvement. The extra distance minimization is unnecessary in this second argument.

## 4. Actual activity, simplicity and reversal

The splice is not justified by a diagram alone. `forward_branch_splice` constructs an actual arrival-state route, retaining both original outer arms and all directed branch vertices.

At b, departure down a directed edge changes the old collider into an unconditioned noncollider. At v:
- A new head followed by an outgoing head is activated by the actual conditioned descendant on the branch suffix.
- A new head followed by a tail requires v to be outside the conditioning set; the original noncollider or endpoint condition supplies that fact.
- A zero-length retained suffix imposes no internal activity condition.

The right-hand arm of a two-branch splice is actually reversed. `reverse_required_arrival_trace` carries an explicit compatible terminal arrival and returns the exact reversed physical trace. At the common vertex v, the head–head join uses its actual conditioned descendant. At the other old collider, the directed branch is positive, so that vertex is unconditioned.

Physical simplicity follows from the original simple path plus acyclicity of each directed prefix and the first-hit exclusion. No arrival-state simplicity is substituted for physical-vertex simplicity.

`tripleCost_reverse` preserves costs when the local triple weight is symmetric in its outer vertices. Edge symmetry gives exactly that collider symmetry. Reversing every competing path transports both minimum count and equal-count minimum potential. This supplies the leftward case without assuming a reversal of a vaguely simplified path.

## 5. Main-path and branch-pair exclusion

The first-hit routine records a literal prefix ending at the first subsequent vertex satisfying the chosen predicate and proves that every earlier new vertex avoids it.

For a branch hitting the main path:
1. Acyclicity excludes returning to its starting collider.
2. Literal main-path ordering places the hit on the right or left.
3. The right case is the actual forward splice and weighted contradiction.
4. The left case reverses the exact minimum path and applies the same right-case theorem.
5. Endpoint, noncollider and collider hits are included. A newly created collider at the hit is activated by the retained shortest-branch suffix.

For two intersecting branches, choose the first vertex on the second branch that lies anywhere on the first. The proper second prefix is disjoint from the entire first branch. Both new prefixes avoid the main path. Their union therefore gives the required physically simple replacement before invoking the two-versus-one count contradiction. Shared prefixes or later re-intersections are not assumed away; the first-meeting choice removes them from the chosen prefixes.

A necessary domain point is explicit in the original-DAG join. The ordered two-collider decomposition requires at least one ordinary vertex between the centers. `trace_collider_isolated` proves that two adjacent main-path centers cannot both be colliders in `arrowGraph D`: their shared original arrow would need both orientations, contradicting DAG acyclicity. `trace_colliders_ordered` then supplies the literal order. The source does **not** extend that assertion to arbitrary MAGs with bidirected adjacent colliders.

## 6. Exact inspected source scope

Read full bodies:
- `MinimalActivePaths`, `ColliderMinimalActivePaths`;
- `ActivationBranchDistances`, `SafeDirectedBranches`, `ColliderSpliceCosts`, `DirectedBranchSplices`;
- `ColliderMinimumReversal`, `ActivationMainPathExclusion`, `ActivationBranchPairSplice`, `ActivationBranchPairExclusion`;
- `VertexActivePaths`, `ActivePathReversal`, `MinimumDirectedPathTransfer`, `ClosestFirstArrowGeometry`;
- `BinaryTraceIncidence`, `BinaryActivationFamily`.

Selected additional supplier bodies:
- `ClosestFirstArrowSplice.reverse_required_arrival_trace` and `nodup_insert_fresh`;
- `Route.split_at_mem` in `ClosestFirstArrowGeometry`;
- `Route.prefix_of_mem` in `GeneralActiveWalkReduction`;
- `Route.terminal_step_of_nonempty` in `CommonDiscriminatingParents`.

The basic route/mark definitions and earlier semantic conversions remain the same objects used throughout the source packet. This list is a body-inspection inventory, not an assertion that every unrelated declaration in every transitively imported module was accepted.

## 7. Separate finite-bound check

Also read full `CanonicalFiniteBounds`, `FiniteProfileRegistry`, `RestrictedBudgetAndHonesty`, `EffectiveQueryEnumeration`, `RestrictedQueryBudgetBound`, `BinaryPhysicalGame` and the used G7 compatibility-port source.

The representative selector bound retains singleton parent flags and at most four marked bridges per unordered observed pair. The hidden-root tag argument counts:
- at most one root per observed–observed unordered pair;
- at most two possible root incidences per marked-pair selector;
- no singleton-selector root and no selector–selector root.

Thus the stated bounds n + 4 choose(n,2) selectors and 9 choose(n,2) hidden roots concern the one constructed representative, not a hidden-size assumption on the arbitrary original finite source.

The finite registry bound also agrees with the original manuscript: each unordered observed pair has three directional choices, an independent bidirected bit and four independent marked-bridge bits. With one parent flag per observed label this gives exactly 2^n · 96^choose(n,2) raw codes. The profile encoding is injective; filtering admissibility cannot increase that cardinality. This is not a claim that every raw code is an unmodified admissible original graph.

The query cardinality is the actual marginal-index count plus the two endpoint-excluding subset sums. Its bound is valid at n = 0 and n = 1 using natural subtraction. Full coverage gives this policy's 5 choose(n,2) queries, with HPL's prior quadratic result still attributed. The all-k upper need not be optimal at k = 0; the original target is then the singleton empty graph with a zero-query solution.

The sorted finite-coordinate enumeration is separate from noncomputable mathematical source/oracle specifications. The inspected G7 definitions retain one admitted source fitting the entire history, actual response-branch budget consumption and the original class target. The later hosted evidence does not verify this 4.33.1 port.

## 8. Remaining acceptance boundary

This author audit discharges no execution hold and is not a substitute for independent checking. The full upper statement still requires reconciliation of every mathematical supplier with the immutable root import inventory, review of exact library/API usage, and authorized actual elaboration and transitive axiom checking.

The reviewed source class remains arbitrary finite latent/selection DAGs with selection sinks, binary shared mechanisms and separate named soft-intervention indicators. The observations remain elementary population CI/conditional-invariance answers and the target remains the full marked HPL TCM class on all observed labels. No sample bound, intervention-count bound, hard-intervention claim, Gaussian substitute, full numerical-law preservation under compression or novelty conclusion is added.
