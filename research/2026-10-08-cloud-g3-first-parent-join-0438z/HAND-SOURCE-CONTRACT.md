# First common original parent-path vertex and actual focal frontier

Cloud G3, 8 October 2026, 04:38 UTC. **HAND/SOURCE candidate, independent review pending; new Lean source compiler UNCHECKED.** Contributor and publisher: Cloud G3 / OpenAI, under Nolan's continuing G programme instruction and root's bounded assignment. The original source grammar, graph, rates, register and compiler are unchanged.

## Original question and this exact contribution

Original general G3 asks for exact source recognition from its declared finite observations, with an actual finite positive source witness on YES and a terminal NO on impossible inputs, in both inherited modes and across arbitrary finite admitted sources and the original coupled menus. Whole-fibre extraction and unknown-length completeness remain open. The accepted passive quartet image and hybrid-count statements do not settle that question.

The [previous grouped parent-path packet](../2026-10-08-cloud-g3-grouped-parent-path-0418z/HAND-PARENT-PATH-CONTRACT.md) derived the actual selected source row between consecutive physical arm endpoints even when those endpoints differ. Its next missing graph gate was extraction of the first join and proof of arm separation. The present packet supplies that gate directly from the two existing original paths. It also derives the focal current-root interface from actual initialization rather than assuming every root in the larger source occupies the focal node. The full mixed batch, whole-arm generator regrouping, scalar attachment and general recognition obligations remain separate.

The new [Lean prototype](FirstParentJoin.lean) has three definitions and twenty-five theorem bodies, twenty-eight named declarations in total. This is a static inventory, not a compiler or axiom audit. It imports the unchanged previous `GroupedParentPathCalendar` draft and inherited providers. The prototype is outside all shared source freezes and has not been compiled. None of the source statements assumes a desired source-law equality, route coverage, independent entering law, fitted rate or graph replacement.

## 1. Actual source and route data

Fix the inherited finite `RootedBinary N`, strict `Calendar C`, actual original parent registry `R`, positive pair-rate bank `r`, and `CutChild N`. At a genuine original hybrid h, use its two distinct original incoming edge occurrences `H.parent false` and `H.parent true`. In the actual compiler application set **H = R.parents hy**, so the site's parent ordering and its stored COMMON bit are the original ones. The graph lemmas themselves also hold for either legitimate ordering of the two actual parents.

Fix an actual component entry `entry` with `ParentCalendar.IsComponentEntryFor N entry h`. Inherited `parentRoute_path` and `parentRoute_nonbridge` give two finite original edge-ID paths

\[
 P_0,P_1:\quad entry\longrightarrow h.
\]

Each finishes with its named original parent occurrence. Parallel occurrences are distinct even if their endpoints agree. `CutChild` and nonbridge membership exclude a hybrid at the source of every path edge. The actual nonhybrid indegree bound, including the root case, then supplies uniqueness of incoming edge occurrences at those source vertices. This is the previously proved `cut_child_nonbridge_incoming_unique`, not a new graph-to-word premise.

No claim here says an arbitrary original focal blob is a literal `OriginalSpan` bigon. The [distinct-parent obstruction](../2026-10-08-cloud-g3-original-span-count-0347z/HAND-SOURCE-CONTRACT.md) remains valid: suppressing side branches for a selected marginal does not manufacture two parallel original arcs.

## 2. Constructing the first joining vertex and the actual arm lists

For each original list P_b, let S_b be its finite set of **source vertices**, retaining the original edge IDs in P_b. Let S = S_0 intersect S_1. The vertex h is excluded from these sets by strict edge ages. The original entry belongs to both: the path cannot be empty because its final original parent edge proves age(h) < age(entry). Thus S is nonempty.

Choose j in S minimizing C.age over S, using the inherited finite `Finset.exists_min_image` theorem. The minimization is over actual finite path data, not over source kernels, observations or a hypothesized factorization. Strict path ages give

\[
 C.age(h)<C.age(j)\le C.age(entry). \tag{1}
\]

The new source `actual_first_join_exists`, `firstParentJoin`, `actual_first_join_spec` and `actual_first_join_age_window` implement this construction. A youngest common vertex is unique: two distinct vertices on the same directed path have strictly ordered ages. The implementation only needs the chosen minimizer and does not introduce a uniqueness premise.

Use the existing `ComponentCalendar.EdgePath.split_at_original_edge` at a listed edge whose source is j on each path. It derives lists

\[
 P_0=L_0\mathbin{+\!+}A_0,\qquad P_1=L_1\mathbin{+\!+}A_1,
\]

where L_b is an original path entry to j and A_b is an original path j to h. The lists A_b are nonempty by (1). Every edge of L_b is nonbridge. Reverse each L_b into the inherited rootward `UpPath`. Since j is the source of an actual nonbridge edge, the original CutChild incoming-edge uniqueness theorem applies at the start and at every subsequent kept-edge source. `UpPath.unique_from_kept_source` therefore proves L_0 = L_1. Denote this actual common stem by L.

For a vertex v that is a source on both A_0 and A_1, minimization gives age(j) <= age(v); the path from j gives age(v) <= age(j). Equality and strict edge ages force v = j. The younger arm interiors are therefore disjoint original vertex sets. Their only shared target endpoint is h. Neither arm has a hidden hybrid at any source, and j is nonhybrid. This derives the full graph-level contract

\[
 P_b=L\mathbin{+\!+}A_b,\qquad A_b:j\to h,
 \qquad A_0\cap A_1\text{ internally empty}. \tag{2}
\]

`actual_parent_routes_shared_stem_disjoint_arms` proves the two literal list decompositions, actual path proofs and absence of any common arm source other than j. It does not assume an arm decomposition or a projection law as a field. These lists contain original edge occurrences only; no new edge, vertex, duration or rate is fitted.

## 3. Actual current populations are distinct until joining

Take age(h) <= t < age(j). Existing `parentPosition` chooses the unique active original edge e_b(t) on P_b, using the actual older-side convention age(target e) <= t < age(source e).

Suppose e_0(t) = e_1(t) = e. If target(e) were h, strict ages exclude any earlier prefix edge entering h, so e would equal both distinct named original parents, a contradiction. Otherwise path continuity puts target(e) in both source-vertex sets. Minimality gives age(j) <= age(target e) <= t, also a contradiction. Hence

\[
 e_0(t)\ne e_1(t)\qquad(age(h)\le t<age(j)). \tag{3}
\]

The new `actual_parent_positions_distinct_before_join` derives (3) from path membership, distinct original parent IDs, continuity and calendar ages. It does not assume distinct populations.

The same path order shows that each active edge's older source lies at or below j in age: the edge cannot precede a still older listed vertex in the reverse traversal while t is below that vertex. Therefore the existing constructed next cut

\[
 t' = \min_b C.age(source(e_b(t)))
\]

obeys t < t' <= age(j). `actual_position_source_age_le_join` and `actual_next_parent_cut_le_join` prove the upper bound; the previous packet already proves strict progress, actual scheduled-date membership and the weaker endpoint bounds needed for source compression. At t' = age(j) the slice ends **before** that cut's exits and node operations; its two original child-edge populations remain distinct. The subsequent join batch can pool them. No separation after pooling is claimed.

## 4. Actual initialized focal frontier in a larger original source

A generic `SourceValid` state alone permits premature edge entry or dormant internal nodes. The natural interface must come from the original initialized compiler. Fix **one actual complete original register** gamma0 and a state s in the support of

\[
 sourceProgram(actualFrontierProgram(C.age(h)), initialCode(N,sample,gamma_0)). \tag{4}
\]

The inherited `actual_initialized_frontier_support` proves on every such state: `AfterExits` at h's age, `NaturalNodes` for the original sampling labels, and strict past entry of occupied edges. In particular, any remaining original edge has its older source strictly above h's age, while its target was strictly entered earlier. All exits at that date have already occurred; the h node batch has not.

The actual binary outdegree of h constructs its unique original child edge f. `CutChild` proves f is a bridge. For an original sampled label below h, `descendant_via_unique_child` puts its leaf in f's target-side descendant component. Original descendant validity and the preceding age invariants force its copy location to be node h:

* If the location is a node v on f's target side, it is a descendant of target(f), strictly younger than h, contradicting the pre-node readiness age. If v is on the source side and reaches the sampled descendant, the actual bridge-crossing theorem gives v reaching h. NaturalNodes excludes a dormant older internal node; a dormant original leaf here would belong simultaneously to the two bridge sides. Strict directed ages then force v = h.
* If it is edge e with target(e) on f's source side, target(e) reaches h, contradicting the strict earlier target-entry bound. If target(e) is on the target side, either e = f and the full exit batch has removed it, or e differs from f and its source is also on the target side. In the latter case that source is younger than h, contradicting the post-exit source-age bound.
* A root-population location would require root age <= h age. A genuine original hybrid is nonroot, so rooted strict chronology gives h age < root age.

Conversely, a copy at node h has an original sampled descendant of h by the inherited `SourceValid.original_descendant` condition. Thus, on the actual initialized support,

\[
 copyLocation(s,x)=node(h)
 \quad\Longleftrightarrow\quad
 N.graph.DReach(h,N.leaf(sample(x))). \tag{5}
\]

The prototype implements the bridge-source argument and derives f and its bridge status in `actual_initialized_hybrid_descendant_frontier`; `_iff` implements both directions of (5). This does not assume an all-live-roots-at-h condition or independently initialized entering forest. Every original outside root, opaque carried tree and register bit remains in s. Focal current blocks are the existing live owners visible in the selected descendant view, not four freshly separated original-copy roots. Integrating (5) over the genuine original register PMF is valid because it holds for each fixed gamma0 and each actual supported prefix; it does not replace the register by a new marginal or assert posterior independence.

## 5. Mixed actual pulse and the derived single-slice joint source law

For a selected descendant copy at node h, its existing current owner belongs to `AtNode s h`. The actual pulse routes it to

\[
 edge\bigl(H.parent(coin(ancestor_s(x)))\bigr). \tag{6}
\]

`actual_selected_pulse_owner_bit` derives (6) directly from the admitted `pulseCode`, exact snapshot decoding and inherited current-owner pulse routing. Already merged copies with the same current owner receive the same bit. In INDEPENDENT mode the actual Bernoulli product is on those current owners; the existing full selected-pulse projectivity theorem supplies its exact law. In COMMON mode the coin in (6) is the **same stored** s.register(h), giving `actual_selected_common_pulse_bit`. No fresh Bernoulli draw is performed after conditioning on the old past or a prefix outcome.

A root already on any original edge is unchanged by an original node operation, even when other current roots in the same state lie at h or at another node. The new `actual_node_kernel_keeps_existing_edge` follows from the actual original node-movement theorem on kernel support. This is a mixed-state support fact. It does **not** yet identify a complete same-date mixed node/exit batch with an isolated h pulse; that probability consumer remains open.

Condition on the actual entering state and actual pulse outcome/owner allocation. Consider the two original-label panels I_0 and I_1 currently on e_0(t) and e_1(t), respectively. They may contain many labels but preserve their existing current blocks and old subtrees. Their positions are a physical state premise; no entering product or desired law is assumed. Equation (3) gives actual `PopulationSeparated`. The constructed next slice contains actual original intervals, outside exits below t', and original node operations. The previous weaker endpoint theorem proves these operations are `EdgeSafeStep` for **each singleton** {e_b(t)}. On every actual positive-support destination the inherited movement/merger lemmas preserve each singleton population panel. Induction derives `SeparatedAgenda` on every prefix of this literal slice.

The existing full-genealogy source theorem can consequently be applied with its separator discharged:

\[
 (sourceProgram(slice,s)).map(jointProjection(I_0,I_1))
 = independentProduct\bigl(
 selectedProgram(I_0,slice,projection(I_0,s)),
 selectedProgram(I_1,slice,projection(I_1,s))\bigr). \tag{7}
\]

`actual_parent_slice_joint_law` implements (7), using `actual_two_edge_safe_agenda_separated` and `actual_distinct_edge_panels_separated`. It is conditional on one entering Code s, hence one correlated old forest and one full original register. The cloned registers on the two right-hand projections are the same deterministic register at this conditional stage; (7) does not make the random original register independent of itself or of an observed past.

Outside original operations continue executing. The two panels in (7) are the **selected arm panels**, not the entire outside genealogy. A nonfocal root can merge with one arm and still carry exterior labels; source pruning makes its effect on the selected law consistent. Nothing here factors all exterior observations, redraws conditional COMMON bits, or gives an arbitrary rich exterior observer the selected population/register view. Equation (7) is a whole selected genealogy/population/register statement, stronger than a pair-survival scalar and weaker than full original outside independence.

## 6. Source admission, edge cases and remaining gates

All original graph edges and their rates/durations persist. The actual first join may equal the component entry, and the older common stem L may be empty. Parallel parent edges are retained as distinct IDs and are separated for every t strictly below their common source age. Equal ages at unrelated original vertices do not affect the finite minimizer or path strictness. Either selected arm panel may be empty. A slice that ends at j includes its interval and stops before exits, so its separation proof does not accidentally extend past the pooling operation. Every statement applies to an arbitrary finite copy carrier and opaque old genealogy; a numerical sample cap is not a substitute for current-root initialization.

The [earlier nine-vertex actual distinct-parent example](../2026-10-08-cloud-g3-original-span-count-0347z/HAND-SOURCE-CONTRACT.md) is covered: h's parents start at distinct s0 and s1, j = u. The actual incoming bridge r-to-u makes the component entry u, so L is empty; r is not an admissible entry for this nonroot component. The new proof constructs paths from actual originals; it never tries to declare that h already has a same-source `NonrootBigon`.

| Original obligation | Present status | Concrete remaining action |
|---|---|---|
| First shared original vertex and disjoint younger arms | New hand proof and source bodies, review pending, compiler UNCHECKED | Review exact graph/path proof; no build requested |
| Actual selected h interface from natural original initialization | New support proof and source bodies, same status | Review bridge-source case analysis |
| Full two-panel selected law of one unequal-endpoint slice | New derived separator consumer, same status | Review single-slice source support and joint theorem application |
| Mixed original boundary batches at every intermediate arm endpoint | Support primitive only; full law consumer still open | Serialize actual ending-edge exits and ordinary node entry, including foreign same-date operations |
| Whole disjoint arm agenda through the last selected exit at j | Still open formally | Iterate slice/batch consumers; stop separator at the last selected join exit and treat the silent suffix separately |
| Population-to-arm generator transport and integrated Kingman law | Inherited providers plus earlier hand argument; formal assembly open | Prove exact original-rate integrated arm operators and current-root reindexing |
| Actual grouped source word to passive quartet cocycle/count bound | Earlier accepted hand applicability, formal source adapter still incomplete | Attach complete grouped arm law to unchanged scalar/count core |
| Original general G3 recognition and terminal NO | OPEN | Whole-fibre positive extraction, coupled menus and unknown word/template completeness |

No compiler, Actions, source enumeration, QE, stochastic simulation, solver/API or numerical control ran. No prior packet, provider, frozen source, workflow, shared navigator or private product code changed. Publication preserves a candidate; it does not establish its truth. This packet is the graph/frontier/single-slice continuation of `368bb25`, not a replacement for its remaining whole-arm source law.
