# Actual mixed original node batches and one parent-path boundary

Cloud G3, 8 October 2026, 05:08 UTC. **HAND/SOURCE candidate; primary review pending; compiler UNCHECKED. Original general G3 OPEN.** Nolan authorized continuation of the original proof programme. This packet preserves an additive consumer of the unchanged original graph, calendar, registry, rate bank and admitted source PMFs. No compiler, Actions, solver, simulation, API, source enumeration, QE or numerical control ran.

## Original contract and inherited checkpoint

General G3 still asks for input-only exact recognition of its declared coupled finite observations over all admitted finite positive sources, producing a finite positive witness on YES and a terminal NO on impossible input. Neither the passive quartet scalar image nor this selected-source adapter settles whole-fibre extraction or unknown-word completeness.

The [first-parent-join packet](../2026-10-08-cloud-g3-first-parent-join-0438z/HAND-SOURCE-CONTRACT.md), preserved at `dea47819891773a8d173d7766f17507db7a19740`, constructs the youngest common ORIGINAL parent-path source j, derives disjoint younger arms and distinct current arm populations below j, and derives h's selected descendant interface from the actual initialized original source. Its code and proof are still candidates awaiting their own review and compiler gate. The [grouped parent-path packet](../2026-10-08-cloud-g3-grouped-parent-path-0418z/HAND-PARENT-PATH-CONTRACT.md), preserved at `368bb25ca110982e9fd34c5fe106d47bdb66ea08`, supplies the actual interval selected row between unequal arm endpoints. Both original source files remain byte-identical.

The concrete missing gate addressed here is a **mixed same-date original node batch**: selected roots can be at one or two ending original nodes while others remain on longer original edges. Requiring all selected roots at one node would lose the genuine distinct-parent case. Replacing the whole original batch by one isolated pulse without deriving its selected law would assume the result.

The [new source](MixedParentBoundary.lean) derives a finite filtering law from the actual source support and projection theorems. It has three definitions and twelve theorem bodies, fifteen explicit named declarations. That is a static text inventory, not a Lean acceptance or axiom audit. No provider, archived candidate, workflow, source freeze or shared target is changed.

## 1. Actual original source types and physical node restriction

Use the finite `Nanuq.Source.RootedBinary N`, strict `GProgram.G5.Calendar C`, original parent registry R, actual gamma/common flags, positive original pair-rate bank r, and one source-valid entering `Code N sample` s. Write pi for `SourceFiniteProjection.projection N keep`. It contains the entire selected genealogy, original population location for every kept label, and the **whole original register**; it is an internal selected view, not automatically an admitted public observation.

For a finite set Q of original vertices, define the physical predicate

\[
 \operatorname{NodesWithin}(s,keep,Q)
 \quad\Longleftrightarrow\quad
 \forall x\in keep,\ \forall v,\
 copyLocation(s,x)=node(v)\ \Longrightarrow\ v\in Q. \tag{1}
\]

This is only a restriction on existing selected node locations. Selected copies may be on arbitrary original edges or in the original ancestral population. The remaining full source may contain arbitrary outside current roots, their old trees and their node/edge locations. Equation (1) supplies no distribution, independence, desired kernel or graph coverage field.

For an actual original node operation at v, inherited `actual_original_node_kernel_movement` proves `NodeMovement` on **every supported destination**. The already proved `node_move_never_creates_node` says that an absent node cannot be created: current owners at v enter an actual incoming original edge (or the root population), and all other locations stay fixed. Thus (1) holds in every supported destination. New `actual_node_support_nodes_within` and its literal-list induction implement this implication.

If v is outside Q, (1) also proves physical absence of the selected panel from the actual touched place `node(v)`. `actual_untouched_boundary_panel` consequently proves pi(d) = pi(s) in every positive-support destination d. This uses the actual current-owner independent pulse and SAME-register COMMON pulse definitions, not a deterministic approximation to them.

## 2. Principal actual mixed-node filtering law

Let `nodeListProgram(vs)` be the literal list of actual original node operations for an arbitrary list vs of original vertices, with its actual order retained. Let `vs|Q` be that list filtered to vertices in Q. Then

\[
 \operatorname{NodesWithin}(s,keep,Q)
 \ \Longrightarrow\quad
 sourceProgram(nodeListProgram(vs),s).map\,pi
 =sourceProgram(nodeListProgram(vs|Q),s).map\,pi. \tag{2}
\]

The source body `actual_node_list_filtered_law` proves (2) by induction on vs, using only actual PMFs:

* At a retained head v, the same original kernel executes on both sides. Every supported destination retains (1), so the induction applies to the true tail row.
* At a removed head v, actual absence gives pi(d) = pi(s) on its support. Apply the tail induction at d. The inherited **proved** `actual_source_program_projection` makes the complete tail selected row depend only on pi(d), hence it equals the tail row from s. The removed actual kernel integrates this constant normalized row to itself by `PMF.bind_const`.

No source fibre is conditioned or normalized separately. Null fibres contribute zero automatically. Repetitions in a generic node list are permitted; no chronology sorting, artificial node collapse or independence assumption is needed. For the actual compiler the finite node list remains the original same-date order.

Equation (2) is equality of a selected marginal. The whole source on the left still processes **every** original node, including all outside pulses. The shorter programme on the right need not have the same outside genealogy or a rich exterior observation law. In particular, it is not an interchangeable whole-source gadget merely because its selected marginal agrees.

## 3. Complete actual exits construct the mixed node set

Let `originalExits(N,C,b)` be the compiler's literal list of all original edge IDs with older source date b. For every original edge e the deterministic exit list satisfies

\[
 exitLocationList(originalExits(b),edge(e))=
 \begin{cases}
 node(source(e)),&C.age(source(e))=b,\\
 edge(e),&C.age(source(e))\ne b.
 \end{cases} \tag{3}
\]

The hit branch reuses `actual_exit_location_list_hit`; the new miss induction derives the other branch. Original edge IDs are retained, including parallel occurrences. Exits turn an edge location into a node; they do not change genealogy, current owners or the register. Later exits cannot change an already created node location.

For a finite set P of occupied original edges, construct

\[
 Q_b(P)=\{source(e):e\in P,\ C.age(source(e))=b\}. \tag{4}
\]

If `AtEdgePanel(state(s),keep,P)` holds, (3) and the inherited exact snapshot location theorem prove `NodesWithin` with Q_b(P) immediately after **all** original exits at b. This is `actual_original_exit_batch_nodes_within`; Q is extracted from physical original IDs and ages, not supplied as a desired node-law field.

Write V_b for the compiler's list of every original vertex dated b. The actual `boundaryOperations(b)` is definitionally `all original exits at b ++ nodeListProgram(V_b)`. Its exit programme is the deterministic admitted `exitCodeList`. Applying (2) to that actual post-exit state proves

\[
 sourceProgram(boundaryOperations(b),s).map\,pi
 = sourceProgram\bigl(originalExits(b)\,;++\,
                nodeListProgram(V_b|Q_b(P)),s\bigr).map\,pi. \tag{5}
\]

`actual_original_mixed_boundary_filtered_law` implements (5) without a separation or source-law equality premise. Both distinct arm endpoints may have date b. Then Q_b can have two different original vertices; both operations execute in their original order. If only one arm ends, the other panel remains on its older-ending original edge. Empty panels and empty Q_b are included.

For the constructed two parent positions below j, P is the inherited `occupiedParentEdges`. At an intermediate cut b < C.age(j), each v in Q_b is a source on a nonbridge original parent route. CutChild excludes a hybrid at v; rooted strict chronology excludes v = root because root is at least as old as j. The actual original indegree theorem therefore gives `inDegree(v)=1`. The new `actual_intermediate_ending_nodes_ordinary` derives this from graph/age facts; it does not assume ordinary ending nodes. At the join itself this ordinary/nonroot conclusion is deliberately not imposed: j may equal the original root.

## 4. Actual initialized focal pulse, with current owners and the SAME register

Let hy be a genuine original `Hybrid N`, and take the actual inherited original ordering H = R.parents(hy). Condition on a state s in the support of

\[
 sourceProgram(actualFrontierProgram(C.age(hy)),
               initialCode(N,sample,gamma_0)). \tag{6}
\]

For each selected sampled descendant of hy, the first-join checkpoint derives `copyLocation(s,x)=node(hy)` from the original bridge child, strict initialized frontier invariants and original descendant validity. It does not require unrelated live roots elsewhere in the larger source to occupy hy. The inherited full node-list binding then gives the selected law of the whole actual node batch at hy's date as the selected law of its single actual registered hy operation.

Unfold that **actual** original operation and boundary PMF. The new `actual_initialized_focal_node_batch_law` concludes exactly

\[
 sourceProgram(nodeOperations(C.age(hy)),s).map\,pi=
 \begin{cases}
 \delta_{\,pi(pulseCode(H,s,\,owner\mapsto s.register(hy)))},
       &common(hy),\\
 currentCoinPMF(AtNode(state(s),H.hybrid),gamma(hy)).map
       (coin\mapsto pi(pulseCode(H,s,coin))),
       &\neg common(hy).
 \end{cases} \tag{7}
\]

The independent product carrier is the actual **current AtNode owners**. Already merged original labels sharing one current owner are never independently recoined. Whole-register selected projectivity accounts for owners invisible in keep. COMMON reads the register stored in this same entering s. It does not draw a new coin after observing old history, average a posterior into a fresh prior or assume private seed independence. All proofs hold pointwise for each original gamma_0 and supported s; integrating against the actual correlated prefix/register law preserves the same conditioning.

Equation (7) is the smallest actual mixed-source focal pulse consumer. It uses no fitted hybrid ordering, new node or transformed graph.

## 5. One actual parent slice followed by its complete boundary

Use the existing two actual parent positions at age(h) <= t < age(entry), set P to their original IDs, and let

\[
 b=\min_{i=0,1} C.age(source(e_i(t))).
\]

The grouped-path checkpoint already derives b > t, original scheduled-date membership, endpoint bounds and the physical silence of every selected operation in `parentPairSliceProgram`. It proves that the whole selected row of this literal interleaved slice equals the actual original time kernel of duration b-t. It stops before b's boundary.

Let B_b(P) be the right-hand **actual original** boundary sublist in (5). The new concrete law is

\[
 sourceProgram\bigl(parentPairSliceProgram\,;++\,boundaryOperations(b),s\bigr).map\,pi
 = sourceTimeKernel(b-t,s).bind\bigl(
       d\mapsto sourceProgram(B_b(P),d).map\,pi\bigr). \tag{8}
\]

`actual_parent_slice_then_boundary_law` implements (8). First append the true boundary using the actual PMF programme recursion. Proved source projectivity allows the slice selected-row identity to be transported through this same future boundary; it does **not** infer equality of the hidden full-state distributions. Every supported actual time-kernel destination retains P by the original copy-population law. Apply (5) on precisely those supported d to obtain (8).

Thus the interval and mixed boundary consumer can retain the selected full old forest and entire original register while the full original outside process runs. There is no supplied desired Gamma/observation/source-law equality in its hypotheses.

For separated arm iteration, apply (8) below j and use the prior first-join separator only where its actual location hypotheses hold. The generic equality (8) also exists at a joining boundary, but it does not prove that panels remain separated after pooling. The grouped fork programme from the earlier packet stops after the join's exits and before its node batch; (8), which includes the entire boundary, does not redefine that terminal interface.

## 6. Actual contribution and explicit remaining gates

The packet supplies substantive mixed-boundary source bodies and a derivation of the true focal pulse law in a larger naturally initialized original source. Its law statements concern the SAME graph, original edge IDs, positive rate bank, registry and whole stored register. It preserves genealogy/current-owner semantics and handles unrelated equal-aged endpoints.

| Gate | Exact status after this packet |
|---|---|
| First common original vertex, disjoint younger arms and distinct positions below j | Prior source candidate c28c4a7f, primary/compiler acceptance separate |
| Actual mixed node support and removal of foreign nodes from selected law | New proof bodies (1)-(2), HAND/SOURCE candidate and compiler UNCHECKED |
| Complete original exits and selected mixed boundary row | New derived bodies (3)-(5), same status |
| Natural initialized focal current-owner pulse/SAME COMMON bit | New concrete body (7), same status |
| Actual unequal-endpoint slice plus complete boundary | New concrete body (8), same status |
| Supported post-boundary selected locations equal the next constructed original `parentPosition` on each arm | Still an explicit source/graph assembly gate; identify the unique incoming original edge along the extracted path, including simultaneous endpoint dates |
| Whole disjoint-arm agenda through last selected exit, silent suffix after pooling | Still requires iteration of exact slice/boundary frontiers and a precisely stopped separator |
| Integrated original-rate Kingman operators and grouped source word/scalar recurrence | Earlier hand route; formal generator/reindexing/whole-word assembly still separate |
| Full outside genealogy or arbitrary rich exterior observation replacement | Not concluded by selected marginal equality |
| Original general G3 coupled exact recognition / terminal NO | OPEN |

No mathematical control or executable verification supports the new code. The static checks authenticate files, quoted source/API identities, declaration inventory and links only. Imports require later isolated overlay of the two unchanged earlier Cloud drafts and inherited G1/baseline providers; no compilation or build enrollment is requested now. Dependent registry/subtype rewriting in (7), definition unfolding and PMF callback elaboration in (8) remain compiler questions, even though no new source-law/probability premise was introduced.
