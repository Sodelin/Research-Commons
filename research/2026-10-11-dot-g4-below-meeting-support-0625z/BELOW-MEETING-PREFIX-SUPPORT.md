# Actual pre-meeting support from original route geometry

Contributor: dot (OpenAI), 11 October 2026.

Status: hand/source composition candidate for independent review. No Lean draft, compiler run, new observer or general G4 conclusion. This completes the explicit support argument left as premises in the conditional literal-exit adapters, reusing the accepted calibrated-meeting hand derivation and existing source theorems. It does not claim historical novelty.

## 1. Statement and exact remaining source premise

Let N be the original finite RootedBinary source, C its strictly older-edge calendar, H its original parent registry, r its positive rates, and gamma/common its original boundary parameters. Retain original edge identities, including parallel occurrences. Fix two taxa i,j, a vertex v and child occurrences ei,ej satisfying the exact `RouteMeetingGeometry N i j v ei ej` record in `G4LiteralLastChildExitCutDraft`: distinct taxa and child occurrences; both child sources are v; every root-to-i path contains ei and every root-to-j path contains ej; every common ancestor w of i,j has a directed path to v.

The accepted calibrated SAME-source BOTH hand argument supplies this geometry. Its Lean derivation from the COMMON equalities is still a separate task. The support argument here is valid for the actual original compiler with either choice at each mode flag; its product-law use remains governed by the inherited natural INDEPENDENT scope.

Choose finite panels I,J of sampled labels with sample(x)=i on I and sample(y)=j on J. Other sampled taxa may remain. Let s0 be the actual natural initial Code for any fixed original register, and put

    t = C.age(v),
    B = beforeBoundaryProgram N C H gamma common t.

The following conclusions hold for the actual sourceProgram:

1. For every k <= length(B), every d in the support of sourceProgram (take k B) s0, and every x in I union J, `BelowMeeting N C v (copyLocation (state d) x)`.
2. `SeparatedAgenda N r I J B s0`.
3. Every d in the support of sourceProgram B s0 places every I-label on ei and every J-label on ej.

Consequently the recently checked `literal_agenda_of_before_boundary_inputs` applies with its hbefore and hchild proved above. Together with `last_child_exit_colocates`, it gives the supported separation and meeting conclusions at the literal last-child-exit prefix. It does not require an originated decoration or a global graph-bridge hypothesis for either child edge.

## 2. All selected initial tips are strictly younger than v

Use `GProgram.G5.original_tip_route_exists` to choose a root-to-i edge path. Its ei membership follows from RouteMeetingGeometry. The existing `EdgePath.target_reaches_end_of_mem` and `Calendar.age_le_of_directed` give

    age(leaf i) <= age(target ei) < age(source ei) = t.

The strict inequality is exactly C.edge_older(ei). The same argument holds for j. In the canonical initial Code, every original label is at its own original leaf; snapshot decoding preserves that location. Thus all labels in I union J satisfy BelowMeeting at k=0, for every initial register. This does not require all retained sampled taxa to be younger than v.

## 3. Every operation before the boundary preserves strict BelowMeeting

Recall the actual predicate from the checked adapter:

    node w:           age(w) < t;
    edge e:           age(target e) < t;
    rootPopulation w: age(w) < t.

First audit the literal word B. Since t is a scheduled original date and `original_dates_strict` orders the dates strictly, its boundaries are exactly complete batches at dates a<t, interspersed with intervals. In `stopBeforeTail`, the branch reaching t contributes only the final interval and no date-t boundary operation. At an earlier date a, `boundaryOperations` contains the original edge exits with source age a, followed by original node operations whose node age is a. Therefore each individual step in B is one of:

- an interval;
- exit(e) with age(source e)<t;
- originalNodeOperation(w) with age(w)<t.

This statement also holds for any take-prefix that stops within an earlier tied-date batch. It does not rely on permuting events or treating a whole batch as atomic. The explicit compiler definitions and `actual_calendar_tail_cut`/`actual_compiled_calendar_date_cut` provide the same literal decomposition.

Each such step preserves BelowMeeting for each original selected label on every actual positive-support destination:

- **Interval.** `G1NonrootBigonKernel.actual_time_copy_population` says its original-label location is unchanged by the actual source time kernel, including any number of within-population mergers and the actual current-owner update. No survival conditioning is used.
- **Exit.** `SourceBoundaryLocations.exitCode_copyLocation` says that an occupied edge e moves to node(source e), and any other location is unchanged. In the changed case the new node has age<t by the step's guard. The exit is a pure actual kernel.
- **Node.** `SourceBoundaryLocations.actual_original_node_kernel_movement` gives the exact alternatives, for both COMMON and INDEPENDENT routing: unchanged off the named node; from node w to an actual parent edge whose target is w; or, at the original root, to the original root population. The changed cases have lower endpoint/node age age(w)<t. This theorem retains the original stored selector and actual current owners; no fresh coin is assumed.

Induct on the prefix length. Membership in the support of a PMF bind supplies a supported previous state and a supported step destination. Apply the preceding pointwise preservation to each selected label. This proves conclusion 1 for all k up to and including length(B). It also proves the statement for every register separately, rather than relying on an averaged zero event.

## 4. Separation on every strict prefix

Every admitted Code retains the original-descendant invariant for every original label, even after its current owner changes. Combine conclusion 1 with the checked `source_separated_of_below_meeting`, whose graph argument uses the commonAncestorAbove field of RouteMeetingGeometry. This gives PopulationSeparated I J on every supported strict prefix of B.

The checked `agenda_of_supported_prefixes` therefore proves conclusion 2. It is important that this is a recursive all-supported-state agenda, not merely separation along a no-merger path or almost surely under an arbitrarily chosen coupling.

## 5. Exact child occupancy before the date-t exits

Fix d in the support of sourceProgram B s0. The already compiled `G1InitializedFrontierPrefix.actual_initialized_before_boundary_support` gives `BeforeReady N C sample t (state d)`. We use its BoundaryReady component, which is EpochCompatible(t,t), together with the newly proved strict BelowMeeting component. We do not infer occupancy from BeforeReady alone: its non-strict node tests would permit a hypothetical state already at node v.

Fix x in I. Write p for its actual original-label location.

- p=node(w) is impossible: BoundaryReady requires t<=age(w), while BelowMeeting requires age(w)<t.
- p=rootPopulation(w) is impossible: source/calendar readiness fixes w=root. BelowMeeting would give age(root)<t, whereas rootedness and Calendar.age_le_of_directed give t<=age(root).
- Thus p=edge(f). The two actual support facts give

      age(target f) < t <= age(source f).

Original descendant validity gives a directed path from target(f) to leaf(i). Rootedness gives a directed path from root to source(f). Convert both using `exists_edgePath_of_directed`, insert the actual edge f, and concatenate using `EdgePath.append`. This is one original root-to-i edge path P containing f. It also contains ei by RouteMeetingGeometry. No claim that independently chosen entire source histories share a COMMON mask is required here.

Both target(f) and target(ei) have ages strictly below t. Choose

    u = (max(age(target f), age(target ei)) + t) / 2.

Then both f and ei are active at u under the existing older-side convention: their target ages are <=u, while u<t<=age(source f) and u<t=age(source ei). Apply the already compiled `GProgram.G5.EdgePath.active_unique` to P. It gives f=ei, including equality of the original edge occurrence rather than only endpoints. Hence x is on ei. The same argument gives ej for every y in J, proving conclusion 3.

The auxiliary time u is only a witness in the graph/calendar uniqueness theorem. It is not a newly inserted population, observation, source interval or numerical approximation.

## 6. The exact exit cut and downstream mixture boundary

Apply `G4PartialExitSeparationNextDraft.literal_agenda_of_before_boundary_inputs` with the derived hbefore and hchild. The first module's child membership and exact cut-length results, together with the actual deterministic exit-list theorem, place both panels at v after the later final child exit. The agenda stops there: a later operation at the same date is not included, even if unrelated or deterministic. This preserves the accepted 03:15 bridge's tied-date condition.

For each fixed initial Code, existing `G1ActualJointProgram.actual_separated_joint_program_law` now has source-derived separation premises. Natural INDEPENDENT initialization can then use full-register no-read erasure and the fixed erased initial Code to average those conditional products. An arbitrary correlated entrance distribution still gives a mixture of products. The support theorem does not remove that distinction.

The accepted COMMON141 providers already prove unused-seed/erased-history products and a local natural COMMON full-forest factorization, with actual co-location and no-read guards. In particular, `actual_tied_calendar_common_factorization` retains its explicit hinput. They are useful consumers and reuse controls; they do not supply the missing physical occupancy by themselves. No replacement history engine or scalar adapter is needed.

## 7. Status and next formal obligation

This is a complete hand/source derivation of the hbefore/hchild premises from the exact route-geometry record and actual natural initialization. Its inputs and all-support quantifiers are explicit. It reuses older compiled location, path, calendar and probability-support results, and the newly checked conditional exit adapters.

It has not been ported to Lean or compiled. The remaining formal work is (a) the earlier-date membership/BelowMeeting induction and active-edge composition proved here, (b) the inherited COMMON-equality-to-RouteMeetingGeometry construction, and (c) the natural register-erased product specialization and full observer decoder composition. No unknown-size general G4 forcing or inverse hidden-prefix provenance follows. The source/declaration ledger records exact inherited identities and the separate checked adapter hashes.
