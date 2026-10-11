# Calibration to the literal last-child-exit prefix
Status: SOURCE_ONLY_UNCOMPILED_NOT_KERNEL_ACCEPTED. This is a Lean-facing proposal and missing-API specification. No target, parser, kernel, executable import, staging, cache admission, observer or Git mutation was used. Prior evidence is unchanged.

The draft uses the SAME supplied RootedBinary N, strict Calendar C, original parent registry H, gamma/common, rates and admitted Code. Put t=C.age v and es=G1OriginalCalendarDecomposition.originalExits N C t, exactly the compiler's existing Finset.toList. With k=max(es.idxOf ei)(es.idxOf ej)+1, define P=beforeBoundaryProgram...t ++ (es.take k).map exit, and U=(es.drop k).map exit ++ nodeOperations...t ++ calendarTail...t(filtered later original dates). The proposed literal_calendar_cut reuses actual_compiled_calendar_date_cut, original_date_scheduled and take_append_drop. Its list identity holds without edge membership; the last-child interpretation additionally needs both original sources equal v. Separate proposed lemmas give membership and k<=es.length. Distinct children are an explicit graph-witness field. No tie order or phase permutation is introduced.

SupportedSeparatedPrefixes quantifies every actual sourceProgram(P.take n) support for n<P.length. The proposed agenda_of_supported_prefixes converts that physical input to existing SeparatedAgenda by pure/bind support only. Its premise is not derived from calibration. The terminal state is excluded because it may first meet at v. Every remaining exit and every node operation at t stays in U.

RouteMeetingGeometry is graph-only: different taxa/child edges, both sources v, designated child membership on every original root-to-corresponding-tip EdgePath, and every common original ancestor reaches v. It contains no probability or desired law; calibration-to-this-witness is missing. BelowMeeting requires strict young-anchor age for a node, edge target or ancestral root. The proposed descendant_locations_ne/source_separated_of_below_meeting reuse SourceValid.original_descendant, so include all original-copy fibres through current-root mergers without fixed-selector or unchanged-count restrictions.

last_child_exit_colocates proposes actual terminal node-v locations GIVEN opposite child-edge locations before the exit segment. It reuses actual_exit_list_program, actual_exit_list_copy_location and actual_exit_location_list_hit. It proves neither that input premise nor independence. All these scripts remain uncompiled.

## Exact missing physical consumer
First formally connect the actual admitted natural paired COMMON calibration/readout to RouteMeetingGeometry. These providers do not already have a compiled calibration/observer type with that conclusion. A new Calibration field asserting the desired separator or output law would hide the gap.

After the graph witness, the required physical consumer has this signature. It is a specification, not an asserted or implemented theorem (usual Fintype/DecidableEq assumptions apply):

    (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (sample : Copy → X) (register : V → Bool)
    (i j : X) (v : V) (ei ej : E)
    (hg : RouteMeetingGeometry N i j v ei ej)
    (inside outside : Finset Copy)
    (hi : ∀ x ∈ inside, sample x = i)
    (hj : ∀ y ∈ outside, sample y = j) :
      SupportedSeparatedPrefixes N r inside outside
        (literalPrefix N C H gamma common v ei ej)
        (UnifiedLean.Source.SourceInitializedCalendar.initialCode N sample register)
      ∧ ∀ d ∈ (sourceProgram N r
          (beforeBoundaryProgram N C H gamma common (C.age v))
          (UnifiedLean.Source.SourceInitializedCalendar.initialCode N sample register)).support,
        (∀ x ∈ inside, copyLocation (state d) x = .edge ei) ∧
        (∀ y ∈ outside, copyLocation (state d) y = .edge ej)

This is full physical support on the literal original word. It is not a desired-law equality, arbitrary conditioned Old hypothesis, source reconstruction or scalar OriginalSpan field. The observational application separately requires actual retained-source/sample admission and nonempty disjoint labelled cohorts; empty panels satisfy the formal interface vacuously.

## Existing proof route and remaining links
1. Formalize the hand route argument: disjoint strict route prefixes below first shared node w can be completed to one COMMON assignment by shared continuation above w and unused bits. Both positive actual natural calibrations force w=v; binary degree yields the fixed children. Reuse EdgePath.directed/append, exists_edgePath_of_directed and original_tip_route_exists. The real source/readout/positive-support bindings still need a formal consumer.

2. Strengthen initialization/timing for EVERY partial prefix before t: selected sample leaves or processed node anchors strictly below t; edge targets and ancestral-root anchors strictly below t. Reuse actual_initial_natural, actual_time_natural, actual exit/node movement and sorted-date recursion. Existing actual_initialized_before_boundary_support yields BeforeReady, but its natural node bound is only <=t and does not exclude v before the meeting exits. The strictness upgrade remains missing. The graph/age draft then gives earlier-support separation, including merged roots.

3. At the pre-boundary endpoint combine strict anchors with BoundaryReady=EpochCompatible t t. Selected copies cannot be pending nodes or ancestral population. SourceValid.original_descendant extends the current edge towards the tip; rootedness extends towards the root. The graph witness forces the designated child on the same complete path. An interior time below t above both younger endpoints and EdgePath.active_unique identify the current edge. This path/dominance proof remains missing. Allow serial sample ages; do not use actual_activated_prefix_no_pending without its contemporaneous premise.

4. The partial exit segment is deterministic. exitLocationList leaves a child edge unchanged before its occurrence and sends it to node v afterwards. For n<k both children cannot have occurred: membership in es.take n forces first-index<n, contradicting n<max index+1 for the later child. Finset.nodup_toList gives literal Nodup. The finite first-index/non-hit proof is still unimplemented; terminal child memberships alone do not establish earlier-state separation. Do not infer equality under arbitrary tied permutations.

5. Combine segments with accepted actual_separated_agenda_append_iff or proposed all-prefix glue, then reuse actual_separated_joint_program_law. Full selected projectivity handles other retained copies without source deletion. No new probability/generator engine is needed.

## Explicit natural/G6/Rust boundaries
Fixed Code/register plus proved agenda gives the existing conditional full-view product. Varying entrants give mixtures of products. A natural erased product additionally requires the actual singleton initializer, INDEPENDENT modes, sampled-once private-bit bank, whole-prefix no-private-read and the same erased initialized selected input across draws. Erasure resets exactly declared private slots while preserving other slots, population and full carried forest. Arbitrary conditioned Old can change entering forests/locations, so no arbitrary-Old product follows.

G6 accepted a080/3fc retains supplied NonrootBigon, input/co-location, no-read, positive min exposure and residual-epoch premises. This draft does not discharge them. Span219 needs a supplied typed OriginalSpan; arbitrary interleaved/exclusive words are not coerced into that scalar type. Rust DTO, fitted witness and named observer refinement stay separate. No master closure, native representation, source admission or combined1575 acceptance is claimed.

Freeze validation is UTF-8/JSON/body/import/declaration-name/hash/allocated-size readback only. Independent static review and a separately approved kernel run remain necessary. Four oversized serialization preflights created no files; their counts are recorded.
