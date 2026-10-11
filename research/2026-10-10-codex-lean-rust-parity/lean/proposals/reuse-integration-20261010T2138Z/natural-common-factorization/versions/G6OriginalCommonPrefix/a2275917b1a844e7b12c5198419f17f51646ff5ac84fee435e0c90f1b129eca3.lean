import UnifiedLean.G6.PrivateRegisterCalendarPrefix
import UnifiedLean.Source.SourceInitializedCalendar

/-!
Codex Lean reuse, 10 October 2026. PROPOSAL; no kernel receipt yet.

Proof-only compatibility derivative, 11 October 2026, of frozen 68e0130b.
The first compiler attempt exposed left-associated append membership and
singleton/nil normalization; definitions, statements and imports are unchanged.
The ce9ec8df retry additionally needs a data-only local List.casesOn prefix
type, without the earlier hypotheses being generalized into its match.

The older calendar providers already exclude private reads at every strictly
earlier original date. This adapter ends the actual compiler prefix within the
selected date's node batch, immediately before a named original node. Both
splits below are literal splits of the unchanged compiler lists. Their Nodup
properties, rather than a supplied no-read law, exclude an earlier occurrence
of that same private node. Every original exit and tied earlier node remains.
No calendar engine, reordering, population-support or seed law is introduced.
-/
namespace GProgram.G6.OriginalCommonPrefix

set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.G6.PrivateRegisterBoundary
open UnifiedLean.G6.PrivateRegisterProgram
open UnifiedLean.G6.PrivateRegisterCalendar
open UnifiedLean.G6.PrivateRegisterCalendarPrefix
open scoped Classical NNReal

variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]
variable [Fintype Copy] [DecidableEq Copy]

/-- Only existing calendar constructors, stopped before the selected node. -/
noncomputable def beforeNodeWord (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (site : V) (pre : List ℝ) (nodesBefore : List V) :
    List (ProgramStep N) :=
  (match pre with
   | [] => []
   | a :: dates => boundaryOperations N C H gamma common a ++
       calendarTail N C H gamma common a dates ++
       [.interval (Real.toNNReal (C.age site - finalDate a dates))]) ++
    ((Finset.univ.filter (fun e : E => C.age (N.graph.source e) = C.age site)).toList.map
      (fun e => .boundary (.exit e))) ++
    (nodesBefore.map (fun v => .boundary (originalNodeOperation N H gamma common v)))

private theorem calendarTail_before_last_boundary
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (a site : ℝ) (dates : List ℝ) :
    calendarTail N C H gamma common a (dates ++ [site]) =
      calendarTail N C H gamma common a dates ++
        [.interval (Real.toNNReal (site - finalDate a dates))] ++
          boundaryOperations N C H gamma common site := by
  induction dates generalizing a with
  | nil => simp only [List.nil_append, calendarTail, finalDate, List.append_nil,
      List.cons_append]
  | cons d dates ih =>
      simp only [List.cons_append, calendarTail, finalDate, List.append_assoc]
      rw [ih d]
      simp only [List.append_assoc, List.cons_append, List.nil_append]

/-- The prefix is literally part of the original compiled agenda. Finset.toList
order is retained; no within-phase permutation or symbolic-slot claim is used. -/
theorem actual_compiled_before_node_split
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (site : V) (pre post : List ℝ) (nodesBefore nodesAfter : List V)
    (hdates : sortedOriginalDates N C = pre ++ C.age site :: post)
    (hnodes : (Finset.univ.filter (fun v : V => C.age v = C.age site)).toList =
      nodesBefore ++ site :: nodesAfter) :
    compiledCalendarProgram N C H gamma common =
      beforeNodeWord N C H gamma common site pre nodesBefore ++
        [.boundary (originalNodeOperation N H gamma common site)] ++
        nodesAfter.map (fun v => .boundary (originalNodeOperation N H gamma common v)) ++
        calendarTail N C H gamma common (C.age site) post := by
  rw [compiledCalendarProgram_split_at_guard N C H gamma common (C.age site) pre post hdates]
  cases pre with
  | nil =>
      simp only [List.nil_append, calendarTail, List.append_nil, beforeNodeWord,
        boundaryOperations, hnodes, List.map_append, List.map_cons,
        List.cons_append, List.append_assoc]
  | cons a dates =>
      simp only [List.cons_append]
      rw [calendarTail_before_last_boundary]
      simp only [beforeNodeWord, boundaryOperations, hnodes, List.map_append,
        List.map_cons, List.cons_append, List.nil_append, List.append_assoc]

/-- The actual earlier dates and the actual tied node prefix do not inspect the
selected original site's register. This includes zero intervening intervals. -/
theorem actual_before_node_noPrivateWordRead
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (site : V) (pre post : List ℝ) (nodesBefore nodesAfter : List V)
    (hdates : sortedOriginalDates N C = pre ++ C.age site :: post)
    (hnodes : (Finset.univ.filter (fun v : V => C.age v = C.age site)).toList =
      nodesBefore ++ site :: nodesAfter) :
    NoPrivateWordRead N {site}
      (beforeNodeWord N C H gamma common site pre nodesBefore) := by
  have hd : (pre ++ C.age site :: post).Nodup := by
    rw [← hdates]
    exact (original_dates_ordered N C).2
  have hn : (nodesBefore ++ site :: nodesAfter).Nodup := by
    rw [← hnodes]
    exact Finset.nodup_toList _
  have hdateAbsent : C.age site ∉ pre := by
    have h := (List.nodup_cons.mp (List.nodup_middle.mp hd)).1
    intro hm
    exact h (List.mem_append.mpr (Or.inl hm))
  have hnodeAbsent : site ∉ nodesBefore := by
    have h := (List.nodup_cons.mp (List.nodup_middle.mp hn)).1
    intro hm
    exact h (List.mem_append.mpr (Or.inl hm))
  have hboundary (d : ℝ) (hd : d ∈ pre) :
      NoPrivateWordRead N {site} (boundaryOperations N C H gamma common d) := by
    apply boundaryOperations_noPrivateWordRead
    intro v hv he
    have hv' : v = site := Finset.mem_singleton.mp hv
    subst v
    exact hdateAbsent (by rw [he]; exact hd)
  have hp : NoPrivateWordRead N {site}
      (List.casesOn pre ([] : List (ProgramStep N))
       (fun a dates => boundaryOperations N C H gamma common a ++
           calendarTail N C H gamma common a dates ++
           [.interval (Real.toNNReal (C.age site - finalDate a dates))])) := by
    cases pre with
    | nil => intro op hop; exact False.elim (List.not_mem_nil hop)
    | cons a dates =>
        have hb := hboundary a List.mem_cons_self
        have ht : NoPrivateWordRead N {site} (calendarTail N C H gamma common a dates) := by
          apply calendarTail_noPrivateWordRead
          intro d hd v hv he
          have hv' : v = site := Finset.mem_singleton.mp hv
          subst v
          exact hdateAbsent (by rw [he]; exact List.mem_cons_of_mem a hd)
        intro op hop
        change op ∈ (boundaryOperations N C H gamma common a ++
          calendarTail N C H gamma common a dates) ++
            [.interval (Real.toNNReal (C.age site - finalDate a dates))] at hop
        rw [List.append_assoc] at hop
        rcases List.mem_append.mp hop with hboundaryMem | htailMem
        · exact hb op hboundaryMem
        · rcases List.mem_append.mp htailMem with htailMem | hinterval
          · exact ht op htailMem
          · have heq := List.mem_singleton.mp hinterval
            subst op
            trivial
  intro op hop
  unfold beforeNodeWord at hop
  rw [List.append_assoc] at hop
  rcases List.mem_append.mp hop with hpMem | hremaining
  · exact hp op hpMem
  · rcases List.mem_append.mp hremaining with hexit | hnode
    · obtain ⟨e, _, rfl⟩ := List.mem_map.mp hexit
      trivial
    · obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hnode
      change NoPrivateRead N {site} (originalNodeOperation N H gamma common v)
      apply originalNodeOperation_noPrivateRead
      intro hm
      have heq : v = site := Finset.mem_singleton.mp hm
      exact hnodeAbsent (heq ▸ hv)

/-- At a COMMON hybrid, the selected operation in the split is the actual
registry's original parent pair. No occurrence order or register label changes. -/
theorem actual_compiled_before_common_split
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (h : Hybrid N) (hc : common h = true)
    (pre post : List ℝ) (nodesBefore nodesAfter : List V)
    (hdates : sortedOriginalDates N C = pre ++ C.age h.val :: post)
    (hnodes : (Finset.univ.filter (fun v : V => C.age v = C.age h.val)).toList =
      nodesBefore ++ h.val :: nodesAfter) :
    compiledCalendarProgram N C H gamma common =
      beforeNodeWord N C H gamma common h.val pre nodesBefore ++
        [.boundary (.common (H.parents h))] ++
        nodesAfter.map (fun v => .boundary (originalNodeOperation N H gamma common v)) ++
        calendarTail N C H gamma common (C.age h.val) post := by
  have hr : h.val ≠ N.root := by
    intro heq
    have hd := h.property.1
    rw [heq, N.root_degrees.1] at hd
    exact Nat.zero_ne_add_one 1 hd
  have hop : originalNodeOperation N H gamma common h.val = .common (H.parents h) := by
    simp [originalNodeOperation, hr, h.property, hc]
  rw [actual_compiled_before_node_split N C H gamma common h.val pre post nodesBefore nodesAfter
    hdates hnodes, hop]

#print axioms actual_compiled_before_node_split
#print axioms actual_before_node_noPrivateWordRead
#print axioms actual_compiled_before_common_split

end GProgram.G6.OriginalCommonPrefix
