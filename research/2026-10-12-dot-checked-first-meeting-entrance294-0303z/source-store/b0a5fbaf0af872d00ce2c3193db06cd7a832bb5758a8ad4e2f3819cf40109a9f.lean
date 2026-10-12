import G5StrictBoundaryRoutes
import G5ProtectiveBlock
import G5SafePastHybridDisjointness
import UnifiedLean.Source.SourceCalendarCompatibility

/-! Direct use-site of the inherited protective-edge route theorem on the
actual admitted source Code. This does not assert arbitrary joint feasibility
of independently chosen paths. Interior population admission remains explicit. -/
namespace GProgram.G5.ActualProtectiveOccupancy
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceCalendarCompatibility
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Actual source validity extends any occupied original edge to a full
original root-to-sampled-tip path. This is a witness, not a joint route law. -/
theorem actual_edge_on_original_route (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (x : Copy) (f : E)
    (hf : copyLocation (state s) x = .edge f) :
    ∃ es : List E, EdgePath N.graph N.root (N.leaf (sample x)) es ∧ f ∈ es := by
  have hd := s.property.original_descendant x
  change DescendsTo N (copyLocation (state s) x) (sample x) at hd
  rw [hf] at hd
  obtain ⟨pre,hpre⟩ := exists_edgePath_of_directed (N.rooted (N.graph.source f))
  obtain ⟨post,hpost⟩ := exists_edgePath_of_directed hd
  have hsingle : EdgePath N.graph (N.graph.source f) (N.graph.target f) [f] :=
    .cons rfl (.nil _)
  exact ⟨pre ++ ([f] ++ post),hpre.append (hsingle.append hpost),by simp⟩

/-- Any actual admitted active descendant lineage has the protective edge
as its population, regardless of older mergers or hidden routing dependence. -/
theorem actual_active_descendant_occupies_protective (N : RootedBinary V E X)
    (C : Calendar N.graph) {sample : Copy → X} (s : Code N sample) (x : Copy)
    {h : V} (hh : N.graph.IsHybrid h) {e f : E}
    (hs : N.graph.source e = h) (he : N.graph.IsBridge e)
    (hd : N.graph.DReach h (N.leaf (sample x))) {t : ℝ}
    (ht : C.age (N.graph.target e) ≤ t ∧ t < C.age h)
    (hf : copyLocation (state s) x = .edge f) (ha : C.Active t f) :
    copyLocation (state s) x = .edge e := by
  obtain ⟨es,hp,hm⟩ := actual_edge_on_original_route N s x f hf
  have hfe := (protective_edge_active_on_every_route N C hh hs he hd hp ht).2.2 f hm ha
  simpa [hfe] using hf

/-- Source validity excludes every outside sampled tip from the same edge. -/
theorem actual_protective_occupancy_implies_descendant (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (x : Copy) {h : V} {e : E}
    (hs : N.graph.source e = h) (hx : copyLocation (state s) x = .edge e) :
    N.graph.DReach h (N.leaf (sample x)) := by
  have hd := s.property.original_descendant x
  change DescendsTo N (copyLocation (state s) x) (sample x) at hd
  rw [hx] at hd
  exact (Relation.ReflTransGen.single ⟨e,hs,rfl⟩).trans hd

/-- Uses exactly an actual edge/ancestral placement and its physical epoch
compatibility. It does not ask for the desired descendant-block conclusion. -/
theorem actual_protective_copy_location_iff (N : RootedBinary V E X)
    (C : Calendar N.graph) {sample : Copy → X} (s : Code N sample)
    (place : Copy → Option E)
    (hp : ∀ x, copyLocation (state s) x = originalPlace N (place x))
    {a b t : ℝ} (hc : EpochCompatible N C a b (state s))
    (ha : a ≤ t) (hb : t < b)
    {h : V} (hh : N.graph.IsHybrid h) {e : E}
    (hs : N.graph.source e = h) (he : N.graph.IsBridge e)
    (ht : C.age (N.graph.target e) ≤ t ∧ t < C.age h) (x : Copy) :
    copyLocation (state s) x = .edge e ↔ N.graph.DReach h (N.leaf (sample x)) := by
  constructor
  · exact actual_protective_occupancy_implies_descendant N s x hs
  · intro hd
    cases hx : place x with
    | some f =>
        have hf : copyLocation (state s) x = .edge f := by simpa [hx, originalPlace] using hp x
        exact actual_active_descendant_occupies_protective N C s x hh hs he hd ht hf
          (epoch_edge_active N C hc hf ha hb)
    | none =>
        have hf : copyLocation (state s) x = .rootPopulation N.root := by
          simpa [hx, originalPlace] using hp x
        have hroot := hc x
        rw [hf] at hroot
        have hage : C.age h ≤ C.age N.root := C.age_le_of_directed (N.rooted h)
        exact False.elim (not_lt_of_ge (hage.trans (hroot.2.trans ha)) ht.2)

/-- Entire actual selected population block, with original copy labels and
sample map retained. This holds statewise, hence retains every posterior
correlation. It does not assert realizability of arbitrary route families. -/
theorem actual_protective_selected_block (N : RootedBinary V E X)
    (C : Calendar N.graph) {sample : Copy → X} (s : Code N sample)
    (place : Copy → Option E)
    (hp : ∀ x, copyLocation (state s) x = originalPlace N (place x))
    {a b t : ℝ} (hc : EpochCompatible N C a b (state s))
    (ha : a ≤ t) (hb : t < b)
    {h : V} (hh : N.graph.IsHybrid h) {e : E}
    (hs : N.graph.source e = h) (he : N.graph.IsBridge e)
    (ht : C.age (N.graph.target e) ≤ t ∧ t < C.age h) (keep : Finset Copy) :
    keep.filter (fun x => copyLocation (state s) x = .edge e) =
      keep.filter (fun x => N.graph.DReach h (N.leaf (sample x))) := by
  apply Finset.filter_congr
  intro x _
  exact actual_protective_copy_location_iff N C s place hp hc ha hb hh hs he ht x

/-- A route-family witness for ONE actual admitted state. No statement says
that an arbitrarily selected route family is jointly source-realizable. -/
theorem actual_state_has_matching_route_family [DecidableEq X]
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (s : Code N (id : X → X)) (t : ℝ)
    (hloc : ∀ x : X, ∃ e : E, copyLocation (state s) x = .edge e ∧ C.Active t e) :
    ∃ R : RouteFamily N, ∀ B : Finset X, ∀ e : E,
      selectedPopulationBlock N R B C t e =
        B.filter (fun x => copyLocation (state s) x = .edge e) := by
  choose place hp ha using hloc
  have hx (x : X) := actual_edge_on_original_route N s x (place x) (hp x)
  choose es hs hm using hx
  let R : RouteFamily N := ⟨es, hs⟩
  refine ⟨R,?_⟩
  intro B e
  unfold selectedPopulationBlock
  apply Finset.ext
  intro x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hB,he⟩
    refine ⟨hB,?_⟩
    have heq : e = place x := (hs x).active_unique C he.1 (hm x) he.2 (ha x)
    simpa [heq] using hp x
  · rintro ⟨hB,he⟩
    refine ⟨hB,?_⟩
    have heq : place x = e := Location.edge.inj ((hp x).symm.trans he)
    exact ⟨heq ▸ hm x, heq ▸ ha x⟩

/-- Every inherited all-route sure block is an exact block in the actual
state. This direction is enough to transport absence of observed sure blocks
to the structural safe-past hypothesis, after the existing law/support link. -/
theorem structural_sure_block_in_actual_state [DecidableEq X]
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (s : Code N (id : X → X)) (t : ℝ)
    (hloc : ∀ x : X, ∃ e : E, copyLocation (state s) x = .edge e ∧ C.Active t e)
    (B D : Finset X) (hsure : GProgram.G5.SafePast.SureExactBlock N C B D t) :
    ∃ e : E, B.filter (fun x => copyLocation (state s) x = .edge e) = D := by
  obtain ⟨R,hR⟩ := actual_state_has_matching_route_family N C s t hloc
  obtain ⟨e,he⟩ := hsure R
  exact ⟨e,(hR B e).symm.trans he⟩

/-- The matching-family witness follows from the same original active
placement/epoch premises used by the source triple row, below the root. -/
theorem actual_epoch_has_matching_route_family [DecidableEq X]
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (s : Code N (id : X → X)) (place : X → Option E)
    (hp : ∀ x, copyLocation (state s) x = originalPlace N (place x))
    {a b t : ℝ} (hc : EpochCompatible N C a b (state s))
    (ha : a ≤ t) (hb : t < b) (htop : t < C.age N.root) :
    ∃ R : RouteFamily N, ∀ B : Finset X, ∀ e : E,
      selectedPopulationBlock N R B C t e =
        B.filter (fun x => copyLocation (state s) x = .edge e) := by
  apply actual_state_has_matching_route_family N C s t
  intro x
  cases hx : place x with
  | some e =>
      have he : copyLocation (state s) x = .edge e := by simpa [hx, originalPlace] using hp x
      exact ⟨e,he,epoch_edge_active N C hc he ha hb⟩
  | none =>
      have he : copyLocation (state s) x = .rootPopulation N.root := by
        simpa [hx, originalPlace] using hp x
      have hr := hc x
      rw [he] at hr
      exact False.elim (not_lt_of_ge (hr.2.trans ha) htop)

#print axioms actual_epoch_has_matching_route_family

#print axioms actual_state_has_matching_route_family
#print axioms structural_sure_block_in_actual_state

#print axioms actual_protective_copy_location_iff
#print axioms actual_protective_selected_block

#print axioms actual_edge_on_original_route
#print axioms actual_active_descendant_occupies_protective
#print axioms actual_protective_occupancy_implies_descendant
end GProgram.G5.ActualProtectiveOccupancy
