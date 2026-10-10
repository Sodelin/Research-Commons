import G5OriginalGroupPathChronology
import G5NativeOriginalRouteCoverage
import SourceResolve
import GraphSwitchingChoices

/-!
# Actual common-switching edges and positive calendar quartet witnesses
Contributor: dot / OpenAI, 2026-10-03.
Switchings are constructed from the SAME original parent registry/register.
All raw switchings are covered. Original compiled route membership is exactly
selected-graph directed ancestry. This binds calendar witnesses to actual
switching edge cuts, never to an abstract fitted occupancy kernel.
-/
namespace GProgram.G5.AttainedChronology
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.NonbridgeRoutes
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeCommonPairGerm
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

noncomputable def commonSwitching (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (a : CommonSeed N) : N.Switching :=
  N.switchingOfChoices (fun h => ⟨(H.parents h).parent (a h),registry_parent_target N H h (a h)⟩)

/-- Every raw original switching uses one actual original register assignment. -/
theorem commonSwitching_covers (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (S : N.Switching) : ∃ a : CommonSeed N, commonSwitching N H a = S := by
  have hb : ∀ h : Hybrid N, ∃ b : Bool, (H.parents h).parent b = (N.choicesOfSwitching S h).val := by
    intro h
    exact GProgram.G5.ParentCalendar.incoming_edge_is_original_parent (H.parents h)
      ((N.choicesOfSwitching S h).property.trans (H.original_site h).symm)
  let a : CommonSeed N := fun h => Classical.choose (hb h)
  refine ⟨a,?_⟩
  unfold commonSwitching
  rw [←N.switchingOfChoices_choicesOfSwitching S]
  congr 1
  funext h
  exact Subtype.ext (Classical.choose_spec (hb h))

lemma common_route_kept (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (a : CommonSeed N) (x : X) {e : E}
    (he : e ∈ (commonRoutes N C H a).edges x) : (commonSwitching N H a).keep e := by
  by_cases hh : N.graph.IsHybrid (N.graph.target e)
  · have hc := compiled_original_parent_consistency N C H (fun _ h => a h) x he hh
    exact Or.inr ⟨⟨N.graph.target e,hh⟩,hc.symm⟩
  · exact Or.inl hh

lemma common_kept_edge_respects (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (a : CommonSeed N) {e : E} (he : (commonSwitching N H a).keep e) :
    ∃ hn : N.graph.target e ≠ N.root, (coinSelector N H a).edge ⟨N.graph.target e,hn⟩ = e := by
  let hn := original_edge_target_not_root N e
  refine ⟨hn,?_⟩
  by_cases hh : N.graph.IsHybrid (N.graph.target e)
  · let h : Hybrid N := ⟨N.graph.target e,hh⟩
    have hc := (N.switchingOfChoices_keep_at_hybrid
      (fun h => ⟨(H.parents h).parent (a h),registry_parent_target N H h (a h)⟩) h e rfl).mp he
    simpa only [coinSelector,dif_pos hh] using hc.symm
  · simp only [coinSelector,dif_neg hh]
    exact incoming_equal_of_indegree_le_one N (nonhybrid_indegree_le_one N hh)
      ((defaultSelector N).target ⟨N.graph.target e,hn⟩) rfl

lemma kept_original_path_selected_reach (N : RootedBinary V E X) (S : N.Switching)
    {v w : V} {es : List E} (p : EdgePath N.graph v w es)
    (hk : ∀ e ∈ es, S.keep e) : S.graph.DReach v w := by
  induction p with
  | nil => exact .refl
  | @cons v w e es hs rest ih =>
    exact (Relation.ReflTransGen.single ⟨⟨e,hk e List.mem_cons_self⟩,hs,rfl⟩).trans
      (ih (fun f hf => hk f (List.mem_cons_of_mem e hf)))

lemma selected_path_original (N : RootedBinary V E X) (S : N.Switching)
    {v w : V} {es : List S.Edge} (p : EdgePath S.graph v w es) :
    EdgePath N.graph v w (es.map Subtype.val) := by
  induction p with
  | nil => exact .nil _
  | cons hs rest ih => exact .cons hs ih

lemma selected_reach_original_kept_path (N : RootedBinary V E X) (S : N.Switching)
    {v w : V} (h : S.graph.DReach v w) :
    ∃ es : List E, EdgePath N.graph v w es ∧ ∀ e ∈ es, S.keep e := by
  obtain ⟨es,hp⟩ := exists_edgePath_of_directed h
  refine ⟨es.map Subtype.val,selected_path_original N S hp,?_⟩
  intro e he
  obtain ⟨f,_,rfl⟩ := List.mem_map.mp he
  exact f.property

lemma original_path_eq_compiled_of_respects (N : RootedBinary V E X) (C : Calendar N.graph)
    (P : IncomingSelector N) {v : V} {es : List E} (p : EdgePath N.graph N.root v es)
    (hP : RespectsSelector N P es) : es = compiledRoute N C P v := by
  have hs := compiledRoute_source_spec N C P v
  apply List.reverse_inj.mp
  exact UpPath.eq_of_same_selector N P
    (GProgram.G5.NonbridgeRoutes.EdgePath.to_upPath_reverse p (fun _ _ => trivial))
    (GProgram.G5.NonbridgeRoutes.EdgePath.to_upPath_reverse hs.1 (fun _ _ => trivial))
    (respectsSelector_reverse N P hP) (respectsSelector_reverse N P hs.2)

/-- Exact actual switching ancestry, not an abstract population-side field. -/
theorem common_route_edge_iff_selected_descendant (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (a : CommonSeed N) (x : X) (e : (commonSwitching N H a).Edge) :
    e.val ∈ (commonRoutes N C H a).edges x ↔
      (commonSwitching N H a).graph.DReach (N.graph.target e.val) (N.leaf x) := by
  let S := commonSwitching N H a
  constructor
  · intro he
    obtain ⟨pre,post,hs,hpre,hpost⟩ := GProgram.G5.ComponentCalendar.EdgePath.split_at_original_edge
      ((commonRoutes N C H a).valid x) he
    apply kept_original_path_selected_reach N S hpost
    intro f hf
    apply common_route_kept N C H a x
    rw [hs]
    exact List.mem_append_right _ (List.mem_cons_of_mem e.val hf)
  · intro hd
    obtain ⟨pre,hpre,hprek⟩ := selected_reach_original_kept_path N S (S.selected_rooted (N.graph.source e.val))
    obtain ⟨post,hpost,hpostk⟩ := selected_reach_original_kept_path N S hd
    let es := pre ++ e.val :: post
    have hp : EdgePath N.graph N.root (N.leaf x) es := hpre.append (.cons rfl hpost)
    have hk : ∀ f ∈ es, S.keep f := by
      intro f hf
      rcases List.mem_append.mp hf with hf | hf
      · exact hprek f hf
      · rcases List.mem_cons.mp hf with hf | hf
        · subst f; exact e.property
        · exact hpostk f hf
    have hr : RespectsSelector N (coinSelector N H a) es :=
      fun f hf => common_kept_edge_respects N H a (hk f hf)
    have heq := original_path_eq_compiled_of_respects N C (coinSelector N H a) hp hr
    have hm : e.val ∈ es := List.mem_append_right _ List.mem_cons_self
    rw [heq] at hm
    exact hm

/-- A proper quartet-side population witness in one actual original switching. -/
def OriginalQuartetSideWitness (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (a : CommonSeed N) (t : ℝ) (q : Fin 4 ↪ X) : Prop :=
  ∃ e : E, C.Active t e ∧
    ((e ∈ (commonRoutes N C H a).edges (q 0) ∧ e ∈ (commonRoutes N C H a).edges (q 1) ∧
      e ∉ (commonRoutes N C H a).edges (q 2) ∧ e ∉ (commonRoutes N C H a).edges (q 3)) ∨
     (e ∈ (commonRoutes N C H a).edges (q 2) ∧ e ∈ (commonRoutes N C H a).edges (q 3) ∧
      e ∉ (commonRoutes N C H a).edges (q 0) ∧ e ∉ (commonRoutes N C H a).edges (q 1)))

lemma common_route_edge_iff_selected_target_side (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (a : CommonSeed N) (x : X) (e : (commonSwitching N H a).Edge) :
    e.val ∈ (commonRoutes N C H a).edges x ↔
      (commonSwitching N H a).graph.ReachWithout e (N.graph.target e.val) (N.leaf x) := by
  let S := commonSwitching N H a
  exact (common_route_edge_iff_selected_descendant N C H a x e).trans
    (S.graph.target_side_iff_descendant S.selected_uniqueIncoming S.selected_acyclic e (N.leaf x)).symm

lemma common_route_edge_absent_iff_selected_source_side (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (a : CommonSeed N) (x : X) (e : (commonSwitching N H a).Edge) :
    e.val ∉ (commonRoutes N C H a).edges x ↔
      (commonSwitching N H a).graph.ReachWithout e (N.graph.source e.val) (N.leaf x) := by
  let S := commonSwitching N H a
  have he : S.graph.IsBridge e := S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic e
  constructor
  · intro hn
    rcases S.graph.edge_side_cover e (S.selected_connected (N.graph.source e.val) (N.leaf x)) with hs | ht
    · exact hs
    · exact False.elim (hn ((common_route_edge_iff_selected_target_side N C H a x e).mpr ht))
  · intro hs hm
    exact S.graph.bridge_sides_disjoint he hs ((common_route_edge_iff_selected_target_side N C H a x e).mp hm)

/-- Every calendar witness is an actual selected tree edge-cut resolution. -/
theorem original_calendar_quartet_witness_sound (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (a : CommonSeed N) (q : Fin 4 ↪ X) (t : ℝ)
    (hw : OriginalQuartetSideWitness N C H a t q) :
    (commonSwitching N H a).graph.HasQuartet (N.leaf (q 0)) (N.leaf (q 1)) (N.leaf (q 2)) (N.leaf (q 3)) := by
  let S := commonSwitching N H a
  obtain ⟨e,ha,hside⟩ := hw
  have hk : S.keep e := by
    rcases hside with h | h
    · exact common_route_kept N C H a (q 0) h.1
    · exact common_route_kept N C H a (q 2) h.1
  let f : S.Edge := ⟨e,hk⟩
  refine ⟨f,S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic f,?_⟩
  rcases hside with h | h
  · exact Or.inr ⟨(common_route_edge_absent_iff_selected_source_side N C H a (q 2) f).mp h.2.2.1,
      (common_route_edge_absent_iff_selected_source_side N C H a (q 3) f).mp h.2.2.2,
      (common_route_edge_iff_selected_target_side N C H a (q 0) f).mp h.1,
      (common_route_edge_iff_selected_target_side N C H a (q 1) f).mp h.2.1⟩
  · exact Or.inl ⟨(common_route_edge_absent_iff_selected_source_side N C H a (q 0) f).mp h.2.2.1,
      (common_route_edge_absent_iff_selected_source_side N C H a (q 1) f).mp h.2.2.2,
      (common_route_edge_iff_selected_target_side N C H a (q 2) f).mp h.1,
      (common_route_edge_iff_selected_target_side N C H a (q 3) f).mp h.2.1⟩

/-- Each actual switched quartet edge supplies a NONEMPTY positive ORIGINAL
calendar interval, on EVERY age of which the witness is valid. -/
theorem original_calendar_quartet_witness_complete_positive_interval
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (a : CommonSeed N) (q : Fin 4 ↪ X)
    (hq : (commonSwitching N H a).graph.HasQuartet
      (N.leaf (q 0)) (N.leaf (q 1)) (N.leaf (q 2)) (N.leaf (q 3))) :
    ∃ l u : ℝ, l < u ∧ ∀ t : ℝ, l ≤ t → t < u → OriginalQuartetSideWitness N C H a t q := by
  let S := commonSwitching N H a
  obtain ⟨e,he,hside⟩ := hq
  refine ⟨C.age (N.graph.target e.val),C.age (N.graph.source e.val),C.edge_older e.val,?_⟩
  intro t hlt htu
  refine ⟨e.val,⟨hlt,htu⟩,?_⟩
  rcases hside with h | h
  · exact Or.inr ⟨(common_route_edge_iff_selected_target_side N C H a (q 2) e).mpr h.2.2.1,
      (common_route_edge_iff_selected_target_side N C H a (q 3) e).mpr h.2.2.2,
      (common_route_edge_absent_iff_selected_source_side N C H a (q 0) e).mpr h.1,
      (common_route_edge_absent_iff_selected_source_side N C H a (q 1) e).mpr h.2.1⟩
  · exact Or.inl ⟨(common_route_edge_iff_selected_target_side N C H a (q 0) e).mpr h.2.2.1,
      (common_route_edge_iff_selected_target_side N C H a (q 1) e).mpr h.2.2.2,
      (common_route_edge_absent_iff_selected_source_side N C H a (q 2) e).mpr h.1,
      (common_route_edge_absent_iff_selected_source_side N C H a (q 3) e).mpr h.2.1⟩

/-- Exact ACTUAL raw displayed resolution, with all complete switchings and
original positive calendar witnesses. This does not rename an abstract kernel
as a displayed quartet. Reduction convention bridges remain explicitly scoped. -/
theorem raw_displayed_first_quartet_iff_calendar_witness (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (q : Fin 4 ↪ X) :
    Nanuq.Quartet.Resolution.xy_zw ∈ N.rawDisplayedQuartets q ↔
      ∃ a : CommonSeed N, ∃ t : ℝ, OriginalQuartetSideWitness N C H a t q := by
  simp only [RootedBinary.rawDisplayedQuartets,Nanuq.Quartet.displayed,Finset.mem_image,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨S,hS⟩
    obtain ⟨a,ha⟩ := commonSwitching_covers N H S
    have hq : S.graph.HasQuartet (N.leaf (q 0)) (N.leaf (q 1)) (N.leaf (q 2)) (N.leaf (q 3)) := by
      have hr := S.resolve_spec q
      rw [hS] at hr
      exact hr
    rw [←ha] at hq
    obtain ⟨l,u,hlu,hw⟩ := original_calendar_quartet_witness_complete_positive_interval N C H a q hq
    exact ⟨a,l,hw l le_rfl hlu⟩
  · rintro ⟨a,t,hw⟩
    refine ⟨commonSwitching N H a,?_⟩
    exact (commonSwitching N H a).graph.resolution_unique
      ((commonSwitching N H a).resolve_spec q) (original_calendar_quartet_witness_sound N C H a q t hw)

#print axioms original_calendar_quartet_witness_sound
#print axioms original_calendar_quartet_witness_complete_positive_interval
#print axioms raw_displayed_first_quartet_iff_calendar_witness
#print axioms commonSwitching_covers
#print axioms common_route_edge_iff_selected_descendant
end GProgram.G5.AttainedChronology
