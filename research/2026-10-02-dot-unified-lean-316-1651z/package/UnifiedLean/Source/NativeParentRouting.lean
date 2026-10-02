import G5OriginalRouteHazard
import G4PathResolvedMeasurement
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Data.Finset.Card

/-!
# Native original-graph parent-choice compiler and stopped pair source

Work-in-progress toward complete source binding. Every selector refers only
to an actual incoming original edge. Routes are CONSTRUCTED from those local
choices and strictly older original clocks, not supplied as a desired kernel.
Native coin/clock probability and private-word observation binding follow in
this same source-development target; no complete theorem is claimed yet.
-/
namespace UnifiedLean.Source.NativeParentRouting
open Nanuq.Source
open GProgram.G5
open scoped BigOperators Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

abbrev Nonroot (N : RootedBinary V E X) := {v : V // v ≠ N.root}

/-- Only source-local data: one ACTUAL incoming edge selected at each nonroot.
No route law, survival identity or identifiability conclusion is a field. -/
structure IncomingSelector (N : RootedBinary V E X) where
  edge : Nonroot N → E
  target : ∀ v, N.graph.target (edge v) = v.1

lemma original_incoming_exists (N : RootedBinary V E X) {v : V} (hv : v ≠ N.root) :
    ∃ e : E, N.graph.target e = v := by
  rcases Relation.ReflTransGen.cases_tail (N.rooted v) with heq | ⟨u,_,e,_,ht⟩
  · exact False.elim (hv heq)
  · exact ⟨e,ht⟩

noncomputable def defaultSelector (N : RootedBinary V E X) : IncomingSelector N where
  edge v := Classical.choose (original_incoming_exists N v.property)
  target v := Classical.choose_spec (original_incoming_exists N v.property)

abbrev Hybrid (N : RootedBinary V E X) := {v : V // N.graph.IsHybrid v}

lemma original_parent_ordering_exists (N : RootedBinary V E X) (v : Hybrid N) :
    ∃ H : GProgram.G2.OriginalHybridParents N, H.hybrid = v.1 := by
  classical
  have hc : (Finset.univ.filter (fun e : E => N.graph.target e = v.1)).card = 2 := v.property.1
  obtain ⟨e,f,hef,hset⟩ := Finset.card_eq_two.mp hc
  have he : N.graph.target e = v.1 := by
    have hm : e ∈ Finset.univ.filter (fun e : E => N.graph.target e = v.1) := by rw [hset]; simp
    exact (Finset.mem_filter.mp hm).2
  have hf : N.graph.target f = v.1 := by
    have hm : f ∈ Finset.univ.filter (fun e : E => N.graph.target e = v.1) := by rw [hset]; simp
    exact (Finset.mem_filter.mp hm).2
  exact ⟨⟨v.1, v.property, e, f, he, hf, hef⟩, rfl⟩

/-- Source parameter orientation, consisting solely of BOTH actual original
incoming edge occurrences at every actual original hybrid. -/
structure OriginalParentRegistry (N : RootedBinary V E X) where
  parents : Hybrid N → GProgram.G2.OriginalHybridParents N
  original_site : ∀ v, (parents v).hybrid = v.1

noncomputable def canonicalParentRegistry (N : RootedBinary V E X) : OriginalParentRegistry N where
  parents v := Classical.choose (original_parent_ordering_exists N v)
  original_site v := Classical.choose_spec (original_parent_ordering_exists N v)

lemma registry_parent_target (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (v : Hybrid N) (b : Bool) : N.graph.target ((H.parents v).parent b) = v.1 := by
  cases b
  · exact (H.parents v).target0.trans (H.original_site v)
  · exact (H.parents v).target1.trans (H.original_site v)

/-- Current-root coins choose only their actual ORIGINAL hybrid parent. Every
nonhybrid step uses its fixed original incoming edge; root is terminal. -/
noncomputable def coinSelector (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (coin : Hybrid N → Bool) : IncomingSelector N where
  edge v := if hv : N.graph.IsHybrid v.1 then (H.parents ⟨v.1,hv⟩).parent (coin ⟨v.1,hv⟩)
    else (defaultSelector N).edge v
  target v := by
    by_cases hv : N.graph.IsHybrid v.1
    · simp only [dif_pos hv]
      exact registry_parent_target N H ⟨v.1,hv⟩ _
    · simp only [dif_neg hv]
      exact (defaultSelector N).target v

noncomputable def olderRank (N : RootedBinary V E X) (C : Calendar N.graph) (v : V) : Nat :=
  (Finset.univ.filter (fun w : V => C.age v < C.age w)).card

lemma olderRank_edge_decreases (N : RootedBinary V E X) (C : Calendar N.graph) (e : E) :
    olderRank N C (N.graph.source e) < olderRank N C (N.graph.target e) := by
  unfold olderRank
  apply Finset.card_lt_card
  rw [Finset.ssubset_iff_subset_ne]
  constructor
  · intro w hw
    simp only [Finset.mem_filter,Finset.mem_univ,true_and] at hw ⊢
    exact (C.edge_older e).trans hw
  · intro heq
    have hm : N.graph.source e ∈ Finset.univ.filter
        (fun w : V => C.age (N.graph.target e) < C.age w) := by
      simp only [Finset.mem_filter,Finset.mem_univ,true_and]
      exact C.edge_older e
    rw [← heq] at hm
    simpa using hm

/-- Every traversed original edge was selected at its actual younger endpoint. -/
def RespectsSelector (N : RootedBinary V E X) (P : IncomingSelector N) (es : List E) : Prop :=
  ∀ e ∈ es, ∃ h : N.graph.target e ≠ N.root,
    P.edge ⟨N.graph.target e,h⟩ = e

lemma selector_edge_respects (N : RootedBinary V E X) (P : IncomingSelector N)
    (v : Nonroot N) : RespectsSelector N P [P.edge v] := by
  intro e he
  have h : e = P.edge v := by simpa using he
  subst e
  have ht : N.graph.target (P.edge v) ≠ N.root := by rw [P.target]; exact v.property
  refine ⟨ht,?_⟩
  congr 1
  exact Subtype.ext (P.target v)

lemma selected_original_path_exists (N : RootedBinary V E X) (C : Calendar N.graph)
    (P : IncomingSelector N) (v : V) :
    ∃ es : List E, EdgePath N.graph N.root v es ∧ RespectsSelector N P es := by
  have aux : ∀ n : Nat, ∀ w : V, olderRank N C w = n →
      ∃ es : List E, EdgePath N.graph N.root w es ∧ RespectsSelector N P es := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hn
      by_cases hw : w = N.root
      · subst w
        exact ⟨[],EdgePath.nil _,by intro e he; simp at he⟩
      · let e := P.edge ⟨w,hw⟩
        have ht : N.graph.target e = w := P.target ⟨w,hw⟩
        have hlt : olderRank N C (N.graph.source e) < n := by
          have h := olderRank_edge_decreases N C e
          rwa [ht,hn] at h
        obtain ⟨es,hpath,hselect⟩ := ih _ hlt _ rfl
        have last : EdgePath N.graph (N.graph.source e) w [e] :=
          EdgePath.cons rfl (by rw [ht]; exact EdgePath.nil w)
        refine ⟨es++[e],hpath.append last,?_⟩
        intro f hf
        rcases List.mem_append.mp hf with hf | hf
        · exact hselect f hf
        · exact selector_edge_respects N P ⟨w,hw⟩ f hf
  exact aux (olderRank N C v) v rfl

/-- Constructed original-edge route, valid for every finite native source,
strict calendar and local original incoming-edge selector. -/
noncomputable def compiledRoute (N : RootedBinary V E X) (C : Calendar N.graph)
    (P : IncomingSelector N) (v : V) : List E :=
  Classical.choose (selected_original_path_exists N C P v)

theorem compiledRoute_source_spec (N : RootedBinary V E X) (C : Calendar N.graph)
    (P : IncomingSelector N) (v : V) :
    EdgePath N.graph N.root v (compiledRoute N C P v) ∧
      RespectsSelector N P (compiledRoute N C P v) :=
  Classical.choose_spec (selected_original_path_exists N C P v)

/-- ALL original-tip routes are compiled from the local current-owner coins
on the unchanged graph. Unused coin sites do not invent route segments. -/
noncomputable def compiledRouteFamily (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (coin : X → Hybrid N → Bool) : RouteFamily N where
  edges x := compiledRoute N C (coinSelector N H (coin x)) (N.leaf x)
  valid x := (compiledRoute_source_spec N C (coinSelector N H (coin x)) (N.leaf x)).1

/-- Record ties each traversed original parent edge to the SAME original
hybrid occurrence and the current root owner's actual preassigned coin. -/
theorem compiled_original_parent_consistency (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (coin : X → Hybrid N → Bool) (x : X) {e : E}
    (he : e ∈ (compiledRouteFamily N C H coin).edges x)
    (hy : N.graph.IsHybrid (N.graph.target e)) :
    e = (H.parents ⟨N.graph.target e,hy⟩).parent (coin x ⟨N.graph.target e,hy⟩) := by
  obtain ⟨hne,hsel⟩ := (compiledRoute_source_spec N C (coinSelector N H (coin x))
    (N.leaf x)).2 e he
  simpa only [coinSelector,dif_pos hy] using hsel.symm

#print axioms original_incoming_exists
#print axioms original_parent_ordering_exists
#print axioms registry_parent_target
#print axioms olderRank_edge_decreases
#print axioms compiled_original_parent_consistency
#print axioms selected_original_path_exists
#print axioms compiledRoute_source_spec
end UnifiedLean.Source.NativeParentRouting
