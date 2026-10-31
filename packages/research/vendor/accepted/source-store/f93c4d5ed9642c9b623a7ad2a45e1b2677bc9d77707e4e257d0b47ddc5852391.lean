import G5CommonSwitchingPersistence

/-!
# Every original route is realized by actual original parent bits
Contributor: dot / OpenAI, 2026-10-03.
This is geometric support coverage, preserving exact original parallel IDs.
It does not supply a stochastic law or add source support as a record field.
-/
namespace GProgram.G5.AttainedChronology
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G5.NonbridgeRoutes
open UnifiedLean.Source.NativeParentRouting
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma original_edge_target_not_root (N : RootedBinary V E X) (e : E) :
    N.graph.target e ≠ N.root := by
  intro he
  have hm : e ∈ Finset.univ.filter (fun f : E => N.graph.target f = N.root) := by simp [he]
  have hz := N.root_degrees.1
  rw [EdgeGraph.inDegree,Finset.card_eq_zero] at hz
  rw [hz] at hm
  exact Finset.notMem_empty e hm

/-- Acyclicity prevents a route from selecting two incoming edges at the same
original vertex. The proof applies to original occurrences, not a simple graph. -/
lemma EdgePath.incoming_unique (N : RootedBinary V E X) {a b : V} {es : List E}
    (p : EdgePath N.graph a b es) {e f : E} (he : e ∈ es) (hf : f ∈ es)
    (ht : N.graph.target e = N.graph.target f) : e = f := by
  induction p with
  | nil => simp at he
  | @cons a b d ds hs rest ih =>
    rcases List.mem_cons.mp he with hed | he
    · subst e
      rcases List.mem_cons.mp hf with hfd | hf
      · exact hfd.symm
      · have hc := GProgram.G5.ComponentCalendar.EdgePath.source_reachable_of_mem rest hf
        exact False.elim (N.acyclic (N.graph.target d)
          (Relation.TransGen.tail' hc ⟨f,rfl,ht.symm⟩))
    · rcases List.mem_cons.mp hf with hfd | hf
      · subst f
        have hc := GProgram.G5.ComponentCalendar.EdgePath.source_reachable_of_mem rest he
        exact False.elim (N.acyclic (N.graph.target d)
          (Relation.TransGen.tail' hc ⟨e,rfl,ht⟩))
      · exact ih he hf

lemma UpPath.eq_of_same_selector (N : RootedBinary V E X) (P : IncomingSelector N)
    {a b : V} {es fs : List E} (p : UpPath N.graph (fun _ => True) a b es)
    (q : UpPath N.graph (fun _ => True) a b fs)
    (hp : RespectsSelector N P es) (hq : RespectsSelector N P fs) : es = fs := by
  induction p generalizing fs with
  | nil a =>
    cases q with
    | nil => rfl
    | cons ht he rest =>
      exact False.elim ((UpPath.cons ht he rest).nonempty_start_ne_end N.acyclic rfl)
  | @cons a b e es ht he rest ih =>
    cases q with
    | nil => exact False.elim ((UpPath.cons ht he rest).nonempty_start_ne_end N.acyclic rfl)
    | @cons _ _ f fs htf hf tail =>
      have hef : e = f := selected_edges_equal N P hp hq List.mem_cons_self List.mem_cons_self (ht.trans htf.symm)
      subst f
      congr 1
      exact ih tail (fun d hd => hp d (List.mem_cons_of_mem e hd))
        (fun d hd => hq d (List.mem_cons_of_mem e hd))

/-- Only actual incoming edges on the given route determine its coin choices. -/
theorem original_path_coin_realization (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) {v : V} {es : List E}
    (p : EdgePath N.graph N.root v es) :
    ∃ coin : Hybrid N → Bool, RespectsSelector N (coinSelector N H coin) es := by
  have hex (h : Hybrid N) (hh : ∃ e ∈ es, N.graph.target e = h.1) :
      ∃ b : Bool, ∀ e ∈ es, N.graph.target e = h.1 → (H.parents h).parent b = e := by
    obtain ⟨e,he,ht⟩ := hh
    obtain ⟨b,hb⟩ := GProgram.G5.ParentCalendar.incoming_edge_is_original_parent (H.parents h)
      (ht.trans (H.original_site h).symm)
    refine ⟨b,?_⟩
    intro f hf htf
    exact hb.trans (EdgePath.incoming_unique N p he hf (ht.trans htf.symm))
  let coin : Hybrid N → Bool := fun h =>
    if hh : ∃ e ∈ es, N.graph.target e = h.1 then Classical.choose (hex h hh) else false
  refine ⟨coin,?_⟩
  intro e he
  let hne := original_edge_target_not_root N e
  refine ⟨hne,?_⟩
  by_cases hy : N.graph.IsHybrid (N.graph.target e)
  · let h : Hybrid N := ⟨N.graph.target e,hy⟩
    have hh : ∃ f ∈ es, N.graph.target f = h.1 := ⟨e,he,rfl⟩
    have hcoin := Classical.choose_spec (hex h hh) e he rfl
    simp only [coinSelector,dif_pos hy]
    change (H.parents h).parent (coin h) = e
    dsimp only [coin]
    rw [dif_pos hh]
    exact hcoin
  · simp only [coinSelector,dif_neg hy]
    exact incoming_equal_of_indegree_le_one N (nonhybrid_indegree_le_one N hy)
      ((defaultSelector N).target ⟨N.graph.target e,hne⟩) rfl

/-- The actual compiler covers every original root-to-vertex path; no route
support oracle or assumption of compiler surjectivity is used. -/
theorem compiledRoute_covers_original_path (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) {v : V} {es : List E}
    (p : EdgePath N.graph N.root v es) :
    ∃ coin : Hybrid N → Bool, compiledRoute N C (coinSelector N H coin) v = es := by
  obtain ⟨coin,hcoin⟩ := original_path_coin_realization N C H p
  refine ⟨coin,?_⟩
  have hs := compiledRoute_source_spec N C (coinSelector N H coin) v
  apply List.reverse_inj.mp
  exact UpPath.eq_of_same_selector N (coinSelector N H coin)
    (GProgram.G5.NonbridgeRoutes.EdgePath.to_upPath_reverse hs.1 (fun _ _ => trivial))
    (GProgram.G5.NonbridgeRoutes.EdgePath.to_upPath_reverse p (fun _ _ => trivial))
    (respectsSelector_reverse N _ hs.2) (respectsSelector_reverse N _ hcoin)

/-- Independent original-tip bit assignments realize ALL original route
families. This is support, not a claim of common global route independence. -/
theorem compiledRouteFamily_covers_original_routes (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (R : RouteFamily N) :
    ∃ coin : X → Hybrid N → Bool, ∀ x, (compiledRouteFamily N C H coin).edges x = R.edges x := by
  have hx : ∀ x, ∃ coin : Hybrid N → Bool,
      compiledRoute N C (coinSelector N H coin) (N.leaf x) = R.edges x :=
    fun x => compiledRoute_covers_original_path N C H (R.valid x)
  exact ⟨fun x => Classical.choose (hx x),fun x => Classical.choose_spec (hx x)⟩

#print axioms EdgePath.incoming_unique
#print axioms original_path_coin_realization
#print axioms compiledRoute_covers_original_path
#print axioms compiledRouteFamily_covers_original_routes
end GProgram.G5.AttainedChronology
