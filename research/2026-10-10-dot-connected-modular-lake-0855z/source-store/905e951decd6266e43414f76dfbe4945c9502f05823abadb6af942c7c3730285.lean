import G1LiteralSemidirectedSwitchingTransport

/-! The actual switching transports retain EXACT keep predicates in both
directions. Ordinary root arcs remain kept even when the hybrid suppressed
edge is deleted; no dangling-root artefact leaks into the target interface. -/
namespace G1SemidirectedSwitchingRoundTrip
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 G1ActualFormerRootPorts G1LiteralSemidirectedRootSuppression
open G1ActualMarkedSemidirectedGalledAdmission G1LiteralHybridParentSuppressionBijection
open G1LiteralSemidirectedSwitchingTransport G1FormerRootHybridDirections
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

theorem actual_rooted_switching_round_trip (N : RootedBinary V E X) (ports : RootPorts N)
    (S : N.Switching) (e : E) :
    (toRootedSwitching N ports (toSemidirectedSwitching N ports S)).keep e ↔ S.keep e := by
  by_cases hh : N.graph.IsHybrid (N.graph.target e)
  · let v : SuppressedVertex N := ⟨N.graph.target e,G1RootSuppressionCutChildTransport.actual_hybrid_nonroot N _ hh⟩
    have hm := actual_parent_image_is_marked N ports v hh e rfl
    change originalKeep N ports (toSemidirectedSwitching N ports S) e ↔ _
    simp only [originalKeep,if_pos hh]
    change suppressedKeep N ports S (parentImage N ports e) ↔ _
    rw [actual_marked_parent_keep N ports S v _ hm,actual_original_parent_image_inverse N ports e hh]
  · change originalKeep N ports (toSemidirectedSwitching N ports S) e ↔ _
    simp [originalKeep,hh,S.ordinary e hh]

theorem actual_semidirected_switching_round_trip (N : RootedBinary V E X) (ports : RootPorts N)
    (M : SemidirectedSwitching N ports) (e : SuppressedEdge N) :
    (toSemidirectedSwitching N ports (toRootedSwitching N ports M)).keep e ↔ M.keep e := by
  cases e with
  | inl e =>
    change originalKeep N ports M e.val ↔ M.keep (.inl e)
    by_cases hh : N.graph.IsHybrid (N.graph.target e.val)
    · simp [originalKeep,hh]
    · have hk := M.ordinary (.inl e) (by simp [suppressedMark,hh])
      simp [originalKeep,hh,hk]
  | inr e =>
    cases e
    change (originalKeep N ports M ports.first ∧ originalKeep N ports M ports.second) ↔ M.keep (.inr ())
    by_cases hf : N.graph.IsHybrid (N.graph.target ports.first)
    · have hs : ¬ N.graph.IsHybrid (N.graph.target ports.second) := fun h =>
        actual_root_has_at_most_one_hybrid_child N ports ⟨hf,h⟩
      simp [originalKeep,hf,hs]
    · by_cases hs : N.graph.IsHybrid (N.graph.target ports.second)
      · simp [originalKeep,hf,hs]
      · have hk := M.ordinary (.inr ()) (by simp [suppressedMark,hf,hs])
        simp [originalKeep,hf,hs,hk]

#print axioms actual_semidirected_switching_round_trip
end G1SemidirectedSwitchingRoundTrip
