import SuppressedOrdinaryWalk
import OriginalSimpleGallDetour
import G1ActualMarkedSemidirectedGalledAdmission

/-! UNCOMPILED exact incoming-ID and parent-endpoint transport. RootPorts and
its no-double-hybrid theorem are derived from RootedBinary, not CutChild. -/
namespace Nanuq.MarkedGallAdmission
open Nanuq.Source Nanuq.SimpleGallAdmission
open G1ActualFormerRootPorts G1LiteralSemidirectedRootSuppression
open G1FormerRootHybridDirections G1ActualMarkedSemidirectedGalledAdmission
open G1RootSuppressionCutChildTransport
open scoped Classical Graph
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
    [DecidableEq V] [DecidableEq E]
variable (N : RootedBinary V E X) (ports : RootPorts N)

def incomingID (e : E) : SuppressedEdge N :=
  if hs : N.graph.source e=N.root then .inr () else .inl ⟨e,hs⟩

theorem incoming_ids_distinct {h : V} {e f : E} (hef : e≠f)
    (he : N.graph.target e=h) (hf : N.graph.target f=h) :
    incomingID N e ≠ incomingID N f := by
  have hnotboth : ¬(N.graph.source e=N.root ∧ N.graph.source f=N.root) := by
    rintro ⟨hs,ht⟩
    rcases ports.exhaustive e hs with rfl | rfl <;>
      rcases ports.exhaustive f ht with rfl | rfl
    · exact hef rfl
    · exact actual_root_children_distinct N ports (he.trans hf.symm)
    · exact actual_root_children_distinct N ports (hf.trans he.symm)
    · exact hef rfl
  intro hid
  by_cases hs : N.graph.source e=N.root
  · by_cases ht : N.graph.source f=N.root
    · exact hnotboth ⟨hs,ht⟩
    · simp [incomingID,hs,ht] at hid
  · by_cases ht : N.graph.source f=N.root
    · simp [incomingID,hs,ht] at hid
    · have hsub : (⟨e,hs⟩ : KeptEdge N)=⟨f,ht⟩ :=
        Sum.inl.inj (by simpa only [incomingID,dif_neg hs,dif_neg ht] using hid)
      exact hef (congrArg Subtype.val hsub)

/-- The opposite endpoint of the marked suppressed incoming edge is joined
back to the ORIGINAL parent by ordinary h-avoiding ORIGINAL IDs. -/
theorem incoming_parent_transport {h : V} (hh : N.graph.IsHybrid h) {e : E}
    (he : N.graph.target e=h) :
    ∃ a : SuppressedVertex N,
      (originalGraph (suppressedGraph N ports)).IsLink (incomingID N e)
        ⟨h,actual_hybrid_nonroot N h hh⟩ a ∧
      MarkedIncoming N ports (incomingID N e) ⟨h,actual_hybrid_nonroot N h hh⟩ ∧
      N.graph.UReach (OrdinaryAvoid N h) (N.graph.source e) a.val := by
  have hroot := actual_hybrid_nonroot N h hh
  by_cases hs : N.graph.source e=N.root
  · rcases ports.exhaustive e hs with rfl | rfl
    · have hfirst : N.graph.IsHybrid (N.graph.target ports.first) := he.symm ▸ hh
      have hsecond : ¬N.graph.IsHybrid (N.graph.target ports.second) :=
        fun hh2 => actual_root_has_at_most_one_hybrid_child N ports ⟨hfirst,hh2⟩
      have hother : N.graph.target ports.second≠h :=
        fun heq => actual_root_children_distinct N ports (he.trans heq.symm)
      refine ⟨secondChild N ports,?_,?_,?_⟩
      · simp only [incomingID,dif_pos ports.source_first]
        exact Or.inl ⟨Subtype.ext he,rfl⟩
      · apply Or.inr
        constructor
        · simpa only [incomingID,dif_pos ports.source_first] using
            (actual_suppressed_edge_towards_first_iff N ports).mpr hfirst
        · simp only [incomingID,dif_pos ports.source_first]
          exact Subtype.ext he
      · change N.graph.UReach (OrdinaryAvoid N h) (N.graph.source ports.first)
          (N.graph.target ports.second)
        rw [ports.source_first]
        exact N.graph.ureach_single ⟨ports.second,⟨hsecond,
          by simpa only [ports.source_second] using hroot.symm,hother⟩,
          Or.inl ⟨ports.source_second,rfl⟩⟩
    · have hsecond : N.graph.IsHybrid (N.graph.target ports.second) := he.symm ▸ hh
      have hfirst : ¬N.graph.IsHybrid (N.graph.target ports.first) :=
        fun hh1 => actual_root_has_at_most_one_hybrid_child N ports ⟨hh1,hsecond⟩
      have hother : N.graph.target ports.first≠h :=
        fun heq => actual_root_children_distinct N ports (heq.trans he.symm)
      refine ⟨firstChild N ports,?_,?_,?_⟩
      · simp only [incomingID,dif_pos ports.source_second]
        exact Or.inr ⟨rfl,Subtype.ext he⟩
      · apply Or.inl
        constructor
        · simpa only [incomingID,dif_pos ports.source_second] using
            (actual_suppressed_edge_towards_second_iff N ports).mpr hsecond
        · simp only [incomingID,dif_pos ports.source_second]
          exact Subtype.ext he
      · change N.graph.UReach (OrdinaryAvoid N h) (N.graph.source ports.second)
          (N.graph.target ports.first)
        rw [ports.source_second]
        exact N.graph.ureach_single ⟨ports.first,⟨hfirst,
          by simpa only [ports.source_first] using hroot.symm,hother⟩,
          Or.inl ⟨ports.source_first,rfl⟩⟩
  · refine ⟨keptSource N ⟨e,hs⟩,?_,?_,?_⟩
    · simp only [incomingID,dif_neg hs]
      exact Or.inr ⟨rfl,Subtype.ext he⟩
    · apply Or.inl
      constructor
      · simp [incomingID,hs,suppressedMark,he,hh]
      · simp only [incomingID,dif_neg hs]
        exact Subtype.ext he
    · exact .refl

#print axioms incoming_ids_distinct
#print axioms incoming_parent_transport
end Nanuq.MarkedGallAdmission
