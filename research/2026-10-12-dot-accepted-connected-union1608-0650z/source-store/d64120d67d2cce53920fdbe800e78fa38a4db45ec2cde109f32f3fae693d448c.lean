import G1ActualMarkedSemidirectedGalledAdmission

/-! Actual incoming hybrid edge IDs are in bijection with directed incoming
IDs of the literal suppressed multigraph. This is the source of the exact
switching/delete-one correspondence, including a hybrid root incident arc. -/
namespace G1LiteralHybridParentSuppressionBijection
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 G1ActualFormerRootPorts G1FormerRootHybridDirections
open G1LiteralSemidirectedRootSuppression G1RootSubdivisionPlanarAdmission
open G1ActualMarkedSemidirectedGalledAdmission
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

noncomputable def parentImage (N : RootedBinary V E X) (ports : RootPorts N) (e : E) : SuppressedEdge N :=
  if hf : e = ports.first then .inr () else if hs : e = ports.second then .inr ()
    else .inl ⟨e,fun hr => (ports.exhaustive e hr).elim hf hs⟩
noncomputable def originalParent (N : RootedBinary V E X) (ports : RootPorts N) : SuppressedEdge N → E
  | .inl e => e.val
  | .inr _ => if N.graph.IsHybrid (N.graph.target ports.first) then ports.first else ports.second

@[simp] theorem parentImage_first (N : RootedBinary V E X) (ports : RootPorts N) :
    parentImage N ports ports.first = .inr () := by simp [parentImage]
@[simp] theorem parentImage_second (N : RootedBinary V E X) (ports : RootPorts N) :
    parentImage N ports ports.second = .inr () := by simp [parentImage,Ne.symm ports.different]
@[simp] theorem parentImage_kept (N : RootedBinary V E X) (ports : RootPorts N) (e : KeptEdge N) :
    parentImage N ports e.val = .inl e := by
  have hf : e.val ≠ ports.first := fun h => e.property (h ▸ ports.source_first)
  have hs : e.val ≠ ports.second := fun h => e.property (h ▸ ports.source_second)
  simp [parentImage,hf,hs]

theorem actual_parent_image_is_marked (N : RootedBinary V E X) (ports : RootPorts N)
    (v : SuppressedVertex N) (hh : N.graph.IsHybrid v.val) (e : E) (ht : N.graph.target e = v.val) :
    MarkedIncoming N ports (parentImage N ports e) v := by
  rcases actual_original_edge_cases N ports e with hf | hs | hk
  · subst e; rw [parentImage_first]
    exact Or.inr ⟨(actual_suppressed_edge_towards_first_iff N ports).mpr (ht ▸ hh),Subtype.ext ht⟩
  · subst e; rw [parentImage_second]
    exact Or.inl ⟨(actual_suppressed_edge_towards_second_iff N ports).mpr (ht ▸ hh),Subtype.ext ht⟩
  · rw [parentImage_kept N ports ⟨e,hk⟩]
    exact Or.inl ⟨by simp [suppressedMark,ht,hh],Subtype.ext ht⟩

theorem actual_original_parent_target (N : RootedBinary V E X) (ports : RootPorts N)
    (v : SuppressedVertex N) (e : SuppressedEdge N) (hm : MarkedIncoming N ports e v) :
    N.graph.target (originalParent N ports e) = v.val := by
  cases e with
  | inl e =>
    rcases hm with ⟨hmark,ht⟩ | ⟨hmark,hs⟩
    · exact congrArg Subtype.val ht
    · by_cases hh : N.graph.IsHybrid (N.graph.target e.val) <;> simp [suppressedMark,hh] at hmark
  | inr e =>
    cases e
    rcases hm with ⟨hmark,ht⟩ | ⟨hmark,hs⟩
    · have hh := (actual_suppressed_edge_towards_second_iff N ports).mp hmark
      have hfirst : ¬ N.graph.IsHybrid (N.graph.target ports.first) := fun hf =>
        actual_root_has_at_most_one_hybrid_child N ports ⟨hf,hh⟩
      simp only [originalParent,if_neg hfirst]
      exact congrArg Subtype.val ht
    · have hh := (actual_suppressed_edge_towards_first_iff N ports).mp hmark
      simp only [originalParent,if_pos hh]
      exact congrArg Subtype.val hs

theorem actual_parent_image_original_inverse (N : RootedBinary V E X) (ports : RootPorts N)
    (e : SuppressedEdge N) : parentImage N ports (originalParent N ports e) = e := by
  cases e with
  | inl e => exact parentImage_kept N ports e
  | inr e =>
    cases e
    by_cases hh : N.graph.IsHybrid (N.graph.target ports.first) <;>
      simp [originalParent,hh]

theorem actual_original_parent_image_inverse (N : RootedBinary V E X) (ports : RootPorts N)
    (e : E) (hh : N.graph.IsHybrid (N.graph.target e)) :
    originalParent N ports (parentImage N ports e) = e := by
  rcases actual_original_edge_cases N ports e with hf | hs | hk
  · subst e; simp [originalParent,hh]
  · subst e
    have hfirst : ¬ N.graph.IsHybrid (N.graph.target ports.first) := fun hf =>
      actual_root_has_at_most_one_hybrid_child N ports ⟨hf,hh⟩
    simp [originalParent,hfirst]
  · rw [parentImage_kept N ports ⟨e,hk⟩]
    rfl

/-- Literal original-parent ↔ marked semidirected-parent ID equivalence.
There is no supplied switching/target equality or renamed hidden edge choice. -/
noncomputable def actualHybridParentEquiv (N : RootedBinary V E X) (ports : RootPorts N)
    (v : SuppressedVertex N) (hh : N.graph.IsHybrid v.val) :
    {e : E // N.graph.target e = v.val} ≃ {e : SuppressedEdge N // MarkedIncoming N ports e v} where
  toFun e := ⟨parentImage N ports e.val,actual_parent_image_is_marked N ports v hh e.val e.property⟩
  invFun e := ⟨originalParent N ports e.val,actual_original_parent_target N ports v e.val e.property⟩
  left_inv e := Subtype.ext (actual_original_parent_image_inverse N ports e.val (by rw [e.property]; exact hh))
  right_inv e := Subtype.ext (actual_parent_image_original_inverse N ports e.val)

#print axioms actualHybridParentEquiv
end G1LiteralHybridParentSuppressionBijection
