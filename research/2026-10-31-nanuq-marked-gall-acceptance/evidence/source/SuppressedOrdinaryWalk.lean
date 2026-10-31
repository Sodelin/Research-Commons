import G1LiteralSemidirectedRootSuppression
import GraphGalls

/-! UNCOMPILED source-faithful ordinary-walk expansion through the literal root.
No CutChild, drawing, cyclic-order or GalledDetour hypothesis is assumed. -/
namespace Nanuq.MarkedGallAdmission
open Nanuq.Source G1ActualFormerRootPorts G1LiteralSemidirectedRootSuppression
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
    [DecidableEq V] [DecidableEq E]
variable (N : RootedBinary V E X) (ports : RootPorts N)

def OrdinaryAvoid (h : V) (e : E) : Prop :=
  ¬N.graph.IsHybrid (N.graph.target e) ∧ N.graph.source e≠h ∧ N.graph.target e≠h

def SuppressedOrdinaryAvoid (h : V) (e : SuppressedEdge N) : Prop :=
  suppressedMark N ports e = .undirected ∧
    ((suppressedGraph N ports).source e).val≠h ∧
    ((suppressedGraph N ports).target e).val≠h

theorem ordinary_suppressed_edge_expansion {h : V} (hroot : h≠N.root)
    (e : SuppressedEdge N) (he : SuppressedOrdinaryAvoid N ports h e) :
    N.graph.UReach (OrdinaryAvoid N h)
      ((suppressedGraph N ports).source e).val ((suppressedGraph N ports).target e).val := by
  cases e with
  | inl e =>
    have hord : ¬N.graph.IsHybrid (N.graph.target e.val) := by
      intro hh
      have hm := he.1
      simp [suppressedMark,hh] at hm
    exact N.graph.ureach_single ⟨e.val,⟨hord,he.2.1,he.2.2⟩,N.graph.inc_source_target e.val⟩
  | inr u =>
    cases u
    have hord := (actual_suppressed_edge_undirected_iff N ports).mp he.1
    have h1 : N.graph.UReach (OrdinaryAvoid N h) (N.graph.target ports.first) N.root :=
      N.graph.ureach_single ⟨ports.first,⟨hord.1,
        by simpa only [ports.source_first] using hroot.symm,he.2.1⟩,
        Or.inr ⟨ports.source_first,rfl⟩⟩
    have h2 : N.graph.UReach (OrdinaryAvoid N h) N.root (N.graph.target ports.second) :=
      N.graph.ureach_single ⟨ports.second,⟨hord.2,
        by simpa only [ports.source_second] using hroot.symm,he.2.2⟩,
        Or.inl ⟨ports.source_second,rfl⟩⟩
    exact h1.trans h2

/-- Every actual ordinary h-avoiding suppressed walk expands to original IDs.
The merged edge is expanded, never treated as a new physical original ID. -/
theorem ordinary_suppressed_walk_expansion {h : V} (hroot : h≠N.root)
    {a b : SuppressedVertex N}
    (hw : (suppressedGraph N ports).UReach (SuppressedOrdinaryAvoid N ports h) a b) :
    N.graph.UReach (OrdinaryAvoid N h) a.val b.val := by
  induction hw with
  | refl => exact .refl
  | tail _ hs ih =>
    obtain ⟨e,he,hinc⟩ := hs
    have hex := ordinary_suppressed_edge_expansion N ports hroot e he
    rcases hinc with ⟨ha,hb⟩ | ⟨ha,hb⟩
    · rw [ha,hb] at hex
      exact ih.trans hex
    · rw [ha,hb] at hex
      exact ih.trans (N.graph.ureach_symm hex)

#print axioms ordinary_suppressed_edge_expansion
#print axioms ordinary_suppressed_walk_expansion
end Nanuq.MarkedGallAdmission
