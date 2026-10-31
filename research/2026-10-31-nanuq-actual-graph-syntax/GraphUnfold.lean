import SourceNetwork
import Mathlib.Data.Fintype.EquivFin
set_option debug.skipKernelTC false
namespace Nanuq.GraphSyntax
open Nanuq.Source

inductive BinarySyntax (V : Type*) where
  | tip : V → BinarySyntax V
  | fork : V → BinarySyntax V → BinarySyntax V → BinarySyntax V

variable {V E : Type*} [fv : Fintype V] [Fintype E] [DecidableEq V]

/-- An exact annotated binary expansion of original outgoing edge IDs.
No plane order, adjacency of duplicated tips, or cut-witness conclusion is a field. -/
inductive Represents (G : EdgeGraph V E) : BinarySyntax V → V → Prop where
  | tip (v : V) (h : G.outDegree v = 0) : Represents G (.tip v) v
  | fork (v : V) (e f : E) (hne : e ≠ f)
      (he : G.source e = v) (hf : G.source f = v)
      (hall : ∀ g, G.source g = v → g = e ∨ g = f)
      {l r : BinarySyntax V}
      (hl : Represents G l (G.target e)) (hr : Represents G r (G.target f)) :
      Represents G (.fork v l r) v

include fv

/-- Finite acyclicity supplies termination; it is not assumed as an unfolding oracle. -/
theorem child_wellFounded (G : EdgeGraph V E) (ha : G.Acyclic) :
    WellFounded (fun child parent => Relation.TransGen G.DStep parent child) := by
  have hfin : Finite V := inferInstance
  let R := fun child parent => Relation.TransGen G.DStep parent child
  letI : IsTrans V R := ⟨fun a b c hab hbc => hbc.trans hab⟩
  letI : Std.Irrefl R := ⟨ha⟩
  exact Finite.wellFounded_of_trans_of_irrefl R


/-- Every finite acyclic binary directed graph has a concrete outgoing-edge
expansion. Repeated vertices are not yet excluded: that separate uniqueness
obligation will use actual opened-tree unique incoming/rootedness. -/
theorem exists_represents (G : EdgeGraph V E) (ha : G.Acyclic)
    (hb : ∀ v, G.outDegree v = 0 ∨ G.outDegree v = 2) (v : V) :
    ∃ t, Represents G t v := by
  classical
  induction v using (child_wellFounded G ha).induction with
  | h v ih =>
    rcases hb v with hv | hv
    · exact ⟨.tip v, .tip v hv⟩
    · obtain ⟨e, f, hef, heq⟩ := Finset.card_eq_two.mp hv
      have he : G.source e = v := by
        have hm : e ∈ Finset.univ.filter (fun g => G.source g = v) := by rw [heq]; simp
        exact (Finset.mem_filter.mp hm).2
      have hf : G.source f = v := by
        have hm : f ∈ Finset.univ.filter (fun g => G.source g = v) := by rw [heq]; simp
        exact (Finset.mem_filter.mp hm).2
      obtain ⟨l, hl⟩ := ih (G.target e) (.single ⟨e, he, rfl⟩)
      obtain ⟨r, hr⟩ := ih (G.target f) (.single ⟨f, hf, rfl⟩)
      refine ⟨.fork v l r, .fork v e f hef he hf ?_ hl hr⟩
      intro g hg
      have hm : g ∈ Finset.univ.filter (fun g => G.source g = v) := by simp [hg]
      rw [heq] at hm
      simpa using hm

#print axioms child_wellFounded
#print axioms exists_represents
end Nanuq.GraphSyntax
