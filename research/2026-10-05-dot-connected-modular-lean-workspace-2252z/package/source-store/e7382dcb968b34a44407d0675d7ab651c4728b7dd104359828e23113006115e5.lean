import NanuqActualOpenedIncidence

/-! Hybrid children label distinct original taxa. These labels, and the
ordinary taxa, form the one-copy/two-copy alphabet of the actual opening. -/
namespace Nanuq.Source.RootedBinary
open scoped Classical
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)
variable (hleaf : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e = N.leaf x)

abbrev HybridVertex := {h : V // N.graph.IsHybrid h}
abbrev OrdinaryTaxon := {x : X // N.SkeletonVertexPredicate (N.leaf x)}

include hleaf in
theorem hybrid_child_taxon_exists (h : N.HybridVertex) :
    ∃ x : X, ∃ e : E, N.graph.source e = h.val ∧ N.graph.target e = N.leaf x := by
  obtain ⟨e,he,hu⟩ := Finset.card_eq_one_iff_existsUnique.mp h.property.2
  have hs := (Finset.mem_filter.mp he).2
  obtain ⟨x,hx⟩ := hleaf e (by rw [hs];exact h.property)
  exact ⟨x,e,hs,hx⟩

noncomputable def hybridChildTaxon (h : N.HybridVertex) : X :=
  Classical.choose (N.hybrid_child_taxon_exists hleaf h)

theorem hybridChildTaxon_spec (h : N.HybridVertex) :
    ∃ e : E, N.graph.source e = h.val ∧ N.graph.target e = N.leaf (N.hybridChildTaxon hleaf h) :=
  Classical.choose_spec (N.hybrid_child_taxon_exists hleaf h)

theorem hybridChildTaxon_outgoing (h : N.HybridVertex) (e : E) (he : N.graph.source e = h.val) :
    N.graph.target e = N.leaf (N.hybridChildTaxon hleaf h) := by
  obtain ⟨f,hf,ht⟩ := N.hybridChildTaxon_spec hleaf h
  rw [N.graph.outgoing_equal_of_degree_one h.property.2 e f he hf]
  exact ht

theorem hybridChildTaxon_injective : Function.Injective (N.hybridChildTaxon hleaf) := by
  intro h k hx
  obtain ⟨e,he,hte⟩ := N.hybridChildTaxon_spec hleaf h
  obtain ⟨f,hf,htf⟩ := N.hybridChildTaxon_spec hleaf k
  obtain ⟨g,hg,hu⟩ := N.incoming_unique_of_indegree_one (N.leaf_degrees (N.hybridChildTaxon hleaf h)).1
  have hfg : N.graph.target f = N.leaf (N.hybridChildTaxon hleaf h) := by rw [htf,hx]
  have hef : e = f := (hu e hte).trans (hu f hfg).symm
  exact Subtype.ext (he.symm.trans ((congrArg N.graph.source hef).trans hf))

theorem hybridChildTaxon_not_ordinary (h : N.HybridVertex) :
    ¬ N.SkeletonVertexPredicate (N.leaf (N.hybridChildTaxon hleaf h)) := by
  intro hp
  obtain ⟨e,he,ht⟩ := N.hybridChildTaxon_spec hleaf h
  exact hp.2 e ht (by rw [he];exact h.property)

theorem nonordinary_taxon_is_hybrid_child (x : X)
    (hx : ¬ N.SkeletonVertexPredicate (N.leaf x)) :
    ∃ h : N.HybridVertex, N.hybridChildTaxon hleaf h = x := by
  have hn : ¬ N.graph.IsHybrid (N.leaf x) := by
    intro hh
    have h1 := (N.leaf_degrees x).1
    have h2 := hh.1
    omega
  have he : ∃ e, N.graph.target e = N.leaf x ∧ N.graph.IsHybrid (N.graph.source e) := by
    by_contra h
    apply hx
    refine ⟨hn,?_⟩
    intro e het heh
    exact h ⟨e,het,heh⟩
  obtain ⟨e,ht,hh⟩ := he
  let h : N.HybridVertex := ⟨N.graph.source e,hh⟩
  refine ⟨h,N.leaf.injective ?_⟩
  exact (N.hybridChildTaxon_outgoing hleaf h e rfl).symm.trans ht
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.hybridChildTaxon_injective
#print axioms Nanuq.Source.RootedBinary.nonordinary_taxon_is_hybrid_child
