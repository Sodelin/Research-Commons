import guards.NanuqActualCappedQuartetReadout

set_option debug.skipKernelTC false

/-! Readout transport under a vertex-fixed bijection of individual edge IDs. -/
namespace Nanuq.Source.EdgeGraph
variable {V E F : Type*} (G : EdgeGraph V E) (H : EdgeGraph V F)

theorem reach_without_edge_equiv_forward (e : E ≃ F)
    (hs : ∀ f, H.source (e f) = G.source f)
    (ht : ∀ f, H.target (e f) = G.target f)
    (f : E) {a c : V} (h : G.ReachWithout f a c) : H.ReachWithout (e f) a c := by
  induction h with
  | refl => exact .refl
  | tail _ hstep ih =>
    obtain ⟨g,hgf,hinc⟩ := hstep
    apply ih.tail
    refine ⟨e g,fun heq => hgf (e.injective heq),?_⟩
    rcases hinc with ⟨hsa,hta⟩ | ⟨hsa,hta⟩
    · exact Or.inl ⟨(hs g).trans hsa,(ht g).trans hta⟩
    · exact Or.inr ⟨(hs g).trans hsa,(ht g).trans hta⟩

theorem reach_without_edge_equiv_iff (e : E ≃ F)
    (hs : ∀ f, H.source (e f) = G.source f)
    (ht : ∀ f, H.target (e f) = G.target f)
    (f : E) (a c : V) : G.ReachWithout f a c ↔ H.ReachWithout (e f) a c := by
  constructor
  · exact G.reach_without_edge_equiv_forward H e hs ht f
  · intro h
    have hs' : ∀ g, G.source (e.symm g) = H.source g := by
      intro g
      simpa only [e.apply_symm_apply] using (hs (e.symm g)).symm
    have ht' : ∀ g, G.target (e.symm g) = H.target g := by
      intro g
      simpa only [e.apply_symm_apply] using (ht (e.symm g)).symm
    simpa only [e.symm_apply_apply] using
      H.reach_without_edge_equiv_forward G e.symm hs' ht' (e f) h

theorem bridge_edge_equiv_iff (e : E ≃ F)
    (hs : ∀ f, H.source (e f) = G.source f)
    (ht : ∀ f, H.target (e f) = G.target f) (f : E) :
    G.IsBridge f ↔ H.IsBridge (e f) := by
  unfold IsBridge
  rw [hs f,ht f,← G.reach_without_edge_equiv_iff H e hs ht f]

theorem oriented_quartet_edge_equiv_iff (e : E ≃ F)
    (hs : ∀ f, H.source (e f) = G.source f)
    (ht : ∀ f, H.target (e f) = G.target f) (f : E) (a b c d : V) :
    G.OrientedQuartet f a b c d ↔ H.OrientedQuartet (e f) a b c d := by
  simp only [OrientedQuartet,hs,ht]
  rw [G.reach_without_edge_equiv_iff H e hs ht f,
    G.reach_without_edge_equiv_iff H e hs ht f,
    G.reach_without_edge_equiv_iff H e hs ht f,
    G.reach_without_edge_equiv_iff H e hs ht f]

theorem hasQuartet_edge_equiv_forward (e : E ≃ F)
    (hs : ∀ f, H.source (e f) = G.source f)
    (ht : ∀ f, H.target (e f) = G.target f)
    (a b c d : V) (h : G.HasQuartet a b c d) : H.HasQuartet a b c d := by
  obtain ⟨f,hf,h | h⟩ := h
  · exact ⟨e f,(G.bridge_edge_equiv_iff H e hs ht f).mp hf,
      Or.inl ((G.oriented_quartet_edge_equiv_iff H e hs ht f a b c d).mp h)⟩
  · exact ⟨e f,(G.bridge_edge_equiv_iff H e hs ht f).mp hf,
      Or.inr ((G.oriented_quartet_edge_equiv_iff H e hs ht f c d a b).mp h)⟩

theorem hasQuartet_edge_equiv_iff (e : E ≃ F)
    (hs : ∀ f, H.source (e f) = G.source f)
    (ht : ∀ f, H.target (e f) = G.target f) (a b c d : V) :
    G.HasQuartet a b c d ↔ H.HasQuartet a b c d := by
  constructor
  · exact G.hasQuartet_edge_equiv_forward H e hs ht a b c d
  · apply H.hasQuartet_edge_equiv_forward G e.symm
    · intro g
      simpa only [e.apply_symm_apply] using (hs (e.symm g)).symm
    · intro g
      simpa only [e.apply_symm_apply] using (ht (e.symm g)).symm

theorem resolves_edge_equiv_iff (e : E ≃ F)
    (hs : ∀ f, H.source (e f) = G.source f)
    (ht : ∀ f, H.target (e f) = G.target f)
    (v : Fin 4 → V) (r : Nanuq.Quartet.Resolution) :
    G.Resolves v r ↔ H.Resolves v r := by
  cases r <;> exact G.hasQuartet_edge_equiv_iff H e hs ht _ _ _ _
end Nanuq.Source.EdgeGraph

#print axioms Nanuq.Source.EdgeGraph.resolves_edge_equiv_iff
