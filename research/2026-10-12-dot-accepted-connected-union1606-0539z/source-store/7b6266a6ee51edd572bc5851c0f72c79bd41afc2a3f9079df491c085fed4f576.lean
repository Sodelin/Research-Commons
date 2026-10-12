import G1DecoratedOriginalProvenance

/-! Every future removed bigon lifts to the SAME original registry site and
original parallel population IDs. Contributor: dot, 2026-10-03. Synthetic
bridge recipes can never masquerade as original hybrid-parent populations. -/
namespace G1LiftedOriginalBigon
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.G2
open UnifiedLean.Source.NativeParentRouting
open G1ActualGraphNormalization G1OriginalDecoratedSpan G1DecoratedOriginalProvenance
open G1ActualTwoPortBlob G1CutChildPorts G1NonrootBigonKernel
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

lemma actual_fragment_parent_target (S : Source X) (b : S.network.graph.Blob)
    (A : ActualBlobBigon S.network b) (bit : Bool) :
    S.network.graph.target (A.fragment.parents.parent bit) = A.fragment.parents.hybrid := by
  cases bit <;> simp [OriginalHybridParents.parent,A.fragment.parents.target0,A.fragment.parents.target1]

noncomputable def rawOriginalParent (O S : Source X) (D : Decoration O S)
    (b : S.network.graph.Blob) (A : ActualBlobBigon S.network b) (bit : Bool) : O.Edge :=
  Classical.choose (D.raw_nonbridge (A.fragment.parents.parent bit) (by
    intro hb
    exact actual_hybrid_parent_nonbridge S.network _
      ((actual_fragment_parent_target S b A bit).symm ▸ A.fragment.parents.isHybrid) hb))

lemma actual_raw_original_parent_recipe (O S : Source X) (D : Decoration O S)
    (b : S.network.graph.Blob) (A : ActualBlobBigon S.network b) (bit : Bool) :
    D.recipe (A.fragment.parents.parent bit) = .raw (rawOriginalParent O S D b A bit) :=
  Classical.choose_spec (D.raw_nonbridge (A.fragment.parents.parent bit) (by
    intro hb
    exact actual_hybrid_parent_nonbridge S.network _
      ((actual_fragment_parent_target S b A bit).symm ▸ A.fragment.parents.isHybrid) hb))

lemma actual_raw_original_parent_target (O S : Source X) (D : Decoration O S)
    (b : S.network.graph.Blob) (A : ActualBlobBigon S.network b) (bit : Bool) :
    O.network.graph.target (rawOriginalParent O S D b A bit) = D.vertex A.fragment.parents.hybrid := by
  have h := (D.endpoints (A.fragment.parents.parent bit)).1
  rw [actual_raw_original_parent_recipe] at h
  change O.network.graph.target (rawOriginalParent O S D b A bit) =
    D.vertex (S.network.graph.target (A.fragment.parents.parent bit)) at h
  exact h.trans (congrArg D.vertex (actual_fragment_parent_target S b A bit))

lemma actual_raw_original_parent_source (O S : Source X) (D : Decoration O S)
    (b : S.network.graph.Blob) (A : ActualBlobBigon S.network b) (bit : Bool) :
    O.network.graph.source (rawOriginalParent O S D b A bit) = D.vertex A.fragment.upper := by
  have h := (D.endpoints (A.fragment.parents.parent bit)).2
  rw [actual_raw_original_parent_recipe] at h
  change O.network.graph.source (rawOriginalParent O S D b A bit) =
    D.vertex (S.network.graph.source (A.fragment.parents.parent bit)) at h
  exact h.trans (congrArg D.vertex (A.fragment.arm_sources bit))

lemma actual_raw_original_parents_different (O S : Source X) (D : Decoration O S)
    (b : S.network.graph.Blob) (A : ActualBlobBigon S.network b) :
    rawOriginalParent O S D b A false ≠ rawOriginalParent O S D b A true := by
  intro heq
  have h0 := actual_raw_original_parent_recipe O S D b A false
  have h1 := actual_raw_original_parent_recipe O S D b A true
  rw [← heq] at h1
  have hp := D.raw_injective _ _ _ h0 h1
  exact A.fragment.parents.different (by simpa [OriginalHybridParents.parent] using hp)

noncomputable def originalHybridSite (O S : Source X) (D : Decoration O S)
    (b : S.network.graph.Blob) (A : ActualBlobBigon S.network b) : Hybrid O.network :=
  ⟨D.vertex A.fragment.parents.hybrid,(actual_decoration_hybrid_iff O S D _).mp A.fragment.parents.isHybrid⟩

/-- The ORIGINAL supplied registry pair is used, including nonfair gamma and
COMMON coordinate. It is not the arbitrary order of a later graph extraction. -/
noncomputable def liftedOriginalFragment (O S : Source X) (D : Decoration O S)
    (H : OriginalParentRegistry O.network) (b : S.network.graph.Blob)
    (A : ActualBlobBigon S.network b) : NonrootBigon O.network where
  parents := H.parents (originalHybridSite O S D b A)
  upper := D.vertex A.fragment.upper
  upper_nonroot := by
    intro h
    exact A.fragment.upper_nonroot (D.vertex.injective (h.trans D.root.symm))
  arm_sources bit := by
    let site := D.vertex A.fragment.parents.hybrid
    let es := Finset.univ.filter (fun e : O.Edge => O.network.graph.target e = site)
    have hsite : O.network.graph.IsHybrid site := (originalHybridSite O S D b A).property
    have h0 : rawOriginalParent O S D b A false ∈ es := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,actual_raw_original_parent_target O S D b A false⟩
    have h1 : rawOriginalParent O S D b A true ∈ es := Finset.mem_filter.mpr
      ⟨Finset.mem_univ _,actual_raw_original_parent_target O S D b A true⟩
    have htarget : O.network.graph.target ((H.parents (originalHybridSite O S D b A)).parent bit) = site :=
      registry_parent_target O.network H (originalHybridSite O S D b A) bit
    have he := edge_pair_exhaustive es _ _ (actual_raw_original_parents_different O S D b A)
      h0 h1 hsite.1 _ (Finset.mem_filter.mpr ⟨Finset.mem_univ _,htarget⟩)
    rcases he with he | he
    · rw [he]; exact actual_raw_original_parent_source O S D b A false
    · rw [he]; exact actual_raw_original_parent_source O S D b A true

/-- Literal original word for a later physical component: inherited bridge
labels, original registry pulse/arms, then inherited bridge label. -/
noncomputable def newOriginalSpan (O S : Source X) (D : Decoration O S)
    (H : OriginalParentRegistry O.network) (b : S.network.graph.Blob)
    (A : ActualBlobBigon S.network b) :
    OriginalSpan O.network (D.vertex (S.network.graph.target A.child)) (D.vertex (S.network.graph.source A.entry)) := by
  have cw : OriginalSpan O.network (D.vertex (S.network.graph.target A.child))
      (D.vertex A.fragment.parents.hybrid) := by
    rw [← A.child_source]
    exact bridgeSpan O S D A.child A.child_bridge
  have aw : OriginalSpan O.network (D.vertex A.fragment.parents.hybrid) (D.vertex A.fragment.upper) := by
    have h := OriginalSpan.bigon (liftedOriginalFragment O S D H b A)
    simpa only [liftedOriginalFragment,H.original_site,originalHybridSite] using h
  have ew : OriginalSpan O.network (D.vertex A.fragment.upper) (D.vertex (S.network.graph.source A.entry)) := by
    rw [← A.entry_target]
    exact bridgeSpan O S D A.entry A.entry_bridge
  exact .append cw (.append aw ew)

end G1LiftedOriginalBigon
