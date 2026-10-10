import G1SourceMacroActualCompletion

/-! Every original exterior descendant-labelled causal view is recovered by
grafting the SAME entering opaque subtrees into its CURRENT-root view.
Contributor: dot, 2026-10-03. No original descendant-count cap is introduced. -/
namespace G1OriginalOpaqueExteriorView
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1OpaqueSourceGrafting G1OriginalCurrentRootReconstruction
open G1UnrankedSourceView G1UnrankedActualFuture G1OriginalWholeCausalView
open G1JointUnrankedForestAssembly
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma graftInput_leaf_membership (input : Copy → Genealogy Copy) (t : Genealogy Copy) (x : Copy) :
    x ∈ (graftInput input t).leaves ↔ ∃ l ∈ t.leaves, x ∈ (input l).leaves := by
  induction t with
  | leaf l => simp [graftInput,Genealogy.leaves]
  | graft a b ha hb =>
    simp only [graftInput,Genealogy.leaves,Finset.mem_union,ha,hb]
    constructor
    · rintro (⟨l,hl,hx⟩ | ⟨l,hl,hx⟩)
      · exact ⟨l,Or.inl hl,hx⟩
      · exact ⟨l,Or.inr hl,hx⟩
    · rintro ⟨l,(hl | hl),hx⟩
      · exact Or.inl ⟨l,hl,hx⟩
      · exact Or.inr ⟨l,hl,hx⟩

/-- Actual supported graft reconstruction derives no splitting of any OLD
opaque subtree; no cohort equivalence is assumed as an extra source field. -/
theorem actual_reconstruction_cohort (initial d : State V E Copy)
    (hi : Valid initial) (hd : Valid d) (hr : Reconstructs initial.genealogy initial.live d)
    (x : Copy) : d.ancestor x = d.ancestor (initial.ancestor x) := by
  let owner := d.ancestor x
  have ho := hd.ancestor_live x
  obtain ⟨t,ht,hg⟩ := hr.genealogy owner ho
  have hx : x ∈ (graftInput initial.genealogy t).leaves := by
    rw [hg]
    exact (hd.leaf_fiber owner ho x).mpr rfl
  obtain ⟨l,hl,hxl⟩ := (graftInput_leaf_membership initial.genealogy t x).mp hx
  have hleaf : t.leaves = (d.genealogy owner).leaves ∩ initial.live := by
    have h := Genealogy.prune_leaves initial.live (d.genealogy owner)
    rw [ht] at h
    exact h
  have hli : l ∈ initial.live := (Finset.mem_inter.mp (hleaf ▸ hl)).2
  have hinit : initial.ancestor x = l := (hi.leaf_fiber l hli x).mp hxl
  have hld : d.ancestor l = owner :=
    (hd.leaf_fiber owner ho l).mp (Finset.mem_inter.mp (hleaf ▸ hl)).1
  rw [hinit,hld]

noncomputable def originalExteriorCopies (initial : State V E Copy) (outside : Finset Copy) : Finset Copy :=
  Finset.univ.filter (fun x => initial.ancestor x ∈ outside)

noncomputable def opaqueExteriorView (initial : State V E Copy) (outside : Finset Copy)
    (v : UnrankedView V E Copy) : UnrankedView V E Copy where
  genealogy x := if initial.ancestor x ∈ outside then
    (v.genealogy (initial.ancestor x)).map (graftUnranked initial.genealogy) else none
  population x := if initial.ancestor x ∈ outside then v.population (initial.ancestor x) else none
  register := v.register

/-- Full original exterior subtrees, all original descendant labels, actual
populations and SAME register are recovered at EACH pure supported checkpoint.
The outside CURRENT-root carrier can be much smaller than its old descendants. -/
theorem actual_opaque_original_exterior_view (initial d : State V E Copy)
    (hi : Valid initial) (hd : Valid d) (hr : Reconstructs initial.genealogy initial.live d)
    (inside outside : Finset Copy) (partition : inside ∪ outside = initial.live)
    (pure : PrunedPanelSeparated d inside outside) :
    opaqueExteriorView initial outside (unrankedView (selectedView d outside)) =
      unrankedView (selectedView d (originalExteriorCopies initial outside)) := by
  apply UnrankedView.ext
  · funext x
    by_cases hx : initial.ancestor x ∈ outside
    · have hxo : x ∈ originalExteriorCopies initial outside := by simp [originalExteriorCopies,hx]
      let owner := d.ancestor (initial.ancestor x)
      have howner : d.ancestor x = owner := actual_reconstruction_cohort initial d hi hd hr x
      have holive := hd.ancestor_live (initial.ancestor x)
      have hrootleaf : initial.ancestor x ∈ (d.genealogy owner).leaves := (hd.leaf_fiber owner holive _).mpr rfl
      have hpruneOutside : (d.genealogy owner).prune outside ≠ none := by
        intro hn
        have hm := Finset.mem_inter.mpr ⟨hrootleaf,hx⟩
        rw [(prune_none_iff_no_selected_leaves outside _).mp hn] at hm
        exact Finset.notMem_empty _ hm
      have hinside : (d.genealogy owner).prune inside = none := (pure owner holive).resolve_right hpruneOutside
      obtain ⟨t,ht,hg⟩ := hr.genealogy owner holive
      have htout : (d.genealogy owner).prune outside = some t := by
        rw [← partition,prune_union_of_left_empty _ inside outside hinside] at ht
        exact ht
      have hsubset : (d.genealogy owner).leaves ⊆ originalExteriorCopies initial outside := by
        intro y hy
        have hdy : d.ancestor y = owner := (hd.leaf_fiber owner holive y).mp hy
        have hcohort := actual_reconstruction_cohort initial d hi hd hr y
        have hroot : initial.ancestor y ∈ (d.genealogy owner).leaves :=
          (hd.leaf_fiber owner holive _).mpr (hcohort.symm.trans hdy)
        have hykeep : initial.ancestor y ∈ inside ∪ outside := partition.symm ▸ hi.ancestor_live y
        have hyout : initial.ancestor y ∈ outside := by
          rcases Finset.mem_union.mp hykeep with hin | hout
          · have hm := Finset.mem_inter.mpr ⟨hroot,hin⟩
            rw [(prune_none_iff_no_selected_leaves inside _).mp hinside] at hm
            exact False.elim (Finset.notMem_empty _ hm)
          · exact hout
        simp [originalExteriorCopies,hyout]
      have hfull : (d.genealogy owner).prune (originalExteriorCopies initial outside) =
          some (d.genealogy owner) :=
        (prune_eq_of_leaf_membership _ _ Finset.univ (fun y hy => by simp [hsubset hy])).trans (prune_all _)
      simp only [opaqueExteriorView,if_pos hx,unrankedView,selectedView,selectedGenealogy,
        if_pos hx,if_pos hxo,howner,htout,optionUnranked,Option.map_some,graftUnranked_toUnranked,hg,hfull]
      change Option.map (graftUnranked initial.genealogy)
        (Option.map toUnranked ((d.genealogy owner).prune outside)) = some (toUnranked (d.genealogy owner))
      rw [htout]
      simp only [Option.map_some,graftUnranked_toUnranked,hg]
    · have hxo : x ∉ originalExteriorCopies initial outside := by simp [originalExteriorCopies,hx]
      simp [opaqueExteriorView,unrankedView,selectedView,selectedGenealogy,hx,hxo,optionUnranked]
  · funext x
    by_cases hx : initial.ancestor x ∈ outside
    · have hxo : x ∈ originalExteriorCopies initial outside := by simp [originalExteriorCopies,hx]
      have hc := actual_reconstruction_cohort initial d hi hd hr x
      have hp := merged_copies_same_population d hc
      simpa [opaqueExteriorView,unrankedView,selectedView,selectedLocation,hx,hxo] using congrArg some hp.symm
    · have hxo : x ∉ originalExteriorCopies initial outside := by simp [originalExteriorCopies,hx]
      simp [opaqueExteriorView,unrankedView,selectedView,selectedLocation,hx,hxo]
  · rfl

#print axioms actual_reconstruction_cohort
#print axioms actual_opaque_original_exterior_view
end G1OriginalOpaqueExteriorView
