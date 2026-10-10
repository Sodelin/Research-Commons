import G1ContextualForestReplacement
import UnifiedLean.Source.SourceUnrankedCopyProjectivity
import UnifiedLean.Source.SourceCrossCarrierProgram

/-!
# Reconstruction from current entering roots in the original source

Contributor: dot, 2026-10-03. This is the original all-descendant-labelled
source binding for the arbitrary opaque-tree interface. Initial CURRENT live
representatives are the retained panel. Their already-formed trees are never
split, and every future complete tree is reconstructed by grafting them into
the root-panel tree. The current entering-root cap is independent of the
number of original descendant/sample labels.
-/
namespace G1OriginalCurrentRootReconstruction
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open G1OpaqueSourceGrafting G1ContextualForestReplacement
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceCrossCarrierEpoch
open UnifiedLean.Source.SourceCrossCarrierProgram
open UnifiedLean.Source.SourceUnrankedCopyProjectivity
open scoped Classical NNReal
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma wellLabelled_singleton_tree (t : Genealogy Copy) (ht : t.WellLabelled)
    (l : Copy) (hleaves : t.leaves = {l}) : t = .leaf l := by
  cases t with
  | leaf x => exact congrArg Genealogy.leaf (Finset.singleton_inj.mp hleaves)
  | graft a b =>
      obtain ⟨x,hx⟩ := genealogy_leaves_nonempty a
      obtain ⟨y,hy⟩ := genealogy_leaves_nonempty b
      have hxl : x = l := Finset.mem_singleton.mp
        (hleaves ▸ Finset.mem_union.mpr (Or.inl hx))
      have hyl : y = l := Finset.mem_singleton.mp
        (hleaves ▸ Finset.mem_union.mpr (Or.inr hy))
      subst x; subst y
      exact False.elim (Finset.disjoint_left.mp ht.2.2 hx hy)

lemma prune_singleton_tree (keep : Finset Copy) (t : Genealogy Copy) (ht : t.WellLabelled)
    (l : Copy) (hleaves : t.leaves ∩ keep = {l}) : t.prune keep = some (.leaf l) := by
  have hp := Genealogy.prune_leaves keep t
  have hw := Genealogy.prune_wellLabelled keep t ht
  cases he : t.prune keep with
  | none =>
      rw [he,hleaves] at hp
      change (∅ : Finset Copy) = {l} at hp
      have hh : l ∈ (∅ : Finset Copy) := hp.symm ▸ Finset.mem_singleton_self l
      exact False.elim (Finset.notMem_empty l hh)
  | some q =>
      rw [he] at hp hw
      rw [wellLabelled_singleton_tree q hw l (hp.trans hleaves)]

omit [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] in
/-- A live original representative is the unique selected leaf in its whole
current tree. None of its other descendants is promoted to an input token. -/
theorem initial_live_root_prune (s : State V E Copy) (hs : Valid s) {l : Copy} (hl : l ∈ s.live) :
    (s.genealogy l).prune s.live = some (.leaf l) := by
  apply prune_singleton_tree s.live _ (hs.wellLabelled l hl) l
  ext x
  rw [Finset.mem_inter,hs.leaf_fiber l hl x,Finset.mem_singleton]
  constructor
  · rintro ⟨hx,hxl⟩
    exact (hs.representative x hxl).symm.trans hx
  · intro hx
    subst x
    exact ⟨hs.representative l hl,hl⟩

structure Reconstructs (input : Copy → Genealogy Copy) (keep : Finset Copy)
    (s : State V E Copy) : Prop where
  live_subset : s.live ⊆ keep
  genealogy : ∀ l ∈ s.live, ∃ t, (s.genealogy l).prune keep = some t ∧
    graftInput input t = s.genealogy l

theorem actual_initial_reconstruction (s : State V E Copy) (hs : Valid s) :
    Reconstructs s.genealogy s.live s := by
  refine ⟨Finset.Subset.refl _,?_⟩
  intro l hl
  exact ⟨.leaf l,initial_live_root_prune s hs hl,rfl⟩

omit [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype Copy] in
theorem actual_merger_reconstruction (input : Copy → Genealogy Copy) (keep : Finset Copy)
    (s : State V E Copy) (hs : Reconstructs input keep s) {a b : Copy}
    (hm : LegalMerge s a b) : Reconstructs input keep (merge s a b) := by
  refine ⟨fun l hl => hs.live_subset (Finset.mem_erase.mp hl).2,?_⟩
  intro l hl
  by_cases ha : l = a
  · subst l
    obtain ⟨ta,hta,hga⟩ := hs.genealogy a hm.first_live
    obtain ⟨tb,htb,hgb⟩ := hs.genealogy b hm.second_live
    refine ⟨.graft ta tb,?_,?_⟩
    · simp only [merge,ite_true,Genealogy.prune,hta,htb,Genealogy.joinPruned]
    · simp only [merge,ite_true,graftInput,hga,hgb]
  · simpa only [merge,if_neg ha] using hs.genealogy l (Finset.mem_erase.mp hl).2

omit [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype Copy] in
theorem actual_transport_reconstruction (input : Copy → Genealogy Copy) (keep : Finset Copy)
    (s : State V E Copy) (hs : Reconstructs input keep s)
    (whereTo : Copy → Location V E) (event : SourceEvent V E Copy) :
    Reconstructs input keep (transport s whereTo event) := ⟨hs.live_subset,hs.genealogy⟩

theorem actual_encode_reconstruction (N : RootedBinary V E X) {sample : Copy → X}
    (input : Copy → Genealogy Copy) (keep : Finset Copy) (s : State V E Copy)
    (hs : SourceValid N sample s) (hr : Reconstructs input keep s) :
    Reconstructs input keep (state (admittedCode N sample s hs)) := by
  refine ⟨hr.live_subset,?_⟩
  intro l hl
  rw [show (state (admittedCode N sample s hs)).genealogy l = s.genealogy l from
    decode_encode_live_genealogy N.root s hs.forest hl]
  exact hr.genealogy l hl

theorem actual_step_reconstruction (N : RootedBinary V E X) {sample : Copy → X}
    (input : Copy → Genealogy Copy) (keep : Finset Copy) (s : Code N sample)
    (hs : Reconstructs input keep (state s)) (p : Option (Choice N s)) :
    Reconstructs input keep (state (stepDestination N s p)) := by
  cases p with
  | none => exact hs
  | some p =>
      have hm := population_pair_is_source_legal (state s) (originalPlace N p.1)
        (originalPlace_not_node N p.1) p.2.property
      exact actual_encode_reconstruction N input keep _
        (merge_source_valid N sample _ s.property hm)
        (actual_merger_reconstruction input keep _ hs hm)

lemma actual_step_reconstruction_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (input : Copy → Genealogy Copy) (keep : Finset Copy) (s : Code N sample)
    (hs : Reconstructs input keep (state s)) {d : Code N sample}
    (hd : d ∈ (sourceStep N r s).support) : Reconstructs input keep (state d) := by
  obtain ⟨p,_,hp⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
  rw [← hp]
  exact actual_step_reconstruction N input keep s hs p

lemma actual_iteration_reconstruction_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (input : Copy → Genealogy Copy) (keep : Finset Copy)
    (n : Nat) (s : Code N sample) (hs : Reconstructs input keep (state s)) {d : Code N sample}
    (hd : d ∈ (sourceIteration N r n s).support) : Reconstructs input keep (state d) := by
  induction n generalizing s with
  | zero =>
      have he : d = s := by simpa only [sourceIteration,PMF.mem_support_pure_iff] using hd
      exact he ▸ hs
  | succ n ih =>
      obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact ih z (actual_step_reconstruction_support N r input keep s hs hz) hdz

lemma actual_time_reconstruction_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (input : Copy → Genealogy Copy) (keep : Finset Copy)
    (t : ℝ≥0) (s : Code N sample) (hs : Reconstructs input keep (state s)) {d : Code N sample}
    (hd : d ∈ (sourceTimeKernel N r t s).support) : Reconstructs input keep (state d) := by
  obtain ⟨n,_,hdn⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact actual_iteration_reconstruction_support N r input keep n s hs hdn

lemma actual_boundary_reconstruction_support (N : RootedBinary V E X) {sample : Copy → X}
    (input : Copy → Genealogy Copy) (keep : Finset Copy)
    (op : BoundaryOperation N) (s : Code N sample) (hs : Reconstructs input keep (state s))
    {d : Code N sample} (hd : d ∈ (boundaryKernel N op s).support) :
    Reconstructs input keep (state d) := by
  cases op with
  | exit e =>
      have he : d = exitCode N s e := by simpa only [boundaryKernel,PMF.mem_support_pure_iff] using hd
      subst d
      exact actual_encode_reconstruction N input keep _
        (exitEdge_source_valid N sample _ s.property e) ⟨hs.live_subset,hs.genealogy⟩
  | ordinary e degree =>
      have he : d = ordinaryCode N s e := by simpa only [boundaryKernel,PMF.mem_support_pure_iff] using hd
      subst d
      exact actual_encode_reconstruction N input keep _
        (enterEdge_source_valid N sample _ s.property e) ⟨hs.live_subset,hs.genealogy⟩
  | root =>
      have he : d = rootCode N s := by simpa only [boundaryKernel,PMF.mem_support_pure_iff] using hd
      subst d
      exact actual_encode_reconstruction N input keep _ (enterRoot_source_valid N sample _ s.property)
        ⟨hs.live_subset,hs.genealogy⟩
  | common H =>
      have he : d = pulseCode H s (fun _ => (state s).register H.hybrid) := by
        simpa only [boundaryKernel,PMF.mem_support_pure_iff] using hd
      subst d
      exact actual_encode_reconstruction N input keep _ (pulse_source_valid H sample _ s.property _)
        ⟨hs.live_subset,hs.genealogy⟩
  | independent H gamma =>
      obtain ⟨coin,_,hc⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
      rw [← hc]
      exact actual_encode_reconstruction N input keep _ (pulse_source_valid H sample _ s.property coin)
        ⟨hs.live_subset,hs.genealogy⟩

lemma actual_program_reconstruction_from (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (input : Copy → Genealogy Copy) (keep : Finset Copy)
    (ops : List (ProgramStep N)) (s : Code N sample) (hs : Reconstructs input keep (state s))
    {d : Code N sample} (hd : d ∈ (sourceProgram N r ops s).support) :
    Reconstructs input keep (state d) := by
  induction ops generalizing s with
  | nil =>
      have he : d = s := by simpa only [sourceProgram,PMF.mem_support_pure_iff] using hd
      exact he ▸ hs
  | cons op ops ih =>
      obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      apply ih z _ hdz
      cases op with
      | interval t => exact actual_time_reconstruction_support N r input keep t s hs hz
      | boundary b => exact actual_boundary_reconstruction_support N input keep b s hs hz

theorem actual_program_reconstruction_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r ops s).support) :
    Reconstructs (state s).genealogy (state s).live (state d) :=
  actual_program_reconstruction_from N r (state s).genealogy (state s).live ops s
    (actual_initial_reconstruction (state s) s.property.forest) hd

omit [DecidableEq E] in
/-- Every later ORIGINAL whole tree is obtained by grafting the original
entering opaque subtrees into the selected CURRENT-root tree. -/
theorem actual_whole_forest_reconstruction (N : RootedBinary V E X) {sample : Copy → X}
    (input : Copy → Genealogy Copy) (keep : Finset Copy) (s : Code N sample)
    (hr : Reconstructs input keep (state s)) :
    rootForest N s = (sourceUnrankedForest (state s) keep).image (graftUnranked input) := by
  ext q
  constructor
  · intro hq
    obtain ⟨l,hl,hlq⟩ := Finset.mem_image.mp hq
    obtain ⟨t,ht,hgt⟩ := hr.genealogy l hl
    refine Finset.mem_image.mpr ⟨toUnranked t,?_,?_⟩
    · apply (mem_sourceUnrankedForest (state s) keep _).mpr
      refine ⟨l,hr.live_subset hl,t,?_,rfl⟩
      have hrep : (state s).ancestor l = l := s.property.forest.representative l hl
      rw [hrep]
      exact ht
    · rw [graftUnranked_toUnranked,hgt]
      exact hlq
  · intro hq
    obtain ⟨q0,hq0,hq⟩ := Finset.mem_image.mp hq
    obtain ⟨x,hx,t,ht,htq⟩ := (mem_sourceUnrankedForest (state s) keep q0).mp hq0
    have hl := s.property.forest.ancestor_live x
    obtain ⟨t0,ht0,hgt0⟩ := hr.genealogy ((state s).ancestor x) hl
    have htt : t0 = t := Option.some.inj (ht0.symm.trans ht)
    subst t0
    refine Finset.mem_image.mpr ⟨(state s).ancestor x,hl,?_⟩
    rw [← hgt0,← graftUnranked_toUnranked,htq]
    exact hq

noncomputable def originalCurrentRootKernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    PMF (Finset (UnrankedTree Copy)) :=
  (sourceProgram N r ops s).map (fun d => sourceUnrankedForest (state d) (state s).live)

/-- Exact factorization of the EXISTING full original-descendant source law.
This is not inferred solely from the new opaque wrapper's definition. -/
theorem actual_original_whole_forest_kernel_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    (sourceProgram N r ops s).map (rootForest N) =
      (originalCurrentRootKernel N r ops s).map
        (fun F => F.image (graftUnranked (state s).genealogy)) := by
  rw [originalCurrentRootKernel,PMF.map_comp]
  apply map_eq_of_eq_on_support
  intro d hd
  exact actual_whole_forest_reconstruction N (state s).genealogy (state s).live d
    (actual_program_reconstruction_support N r ops s hd)

theorem actual_original_current_root_cap (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample)
    (m : Nat) (cap : (state s).live.card ≤ m) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r ops s).support) : (rootForest N d).card ≤ m := by
  have hr := actual_program_reconstruction_support N r ops s hd
  exact Finset.card_image_le.trans ((Finset.card_le_card hr.live_subset).trans cap)

omit [DecidableEq E] [Fintype Copy] in
/-- A current root retains the original taxon/graph identity of its owner;
its other carried descendants are not separately routed tokens. -/
lemma current_root_descendant (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (place : Location V E)
    (hplace : ∀ l ∈ (state s).live, (state s).location l = place)
    (l : SelectedCopy (state s).live) :
    DescendsTo N place (selectedSample sample (state s).live l) := by
  have h := s.property.original_descendant l.val
  change DescendsTo N ((state s).location ((state s).ancestor l.val)) (sample l.val) at h
  have hr : (state s).ancestor l.val = l.val := s.property.forest.representative l.val l.property
  rw [hr,hplace l.val l.property] at h
  exact h

noncomputable def actualCurrentRootCode (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (place : Location V E)
    (hplace : ∀ l ∈ (state s).live, (state s).location l = place) :
    Code N (selectedSample sample (state s).live) :=
  enteringCode N (selectedSample sample (state s).live) place (state s).register
    (current_root_descendant N s place hplace)

lemma currentRootCode_ancestor (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (place : Location V E)
    (hplace : ∀ l ∈ (state s).live, (state s).location l = place)
    (l : SelectedCopy (state s).live) :
    (state (actualCurrentRootCode N s place hplace)).ancestor l = l := rfl

lemma currentRootCode_location (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (place : Location V E)
    (hplace : ∀ l ∈ (state s).live, (state s).location l = place)
    (l : SelectedCopy (state s).live) :
    (state (actualCurrentRootCode N s place hplace)).location l = place := by
  exact decode_encode_live_population N.root _ (enteringState_valid place (state s).register)
    (Finset.mem_univ l)

/-- The independently constructed smaller source is initialized on the actual
CURRENT entering roots and agrees with the original state's root-panel view.
This view identity is proved from actual source validity and graft pruning. -/
theorem actual_current_root_initialization (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (place : Location V E)
    (hplace : ∀ l ∈ (state s).live, (state s).location l = place) :
    selectedView (state s) (state s).live =
      liftView (state s).live (selectedView (state (actualCurrentRootCode N s place hplace)) Finset.univ) := by
  apply SelectedView.ext
  · funext x
    by_cases hx : x ∈ (state s).live
    · let l : SelectedCopy (state s).live := ⟨x,hx⟩
      have hh := lifted_original_genealogy (state s).live
        (state (actualCurrentRootCode N s place hplace)) l
      change selectedGenealogy (state s) (state s).live x = _
      rw [hh]
      have hr : (state s).ancestor x = x := s.property.forest.representative x hx
      rw [selectedGenealogy,if_pos hx,hr,initial_live_root_prune (state s) s.property.forest hx,
        currentRootCode_ancestor]
      simp only [actualCurrentRootCode,enteringCode_genealogy,mapLabels]
      rfl
    · simp only [selectedView,selectedGenealogy,if_neg hx,liftView,dif_neg hx]
  · funext x
    by_cases hx : x ∈ (state s).live
    · let l : SelectedCopy (state s).live := ⟨x,hx⟩
      have hh := lifted_original_population (state s).live
        (state (actualCurrentRootCode N s place hplace)) l
      change selectedLocation (state s) (state s).live x = _
      rw [hh]
      have hr : (state s).ancestor x = x := s.property.forest.representative x hx
      simp only [selectedLocation,if_pos hx,copyLocation,hr,hplace x hx,
        currentRootCode_ancestor,currentRootCode_location]
    · simp only [selectedView,selectedLocation,if_neg hx,liftView,dif_neg hx]
  · rfl

/-- Actual K on the smaller CURRENT-root carrier, with original graph,
rates, operation program, root history interface and SAME original register. -/
noncomputable def smallerCurrentRootKernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample)
    (place : Location V E) (hplace : ∀ l ∈ (state s).live, (state s).location l = place) :
    PMF (Finset (UnrankedTree (SelectedCopy (state s).live))) :=
  (sourceProgram N r ops (actualCurrentRootCode N s place hplace)).map
    (fun d => sourceUnrankedForest (state d) Finset.univ)

theorem actual_original_to_current_root_kernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample)
    (place : Location V E) (hplace : ∀ l ∈ (state s).live, (state s).location l = place) :
    originalCurrentRootKernel N r ops s =
      (smallerCurrentRootKernel N r ops s place hplace).map
        (fun F => F.image (mapUnranked Subtype.val)) := by
  have h := congrArg (fun law : PMF (JoinedIndex N sample (state s).live) =>
      law.map (fun v => unrankedForest v.val))
    (actual_cross_carrier_program_law N r (state s).live ops s
      (actualCurrentRootCode N s place hplace) (actual_current_root_initialization N s place hplace))
  rw [PMF.map_comp,PMF.map_comp] at h
  change (sourceProgram N r ops s).map
      (fun d => unrankedForest (selectedView (state d) (state s).live)) =
    (sourceProgram N r ops (actualCurrentRootCode N s place hplace)).map
      (fun d => unrankedForest (liftView (state s).live (selectedView (state d) Finset.univ))) at h
  simp_rw [actual_small_unranked_label_lift] at h
  rw [originalCurrentRootKernel,smallerCurrentRootKernel,PMF.map_comp]
  exact h

lemma graftInput_mapLabels {A B C : Type*} (f : A → B) (input : B → Genealogy C)
    (t : Genealogy A) :
    graftInput input (mapLabels f t) = graftInput (fun a => input (f a)) t := by
  induction t with
  | leaf l => rfl
  | graft a b ih1 ih2 => simp only [mapLabels,graftInput,ih1,ih2]

lemma graftUnranked_mapUnranked {A B C : Type*}
    [DecidableEq A] [DecidableEq B] [DecidableEq C]
    (f : A → B) (input : B → Genealogy C) (q : UnrankedTree A) :
    graftUnranked input (mapUnranked f q) = graftUnranked (fun a => input (f a)) q := by
  induction q using Quotient.inductionOn with
  | h t =>
      change toUnranked (graftInput input (mapLabels f t)) =
        toUnranked (graftInput (fun a => input (f a)) t)
      rw [graftInput_mapLabels]

/-- The actual K has only the CURRENT entering-root carrier. Its law, grafted
with every complete initial subtree, equals the existing original source's
complete rooted unranked forest law. Original sampled-descendant count is
unrestricted. Actual rates/program/graph/register are the SAME throughout. -/
theorem actual_current_roots_complete_graft_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample)
    (place : Location V E) (hplace : ∀ l ∈ (state s).live, (state s).location l = place) :
    (sourceProgram N r ops s).map (rootForest N) =
      (smallerCurrentRootKernel N r ops s place hplace).map
        (fun F => F.image (graftUnranked (fun l => (state s).genealogy l.val))) := by
  rw [actual_original_whole_forest_kernel_law,
    actual_original_to_current_root_kernel N r ops s place hplace,
    PMF.map_comp]
  congr 1
  funext F
  change (F.image (mapUnranked Subtype.val)).image (graftUnranked (state s).genealogy) = _
  rw [Finset.image_image]
  apply Finset.image_congr
  intro q _
  exact graftUnranked_mapUnranked Subtype.val (state s).genealogy q

/-- Source-derived G1 replacement at an arbitrary already-formed original
entering state, with the exterior's SAME exposed original register and any
retained root/history information. Survivor IDs and plane orientation are
erased at the actual unranked interface, never exposed to the exterior.
No source output-law equality or target kernel is a premise. -/
theorem actual_original_contextual_forest_replacement
    (N : RootedBinary V E X) {sample : Copy → X} {History Obs : Type*}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample)
    (place : Location V E) (hplace : ∀ l ∈ (state s).live, (state s).location l = place)
    (history : History)
    (exterior : History × (V → Bool) × Finset (UnrankedTree Copy) → PMF Obs) :
    (sourceProgram N r ops s).bind
      (fun d => exterior (history,(state d).register,rootForest N d)) =
    (smallerCurrentRootKernel N r ops s place hplace).bind
      (fun F => exterior (history,(state s).register,
        F.image (graftUnranked (fun l => (state s).genealogy l.val)))) := by
  have hreg : (sourceProgram N r ops s).map
      (fun d => (history,(state d).register,rootForest N d)) =
      ((sourceProgram N r ops s).map (rootForest N)).map
        (fun F => (history,(state s).register,F)) := by
    rw [PMF.map_comp]
    apply map_eq_of_eq_on_support
    intro d hd
    rw [actual_program_register_support N r ops s hd]
    rfl
  change (sourceProgram N r ops s).bind
    (exterior ∘ fun d => (history,(state d).register,rootForest N d)) = _
  rw [← PMF.bind_map,hreg,actual_current_roots_complete_graft_law N r ops s place hplace,
    PMF.map_comp,PMF.bind_map]
  rfl

abbrev EnteringAtPlace (N : RootedBinary V E X) (sample : Copy → X) (place : Location V E) :=
  {s : Code N sample // ∀ l ∈ (state s).live, (state s).location l = place}

/-- The input forest/register/history can have any joint causal distribution.
Conditioning is on the whole actual entering case. The replacement integrates
that SAME case, instead of reinitializing a shared random register or history. -/
theorem actual_original_joint_context_replacement
    (N : RootedBinary V E X) (sample : Copy → X) {History Obs : Type*}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (place : Location V E)
    (prior : PMF (EnteringAtPlace N sample place × History))
    (exterior : History × (V → Bool) × Finset (UnrankedTree Copy) → PMF Obs) :
    prior.bind (fun c => (sourceProgram N r ops c.1.val).bind
      (fun d => exterior (c.2,(state d).register,rootForest N d))) =
    prior.bind (fun c => (smallerCurrentRootKernel N r ops c.1.val place c.1.property).bind
      (fun F => exterior (c.2,(state c.1.val).register,
        F.image (graftUnranked (fun l => (state c.1.val).genealogy l.val))))) := by
  congr 1
  funext c
  exact actual_original_contextual_forest_replacement N r ops c.1.val place c.1.property c.2 exterior

omit [DecidableEq E] [Fintype Copy] in
/-- The source kernel carrier has cardinality EXACTLY the number of CURRENT
entering roots, even if their descendant trees contain arbitrarily many labels. -/
theorem actual_kernel_carrier_cap (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (m : Nat) (hcap : (state s).live.card ≤ m) :
    Fintype.card (SelectedCopy (state s).live) ≤ m := by
  simpa only [Fintype.card_coe] using hcap

end G1OriginalCurrentRootReconstruction
