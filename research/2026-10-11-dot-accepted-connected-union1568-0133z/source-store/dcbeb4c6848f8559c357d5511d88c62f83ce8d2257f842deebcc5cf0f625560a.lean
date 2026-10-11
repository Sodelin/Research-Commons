import G5ObservedSureBlockChronology
import G5BoundedExactBlock

/-!
# Actual safe exact-block support, with one original COMMON register
Contributor: dot / OpenAI, 10 October 2026.
UNCOMPILED CANDIDATE. This connects the accepted bounded-domain obstruction to
actual original route populations. Cartesian feasibility concerns support only;
it does not assert independence of a conditioned posterior. A fresh observed
triple may contain extra original taxa outside the safe retained set.
-/
namespace GProgram.G5.SafeExactBlockSupport
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5 GProgram.G5.SafePast
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.NativeCurrentPortCompiler
open UnifiedLean.Source.NativeCommonPairGerm
open GProgram.G5.OriginalProgramSurvival GProgram.G5.OriginalSelectedPosterior
open GProgram.G5.EnumeratedPosteriorGerm GProgram.G5.ActualActivatedPrefix
open GProgram.G5.OriginalEpochChart GProgram.G5.OlderSideCutChart
open GProgram.G5.TriplePartitionReadout GProgram.G5.ObservedSafeTripleSupport
open GProgram.G5.SafePrefixRouteBridge GProgram.G5.AllAgeObservedSupport
open GProgram.G5.ActualRoutingSupport GProgram.G5.StrictBoundaryRoutes
open GProgram.G5.RootCutChart GProgram.G5.HiddenRegisterTimedProjectivity
open GProgram.G5.AttainedChronology GProgram.G5.OriginalCoinLaw
open GProgram.G5.ObservedSureBlockChronology GProgram.G5.BoundedSupport
open scoped Classical NNReal
variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

/-- The actual unique population occupied by an original tip in a COMMON
switching at the requested age. The existence proof is geometric, not a new
source field. Above the root this is the original ancestral population. -/
noncomputable def currentPopulation (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (t : ℝ) (hl : ∀ x, C.age (N.leaf x) ≤ t)
    (a : CommonSeed N) (x : X) : Option E :=
  Classical.choose (occupies_exists N C (commonRoutes N C H a) x (hl x))

lemma currentPopulation_occupies (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (t : ℝ) (hl : ∀ x, C.age (N.leaf x) ≤ t)
    (a : CommonSeed N) (x : X) :
    Occupies N (commonRoutes N C H a) C t x (currentPopulation N C H t hl a x) :=
  Classical.choose_spec (occupies_exists N C (commonRoutes N C H a) x (hl x))

lemma occupies_iff_currentPopulation (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (t : ℝ) (hl : ∀ x, C.age (N.leaf x) ≤ t)
    (a : CommonSeed N) (x : X) (pop : Option E) :
    Occupies N (commonRoutes N C H a) C t x pop ↔ currentPopulation N C H t hl a x = pop := by
  constructor
  · exact fun hp => occupies_unique N C _ (currentPopulation_occupies N C H t hl a x) hp
  · intro h; rw [←h]; exact currentPopulation_occupies N C H t hl a x

lemma currentPopulation_of_description (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (t : ℝ) (hl : ∀ x, C.age (N.leaf x) ≤ t)
    (a : CommonSeed N) (x : X) (D : NativeCurrentDescription N C H x t) :
    currentPopulation N C H t hl a x = some (descriptionRead N C hcut H D a) := by
  apply (occupies_iff_currentPopulation N C H t hl a x _).mp
  exact description_read_native_source_spec N C hcut H D (fun _ => a)

lemma currentPopulation_at_root (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (t : ℝ) (hl : ∀ x, C.age (N.leaf x) ≤ t)
    (ht : C.age N.root ≤ t) (a : CommonSeed N) (x : X) :
    currentPopulation N C H t hl a x = none :=
  (occupies_iff_currentPopulation N C H t hl a x none).mp ht

noncomputable def currentDomain (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (t : ℝ) (hl : ∀ x, C.age (N.leaf x) ≤ t) (x : X) : Finset (Option E) :=
  Finset.univ.image (fun a : CommonSeed N => currentPopulation N C H t hl a x)

lemma mem_currentDomain (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (t : ℝ) (hl : ∀ x, C.age (N.leaf x) ≤ t) (x : X) (pop : Option E) :
    pop ∈ currentDomain N C H t hl x ↔ ∃ a : CommonSeed N, currentPopulation N C H t hl a x = pop := by
  simp only [currentDomain,Finset.mem_image,Finset.mem_univ,true_and]

lemma currentDomain_card_le_two (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (t : ℝ) (hl : ∀ x, C.age (N.leaf x) ≤ t) (x : X) :
    (currentDomain N C H t hl x).card ≤ 2 := by
  by_cases ht : t < C.age N.root
  · obtain ⟨D⟩ := original_current_description_exists N C H x (hl x) ht
    have hsub : currentDomain N C H t hl x ⊆
        Finset.univ.image (fun b : Bool => some (descriptionPositions N C hcut H D b)) := by
      intro pop hp
      obtain ⟨a,rfl⟩ := (mem_currentDomain N C H t hl x pop).mp hp
      rw [currentPopulation_of_description N C hcut H t hl a x D]
      unfold descriptionRead
      split <;> apply Finset.mem_image.mpr
      · exact ⟨false,Finset.mem_univ _,rfl⟩
      · exact ⟨_,Finset.mem_univ _,rfl⟩
    exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (by simp))
  · have hsub : currentDomain N C H t hl x ⊆ {none} := by
      intro pop hp
      obtain ⟨a,rfl⟩ := (mem_currentDomain N C H t hl x pop).mp hp
      simp only [currentPopulation_at_root N C H t hl (le_of_not_gt ht),Finset.mem_singleton]
    exact (Finset.card_le_card hsub).trans (by simp)

/-- Arbitrary feasible positions of all safe retained ORIGINAL tips are
simultaneously realized by ONE original COMMON register. -/
theorem safe_current_domains_cartesian (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (B : Finset X) (t : ℝ)
    (hl : ∀ x, C.age (N.leaf x) ≤ t) (hsafe : SafeAt N C B t)
    (f : X → Option E) (hf : ∀ x ∈ B, f x ∈ currentDomain N C H t hl x) :
    ∃ a : CommonSeed N, ∀ x ∈ B, currentPopulation N C H t hl a x = f x := by
  by_cases ht : t < C.age N.root
  · let tip : B ↪ X := ⟨Subtype.val,Subtype.val_injective⟩
    let D : ∀ x : B, NativeCurrentDescription N C H x.val t :=
      fun x => Classical.choice (original_current_description_exists N C H x.val (hl x.val) ht)
    have hbits (x : B) : ∃ k : Fin 2,
        some (binaryPositions (descriptionPositions N C hcut H (D x)) k) = f x.val := by
      obtain ⟨a,ha⟩ := (mem_currentDomain N C H t hl x.val _).mp (hf x.val x.property)
      rw [currentPopulation_of_description N C hcut H t hl a x.val (D x)] at ha
      obtain ⟨choice,hchoice⟩ := common_group_reads_are_coupled_choices N C hcut H tip D a
      exact ⟨choice x,by simpa only [hchoice x] using ha⟩
    choose k hk using hbits
    obtain ⟨a,ha⟩ := safe_common_register_realizes_group_choices N C hcut H B tip
      (fun x => x.property) hsafe D k
    refine ⟨a,?_⟩
    intro x hx
    rw [currentPopulation_of_description N C hcut H t hl a x (D ⟨x,hx⟩),ha ⟨x,hx⟩]
    exact hk ⟨x,hx⟩
  · refine ⟨fun _ => false,?_⟩
    intro x hx
    obtain ⟨a,ha⟩ := (mem_currentDomain N C H t hl x _).mp (hf x hx)
    rw [currentPopulation_at_root N C H t hl (le_of_not_gt ht)] at ha ⊢
    exact ha

/-- A possible exact block in an actual consistent COMMON switching. -/
def PossibleBlock (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (B D : Finset X) (t : ℝ) : Prop :=
  ∃ (a : CommonSeed N) (pop : Option E), populationBlock N (commonRoutes N C H a) B C t pop = D

/-- The accepted abstract ExactBlock premise is discharged from source geometry,
including simultaneous feasibility in one register. -/
theorem possible_block_iff_cartesian (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (B D : Finset X) (t : ℝ)
    (hl : ∀ x, C.age (N.leaf x) ≤ t) (hsafe : SafeAt N C B t) (hDB : D ⊆ B) :
    PossibleBlock N C H B D t ↔ ExactBlock (currentDomain N C H t hl) B D := by
  constructor
  · rintro ⟨a,pop,hblock⟩
    refine ⟨pop,?_⟩
    intro x hx
    have hmem : x ∈ D ↔ currentPopulation N C H t hl a x = pop := by
      rw [←hblock]
      simp only [populationBlock,Finset.mem_filter,hx,true_and,occupies_iff_currentPopulation N C H t hl]
    constructor
    · intro hxD; exact (mem_currentDomain N C H t hl x pop).mpr ⟨a,hmem.mp hxD⟩
    · intro hxD
      exact ⟨currentPopulation N C H t hl a x,(mem_currentDomain N C H t hl x _).mpr ⟨a,rfl⟩,
        fun he => hxD (hmem.mpr he)⟩
  · rintro ⟨pop,hpop⟩
    have hchoose (x : X) : ∃ y : Option E, x ∈ B →
        y ∈ currentDomain N C H t hl x ∧ (y = pop ↔ x ∈ D) := by
      by_cases hx : x ∈ B
      · by_cases hxD : x ∈ D
        · exact ⟨pop,fun _ => ⟨(hpop x hx).1 hxD,iff_of_true rfl hxD⟩⟩
        · obtain ⟨y,hy,hne⟩ := (hpop x hx).2 hxD
          exact ⟨y,fun _ => ⟨hy,iff_of_false hne hxD⟩⟩
      · exact ⟨none,fun hh => False.elim (hx hh)⟩
    choose f hf using hchoose
    obtain ⟨a,ha⟩ := safe_current_domains_cartesian N C hcut H B t hl hsafe f
      (fun x hx => (hf x hx).1)
    refine ⟨a,pop,?_⟩
    ext x
    simp only [populationBlock,Finset.mem_filter,occupies_iff_currentPopulation N C H t hl]
    constructor
    · rintro ⟨hx,he⟩; exact (hf x hx).2.mp ((ha x hx).symm.trans he)
    · intro hx; exact ⟨hDB hx,(ha x (hDB hx)).trans ((hf x (hDB hx)).2.mpr hx)⟩

/-- Same partition code means the same equality relation, on every selected
subpanel. This does not expose original edge or latent register labels. -/
lemma ancestorPartition_eq_rel {A A' : Type*} [DecidableEq A] [DecidableEq A']
    (a : Fin 3 → A) (b : Fin 3 → A') (h : ancestorPartition a = ancestorPartition b) :
    ∀ i j, (a i = a j ↔ b i = b j) := by
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp only [ancestorPartition] at h <;> split_ifs at h <;> simp_all [eq_comm]
  all_goals
    exact iff_of_false (fun he => ‹a 0 ≠ a 1› he.symm)
      (fun he => ‹b 0 ≠ b 1› he.symm)

/-- Every at-most-three original-label set embeds in a genuine fresh observed
triple, even when it contains fewer than three surviving representatives. -/
lemma triple_covering_small_set (hX : 3 ≤ Fintype.card X) (U : Finset X) (hU : U.card ≤ 3) :
    ∃ tip : Fin 3 ↪ X, ∀ x ∈ U, ∃ i, tip i = x := by
  obtain ⟨T,hUT,_,hT⟩ := Finset.exists_subsuperset_card_eq (Finset.subset_univ U) hU
    (show 3 ≤ (Finset.univ : Finset X).card by simpa using hX)
  let e : T ≃ Fin 3 := T.equivFinOfCardEq hT
  let tip : Fin 3 ↪ X := ⟨fun i => (e.symm i).val,by
    intro i j he
    exact e.symm.injective (Subtype.ext he)⟩
  refine ⟨tip,?_⟩
  intro x hx
  refine ⟨e ⟨x,hUT hx⟩,?_⟩
  simp [tip]

/-- An actual cut readout whose selected safe coordinates have exactly the
COMMON support. Extra triple coordinates are unrestricted original taxa.
Both directions retain the original common register, not stage-wise coins. -/
theorem actual_selected_safe_readout
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (B : Finset X) (tip : Fin 3 ↪ X) (a0 t : ℝ)
    (htips : ∀ x, C.age (N.leaf x) = a0) (ht : a0 ≤ t) (hsafe : SafeAt N C B t) :
    let hl : ∀ x, C.age (N.leaf x) ≤ t := fun x => (htips x).le.trans ht
    ∃ (past : List (ProgramStep N)) (epsilon : ℝ),
      ActualCutReadout N C tip H p common r t past epsilon ∧
      (∀ a : CommonSeed N, ∃ s : ActualSeed N (originalTripleCodePosterior N tip p r past),
        ∀ i, tip i ∈ B → codePopulation N s.val i = currentPopulation N C H t hl a (tip i)) ∧
      (∀ s : ActualSeed N (originalTripleCodePosterior N tip p r past), ∃ a : CommonSeed N,
        ∀ i, tip i ∈ B → codePopulation N s.val i = currentPopulation N C H t hl a (tip i)) := by
  dsimp only
  let hl : ∀ x, C.age (N.leaf x) ≤ t := fun x => (htips x).le.trans ht
  by_cases hroot : t < C.age N.root
  · obtain ⟨pre,guard,next,post,hsplit,hleft,hright⟩ := original_older_gap_exists N C t
      (by simpa only [first_date_of_contemporaneous_tips N C a0 htips] using ht) hroot
    let D : ∀ i : Fin 3, NativeCurrentDescription N C H (tip i) t :=
      fun i => Classical.choice (original_current_description_exists N C H (tip i) (hl (tip i)) hroot)
    let past := cutPast N C H p common pre guard t
    refine ⟨past,next-t,⟨sub_pos.mpr hright,
      actual_cut_posterior_placement N C tip H p common r a0 t htips pre post guard next hsplit hleft hright hroot,
      actual_cut_joint_observed N C tip H p common r pre post guard next t hsplit hleft hright⟩,?_,?_⟩
    · intro a
      let d := fixedRegisterPrefix N past (initialCode N tip (originalRegister N a))
      have hs := actual_cut_word_strict N C H p common pre post guard next (Real.toNNReal (t-guard)) hsplit
      have hroute : d ∈ (originalRouteLaw N tip p past).support :=
        (actual_original_route_support_iff_seeds N tip p past hs d).mpr ⟨a,fixedRegisterPrefix_legal N past _⟩
      obtain ⟨hd,hstart⟩ := (actual_original_singleton_iff_route N tip p r past d).mpr hroute
      have hpost : d ∈ (originalTripleCodePosterior N tip p r past).support :=
        (PMF.mem_support_filter_iff (actual_full_code_event_witness N tip p r Finset.univ past)).mpr ⟨hstart,hd⟩
      refine ⟨⟨d,hpost⟩,?_⟩
      intro i _
      have hh : copyLocation (state d) i = .edge (descriptionRead N C hcut H (D i) a) :=
        actual_fixed_cut_description_read N C tip hcut H p common r a0 t htips
          pre post guard next hsplit hleft hright hroot D a i
      simpa only [codePopulation,hh,currentPopulation_of_description N C hcut H t hl a (tip i) (D i)]
    · intro s
      have hdsource := ((PMF.mem_support_filter_iff
        (actual_full_code_event_witness N tip p r Finset.univ past)).mp s.property).2
      obtain ⟨reg,_,hdr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hdsource
      have hactive := actual_cut_supported_locations_active N C tip reg H p common r a0 t htips
        pre post guard next hsplit hleft hright hroot s.val hdr
      have hk (i : Fin 3) : ∃ k : Fin 2,
          codePopulation N s.val i = some (binaryPositions (descriptionPositions N C hcut H (D i)) k) := by
        obtain ⟨e,he,ha⟩ := hactive i
        obtain ⟨k,hk⟩ := actual_active_location_is_description_position N C hcut H tip t D s.val i e he ha
        exact ⟨k,by simpa only [codePopulation,he,hk]⟩
      choose k hk using hk
      let G := {i : Fin 3 // tip i ∈ B}
      let selected : G ↪ X := ⟨fun i => tip i.val,by
        intro i j he; exact Subtype.ext (tip.injective he)⟩
      let Ds : ∀ i : G, NativeCurrentDescription N C H (selected i) t := fun i => D i.val
      obtain ⟨a,ha⟩ := safe_common_register_realizes_group_choices N C hcut H B selected
        (fun i => i.property) hsafe Ds (fun i => k i.val)
      refine ⟨a,?_⟩
      intro i hi
      rw [hk i,currentPopulation_of_description N C hcut H t hl a (tip i) (D i)]
      exact congrArg some (ha ⟨i,hi⟩).symm
  · have hrt := le_of_not_gt hroot
    let past := rootPast N C H p common t
    have hloc (s : ActualSeed N (originalTripleCodePosterior N tip p r past)) (i : Fin 3) :
        codePopulation N s.val i = none := by
      simp only [codePopulation,actual_root_posterior_support N C tip H p common r t s i]
    refine ⟨past,1,actual_root_cut_readout N C tip H p common r t hrt,?_,?_⟩
    · intro a
      obtain ⟨d,hd⟩ := (originalTripleCodePosterior N tip p r past).support_nonempty
      exact ⟨⟨d,hd⟩,fun i _ => (hloc ⟨d,hd⟩ i).trans
        (currentPopulation_at_root N C H t hl hrt a (tip i)).symm⟩
    · intro s
      exact ⟨fun _ => false,fun i _ => (hloc s i).trans
        (currentPopulation_at_root N C H t hl hrt (fun _ => false) (tip i)).symm⟩

#print axioms safe_current_domains_cartesian
#print axioms possible_block_iff_cartesian
#print axioms actual_selected_safe_readout
end GProgram.G5.SafeExactBlockSupport
