import G5AllAgeObservedSupport
import G5SynchronizedObservableChronology

/-!
# Observed M3 support drives the original safe sure-block chronology
Contributor: dot / OpenAI, 10 October 2026.
UNCOMPILED CANDIDATE. The old attained-age argument is reused with an actual
arbitrary-weight observation/support provider. A third original taxon in a
fresh observed triple supplies a pair support reader when only two retained
representatives remain. The positive finite-history argument proves support
invariance; it does not identify the triple-conditioned weights with ordinary
pair weights, and no conditioned posterior is carried into a later stage.
-/
namespace GProgram.G5.ObservedSureBlockChronology
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
open scoped Classical NNReal
variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

/-- The five-state reader retains exactly the first pair's coincidence bit,
for any population carrier rather than only an ancestor index carrier. -/
lemma partition_pair01_eq {A : Type*} [DecidableEq A] (a : Fin 3 → A) :
    a 0 = a 1 ↔ ancestorPartition a = 1 ∨ ancestorPartition a = 4 := by
  unfold ancestorPartition
  split_ifs <;> simp_all [eq_comm]

lemma partition_pair01_ne {A : Type*} [DecidableEq A] (a : Fin 3 → A) :
    a 0 ≠ a 1 ↔ ¬(ancestorPartition a = 1 ∨ ancestorPartition a = 4) :=
  not_congr (partition_pair01_eq a)

lemma universal_predicate_of_support_iff {A B T : Type*} (f : A → T) (g : B → T)
    (h : ∀ t, (∃ a, f a = t) ↔ ∃ b, g b = t) (P : T → Prop) :
    (∀ a, P (f a)) ↔ ∀ b, P (g b) := by
  constructor
  · intro ha b
    obtain ⟨a,he⟩ := (h (g b)).mpr ⟨b,rfl⟩
    simpa only [he] using ha a
  · intro hb a
    obtain ⟨b,he⟩ := (h (f a)).mp ⟨a,rfl⟩
    simpa only [he] using hb b

/-- Every desired safe pair choice extends through one original register to
a positive no-merger history of the full fresh triple. Its third taxon need
not be retained or safe together with that pair. Only support is claimed. -/
theorem actual_triple_safe_pair_relation
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (B : Finset X) (tip : Fin 3 ↪ X) (h0 : tip 0 ∈ B) (h1 : tip 1 ∈ B)
    (a0 t : ℝ) (htips : ∀ x, C.age (N.leaf x) = a0)
    (pre post : List ℝ) (guard next : ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post)
    (hleft : guard ≤ t) (hright : t < next) (hroot : t < C.age N.root)
    (hsafe : SafeAt N C B t)
    (D : ∀ i, NativeCurrentDescription N C H (tip i) t)
    (R : Option E → Option E → Prop) :
    let past := cutPast N C H p common pre guard t
    (∀ s : ActualSeed N (originalTripleCodePosterior N tip p r past),
      R (codePopulation N s.val 0) (codePopulation N s.val 1)) ↔
      ∀ b c : Bool, R (some (descriptionPositions N C hcut H (D 0) b))
        (some (descriptionPositions N C hcut H (D 1) c)) := by
  dsimp only
  let past := cutPast N C H p common pre guard t
  constructor
  · intro hall b c
    let pairTip : Bool ↪ X := ⟨fun a => tip (if a then 1 else 0),by
      intro a b hab
      have he : (if a then (1 : Fin 3) else 0) = (if b then 1 else 0) := tip.injective hab
      cases a <;> cases b <;> simp_all⟩
    let pairD : ∀ a : Bool, NativeCurrentDescription N C H (pairTip a) t :=
      fun a => D (if a then 1 else 0)
    let choice : Bool → Fin 2 := fun a => bitChoice (if a then c else b)
    have hpairs : ∀ a : Bool, pairTip a ∈ B := by intro a; cases a <;> assumption
    obtain ⟨coin,hcoin⟩ := safe_common_register_realizes_group_choices N C hcut H B pairTip hpairs hsafe pairD choice
    have hcoin0 : descriptionRead N C hcut H (D 0) coin = descriptionPositions N C hcut H (D 0) b := by
      simpa [pairD,pairTip,choice,binaryPositions_choiceBit,choiceBit_bitChoice] using hcoin false
    have hcoin1 : descriptionRead N C hcut H (D 1) coin = descriptionPositions N C hcut H (D 1) c := by
      simpa [pairD,pairTip,choice,binaryPositions_choiceBit,choiceBit_bitChoice] using hcoin true
    let d := fixedRegisterPrefix N past (initialCode N tip (originalRegister N coin))
    have hs := actual_cut_word_strict N C H p common pre post guard next (Real.toNNReal (t-guard)) hsplit
    have hroute : d ∈ (originalRouteLaw N tip p past).support :=
      (actual_original_route_support_iff_seeds N tip p past hs d).mpr ⟨coin,fixedRegisterPrefix_legal N past _⟩
    obtain ⟨hd,hstart⟩ := (actual_original_singleton_iff_route N tip p r past d).mpr hroute
    have hpost : d ∈ (originalTripleCodePosterior N tip p r past).support :=
      (PMF.mem_support_filter_iff (actual_full_code_event_witness N tip p r Finset.univ past)).mpr ⟨hstart,hd⟩
    have hloc : ∀ i : Fin 3, copyLocation (state d) i =
        .edge (descriptionRead N C hcut H (D i) coin) :=
      actual_fixed_cut_description_read N C tip hcut H p common r a0 t htips
        pre post guard next hsplit hleft hright hroot D coin
    have h := hall ⟨d,hpost⟩
    simpa only [codePopulation,hloc 0,hloc 1,hcoin0,hcoin1] using h
  · intro hbits s
    have hdsource := ((PMF.mem_support_filter_iff
      (actual_full_code_event_witness N tip p r Finset.univ past)).mp s.property).2
    obtain ⟨reg,_,hdr⟩ := (PMF.mem_support_bind_iff _ _ _).mp hdsource
    have hactive := actual_cut_supported_locations_active N C tip reg H p common r a0 t htips
      pre post guard next hsplit hleft hright hroot s.val hdr
    obtain ⟨e0,he0,ha0⟩ := hactive 0
    obtain ⟨e1,he1,ha1⟩ := hactive 1
    obtain ⟨k0,hk0⟩ := actual_active_location_is_description_position N C hcut H tip t D s.val 0 e0 he0 ha0
    obtain ⟨k1,hk1⟩ := actual_active_location_is_description_position N C hcut H tip t D s.val 1 e1 he1 ha1
    rw [binaryPositions_choiceBit] at hk0 hk1
    simpa only [codePopulation,he0,he1,hk0,hk1] using hbits (choiceBit k0) (choiceBit k1)

/-- Same-root and cross-root ages use one uniform support contract. Native
sure-pair predicates refer to ALL original route families, including the
ancestral population; the actual posterior may have arbitrarily correlated
weights. The prefix and readout are constructed, not supplied by a caller. -/
theorem actual_safe_pair_readout_exists
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (B : Finset X) (tip : Fin 3 ↪ X) (h0 : tip 0 ∈ B) (h1 : tip 1 ∈ B)
    (a0 t : ℝ) (htips : ∀ x, C.age (N.leaf x) = a0) (ht : a0 ≤ t)
    (hsafe : SafeAt N C B t) :
    ∃ (past : List (ProgramStep N)) (epsilon : ℝ),
      ActualCutReadout N C tip H p common r t past epsilon ∧
      ((∀ R : RouteFamily N, SharesPopulation N R C t (tip 0) (tip 1)) ↔
        ∀ s : ActualSeed N (originalTripleCodePosterior N tip p r past),
          codePopulation N s.val 0 = codePopulation N s.val 1) ∧
      ((∀ R : RouteFamily N, ¬SharesPopulation N R C t (tip 0) (tip 1)) ↔
        ∀ s : ActualSeed N (originalTripleCodePosterior N tip p r past),
          codePopulation N s.val 0 ≠ codePopulation N s.val 1) := by
  by_cases hroot : t < C.age N.root
  · obtain ⟨pre,guard,next,post,hsplit,hleft,hright⟩ := original_older_gap_exists N C t
      (by simpa only [first_date_of_contemporaneous_tips N C a0 htips] using ht) hroot
    let D : ∀ i : Fin 3, NativeCurrentDescription N C H (tip i) t := fun i =>
      Classical.choice (original_current_description_exists N C H (tip i)
        (by simpa only [htips] using ht) hroot)
    let past := cutPast N C H p common pre guard t
    refine ⟨past,next-t,⟨sub_pos.mpr hright,
      actual_cut_posterior_placement N C tip H p common r a0 t htips pre post guard next hsplit hleft hright hroot,
      actual_cut_joint_observed N C tip H p common r pre post guard next t hsplit hleft hright⟩,?_,?_⟩
    · simp_rw [sharesPopulation_iff_coOccupy_below_root N C _ hroot]
      exact (all_routes_sure_together_iff_all_position_bits N C hcut H
        (tip.injective.ne (by decide : (0 : Fin 3) ≠ 1)) (D 0) (D 1)).trans (by
          simpa only [Option.some.injEq] using (actual_triple_safe_pair_relation N C hcut H p common r
            B tip h0 h1 a0 t htips pre post guard next hsplit hleft hright hroot hsafe D (· = ·)).symm)
    · simp_rw [sharesPopulation_iff_coOccupy_below_root N C _ hroot]
      exact (all_routes_sure_separate_iff_all_position_bits N C hcut H
        (tip.injective.ne (by decide : (0 : Fin 3) ≠ 1)) (D 0) (D 1)).trans (by
          simpa only [ne_eq,Option.some.injEq] using (actual_triple_safe_pair_relation N C hcut H p common r
            B tip h0 h1 a0 t htips pre post guard next hsplit hleft hright hroot hsafe D (· ≠ ·)).symm)
  · have hrt := le_of_not_gt hroot
    let past := rootPast N C H p common t
    have hloc (s : ActualSeed N (originalTripleCodePosterior N tip p r past)) (i : Fin 3) :
        codePopulation N s.val i = none := by
      have h := actual_root_posterior_support N C tip H p common r t s i
      simp only [codePopulation,h]
    have hgeo : ∀ R : RouteFamily N, SharesPopulation N R C t (tip 0) (tip 1) :=
      fun _ => ⟨none,hrt,hrt⟩
    have hactual : ∀ s : ActualSeed N (originalTripleCodePosterior N tip p r past),
        codePopulation N s.val 0 = codePopulation N s.val 1 := fun s => (hloc s 0).trans (hloc s 1).symm
    refine ⟨past,1,actual_root_cut_readout N C tip H p common r t hrt,
      iff_of_true hgeo hactual,?_⟩
    apply iff_of_false
    · intro h
      obtain ⟨R⟩ := routeFamily_exists N
      exact h R (hgeo R)
    · intro h
      obtain ⟨d,hd⟩ := (originalTripleCodePosterior N tip p r past).support_nonempty
      exact h ⟨d,hd⟩ (hactual ⟨d,hd⟩)


/-- Extend two distinct original taxa to one genuine three-taxon panel. The
third taxon may have been deleted from the retained representative set. -/
lemma original_triple_containing_pair (hX : 3 ≤ Fintype.card X) (x y : X) (hne : x ≠ y) :
    ∃ tip : Fin 3 ↪ X, tip 0 = x ∧ tip 1 = y := by
  classical
  have hz : ∃ z : X, z ≠ x ∧ z ≠ y := by
    by_contra hn
    have hsub : (Finset.univ : Finset X) ⊆ {x,y} := by
      intro z _
      by_contra hz
      have hz' : z ≠ x ∧ z ≠ y := by simpa only [Finset.mem_insert,Finset.mem_singleton,not_or] using hz
      exact hn ⟨z,hz'⟩
    have hc := Finset.card_le_card hsub
    have htwo : ({x,y} : Finset X).card = 2 := by simp [hne]
    rw [Finset.card_univ,htwo] at hc
    omega
  obtain ⟨z,hzx,hzy⟩ := hz
  refine ⟨⟨![x,y,z],?_⟩,rfl,rfl⟩
  intro i j he
  fin_cases i <;> fin_cases j <;> simp_all

section TwoSources
variable {V₂ E₂ : Type*} [DecidableEq V₂] [DecidableEq E₂] [Fintype V₂] [Fintype E₂]

/-- No equal hidden posterior, root age or deletion schedule is assumed.
One genuine ordinary triple containing the retained pair determines both
universal pair predicates at the actual common cut age. -/
theorem equal_observed_triple_laws_safe_pair_support
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (p₂ : HybridProbabilities N₂) (common₂ : Hybrid N₂ → Bool) (r₂ : PositivePairRates E₂)
    (B : Finset X) (tip : Fin 3 ↪ X) (h0 : tip 0 ∈ B) (h1 : tip 1 ∈ B)
    (a0 t : ℝ) (htips : ∀ x, C.age (N.leaf x) = a0) (htips₂ : ∀ x, C₂.age (N₂.leaf x) = a0)
    (ht : a0 ≤ t) (hsafe : SafeAt N C B t) (hsafe₂ : SafeAt N₂ C₂ B t)
    (heq : naturalObservedFullLaw N C tip H p common r = naturalObservedFullLaw N₂ C₂ tip H₂ p₂ common₂ r₂) :
    ((∀ R : RouteFamily N, SharesPopulation N R C t (tip 0) (tip 1)) ↔
      ∀ R : RouteFamily N₂, SharesPopulation N₂ R C₂ t (tip 0) (tip 1)) ∧
    ((∀ R : RouteFamily N, ¬SharesPopulation N R C t (tip 0) (tip 1)) ↔
      ∀ R : RouteFamily N₂, ¬SharesPopulation N₂ R C₂ t (tip 0) (tip 1)) := by
  obtain ⟨past,epsilon,hread,hpair⟩ := actual_safe_pair_readout_exists N C hcut H p common r B tip h0 h1 a0 t htips ht hsafe
  obtain ⟨past₂,epsilon₂,hread₂,hpair₂⟩ := actual_safe_pair_readout_exists N₂ C₂ hcut₂ H₂ p₂ common₂ r₂ B tip h0 h1 a0 t htips₂ ht hsafe₂
  have hs := cut_readouts_identify_occupancy N C tip H p common r N₂ C₂ tip H₂ p₂ common₂ r₂
    t past past₂ epsilon epsilon₂ hread hread₂ heq
  have he : (∀ s : ActualSeed N (originalTripleCodePosterior N tip p r past),
      codePopulation N s.val 0 = codePopulation N s.val 1) ↔
      ∀ s : ActualSeed N₂ (originalTripleCodePosterior N₂ tip p₂ r₂ past₂),
        codePopulation N₂ s.val 0 = codePopulation N₂ s.val 1 := by
    simpa only [←partition_pair01_eq] using universal_predicate_of_support_iff
      (fun s : ActualSeed N (originalTripleCodePosterior N tip p r past) => ancestorPartition (codePopulation N s.val))
      (fun s : ActualSeed N₂ (originalTripleCodePosterior N₂ tip p₂ r₂ past₂) => ancestorPartition (codePopulation N₂ s.val))
      hs (fun gene => gene = 1 ∨ gene = 4)
  have hn : (∀ s : ActualSeed N (originalTripleCodePosterior N tip p r past),
      codePopulation N s.val 0 ≠ codePopulation N s.val 1) ↔
      ∀ s : ActualSeed N₂ (originalTripleCodePosterior N₂ tip p₂ r₂ past₂),
        codePopulation N₂ s.val 0 ≠ codePopulation N₂ s.val 1 := by
    simpa only [←partition_pair01_ne] using universal_predicate_of_support_iff
      (fun s : ActualSeed N (originalTripleCodePosterior N tip p r past) => ancestorPartition (codePopulation N s.val))
      (fun s : ActualSeed N₂ (originalTripleCodePosterior N₂ tip p₂ r₂ past₂) => ancestorPartition (codePopulation N₂ s.val))
      hs (fun gene => ¬(gene = 1 ∨ gene = 4))
  exact ⟨hpair.1.trans (he.trans hpair₂.1.symm),hpair.2.trans (hn.trans hpair₂.2.symm)⟩

/-- Both rivals' full sure-block predicates are identified at every age at
which their retained originals are safe. The observation hypothesis is the
unchanged family of ordinary original triples, not a fitted block oracle. -/
theorem equal_m3_laws_safe_sure_block_equivalence
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (p₂ : HybridProbabilities N₂) (common₂ : Hybrid N₂ → Bool) (r₂ : PositivePairRates E₂)
    (hX : 3 ≤ Fintype.card X) (B D : Finset X) (hDB : D ⊆ B) (hD : D.Nonempty)
    (a0 t : ℝ) (htips : ∀ x, C.age (N.leaf x) = a0) (htips₂ : ∀ x, C₂.age (N₂.leaf x) = a0)
    (ht : a0 ≤ t) (hsafe : SafeAt N C B t) (hsafe₂ : SafeAt N₂ C₂ B t)
    (heq : ∀ tip : Fin 3 ↪ X,
      naturalObservedFullLaw N C tip H p common r = naturalObservedFullLaw N₂ C₂ tip H₂ p₂ common₂ r₂) :
    SureBlock N C B D t ↔ SureBlock N₂ C₂ B D t := by
  have hp (x y : X) (hx : x ∈ B) (hy : y ∈ B) (hne : x ≠ y) :
      ((∀ R : RouteFamily N, SharesPopulation N R C t x y) ↔
        ∀ R : RouteFamily N₂, SharesPopulation N₂ R C₂ t x y) ∧
      ((∀ R : RouteFamily N, ¬SharesPopulation N R C t x y) ↔
        ∀ R : RouteFamily N₂, ¬SharesPopulation N₂ R C₂ t x y) := by
    obtain ⟨tip,h0,h1⟩ := original_triple_containing_pair hX x y hne
    have h := equal_observed_triple_laws_safe_pair_support N C hcut H p common r
      N₂ C₂ hcut₂ H₂ p₂ common₂ r₂ B tip (h0.symm ▸ hx) (h1.symm ▸ hy)
      a0 t htips htips₂ ht hsafe hsafe₂ (heq tip)
    simpa only [h0,h1] using h
  rw [sureBlock_iff_full_pair_predicates N C B D hDB hD (fun x _ => by rw [htips]; exact ht),
    sureBlock_iff_full_pair_predicates N₂ C₂ B D hDB hD (fun x _ => by rw [htips₂]; exact ht)]
  constructor <;> intro h <;> constructor
  · intro R x hx y hy hne
    exact ((hp x y (hDB hx) (hDB hy) hne).1.mp (fun R => h.1 R x hx y hy hne)) R
  · intro R x hx y hyB hyD
    have hne : x ≠ y := fun he => hyD (he ▸ hx)
    exact ((hp x y (hDB hx) hyB hne).2.mp (fun R => h.2 R x hx y hyB hyD)) R
  · intro R x hx y hy hne
    exact ((hp x y (hDB hx) (hDB hy) hne).1.mpr (fun R => h.1 R x hx y hy hne)) R
  · intro R x hx y hyB hyD
    have hne : x ≠ y := fun he => hyD (he ▸ hx)
    exact ((hp x y (hDB hx) hyB hne).2.mpr (fun R => h.2 R x hx y hyB hyD)) R

/-- Reuse of the existing first-attained-age proof. Safety at the comparison
age is derived separately from each original source's no-earlier-block
geometry; compatible deletion schedules are not an input premise. -/
theorem equal_m3_laws_first_attained_age
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (p₂ : HybridProbabilities N₂) (common₂ : Hybrid N₂ → Bool) (r₂ : PositivePairRates E₂)
    (hX : 3 ≤ Fintype.card X) (B : Finset X) (a0 s : ℝ)
    (htips : ∀ x, C.age (N.leaf x) = a0) (htips₂ : ∀ x, C₂.age (N₂.leaf x) = a0)
    (hstartAge : a0 ≤ s) (hs : s ≤ C.age N.root) (hs₂ : s ≤ C₂.age N₂.root) (hc : 2 ≤ B.card)
    (hstart : SafeAt N C B s) (hstart₂ : SafeAt N₂ C₂ B s)
    (heq : ∀ tip : Fin 3 ↪ X,
      naturalObservedFullLaw N C tip H p common r = naturalObservedFullLaw N₂ C₂ tip H₂ p₂ common₂ r₂) :
    firstGroupingAge N C B hs hc = firstGroupingAge N₂ C₂ B hs₂ hc := by
  let tau := firstGroupingAge N C B hs hc
  let sigma := firstGroupingAge N₂ C₂ B hs₂ hc
  have htau := firstGroupingAge_attained N C B hs hc
  have hsigma := firstGroupingAge_attained N₂ C₂ B hs₂ hc
  apply le_antisymm
  · by_contra hn
    have hst : sigma < tau := lt_of_not_ge hn
    obtain ⟨D,hDB,hD,hblock⟩ := hsigma.2.2.2
    have hsafe := safeAt_before_or_at_firstGroupingAge N C hcut B hs hc hstart hst.le
    have hsafe₂ := safeAt_firstGroupingAge N₂ C₂ hcut₂ B hs₂ hc hstart₂
    have he := equal_m3_laws_safe_sure_block_equivalence N C hcut H p common r
      N₂ C₂ hcut₂ H₂ p₂ common₂ r₂ hX B D hDB (Finset.card_pos.mp (by omega))
      a0 sigma htips htips₂ (hstartAge.trans hsigma.2.1) hsafe hsafe₂ heq
    exact no_sure_block_before_firstGroupingAge N C B hs hc hsigma.2.1 hst hDB hD (he.mpr hblock)
  · by_contra hn
    have hts : tau < sigma := lt_of_not_ge hn
    obtain ⟨D,hDB,hD,hblock⟩ := htau.2.2.2
    have hsafe := safeAt_firstGroupingAge N C hcut B hs hc hstart
    have hsafe₂ := safeAt_before_or_at_firstGroupingAge N₂ C₂ hcut₂ B hs₂ hc hstart₂ hts.le
    have he := equal_m3_laws_safe_sure_block_equivalence N C hcut H p common r
      N₂ C₂ hcut₂ H₂ p₂ common₂ r₂ hX B D hDB (Finset.card_pos.mp (by omega))
      a0 tau htips htips₂ (hstartAge.trans htau.2.1) hsafe hsafe₂ heq
    exact no_sure_block_before_firstGroupingAge N₂ C₂ B hs₂ hc htau.2.1 hts hDB hD (he.mp hblock)

/-- All simultaneous sure blocks agree at the proved shared attained age. -/
theorem equal_m3_laws_simultaneous_blocks
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (p₂ : HybridProbabilities N₂) (common₂ : Hybrid N₂ → Bool) (r₂ : PositivePairRates E₂)
    (hX : 3 ≤ Fintype.card X) (B : Finset X) (a0 s : ℝ)
    (htips : ∀ x, C.age (N.leaf x) = a0) (htips₂ : ∀ x, C₂.age (N₂.leaf x) = a0)
    (hstartAge : a0 ≤ s) (hs : s ≤ C.age N.root) (hs₂ : s ≤ C₂.age N₂.root) (hc : 2 ≤ B.card)
    (hstart : SafeAt N C B s) (hstart₂ : SafeAt N₂ C₂ B s)
    (heq : ∀ tip : Fin 3 ↪ X,
      naturalObservedFullLaw N C tip H p common r = naturalObservedFullLaw N₂ C₂ tip H₂ p₂ common₂ r₂) :
    let tau := firstGroupingAge N C B hs hc
    firstGroupingAge N₂ C₂ B hs₂ hc = tau ∧
      simultaneousBlocks N C B tau = simultaneousBlocks N₂ C₂ B tau := by
  dsimp only
  have he := equal_m3_laws_first_attained_age N C hcut H p common r N₂ C₂ hcut₂ H₂ p₂ common₂ r₂
    hX B a0 s htips htips₂ hstartAge hs hs₂ hc hstart hstart₂ heq
  refine ⟨he.symm,?_⟩
  have hsafe := safeAt_firstGroupingAge N C hcut B hs hc hstart
  have hsafe₂ := safeAt_firstGroupingAge N₂ C₂ hcut₂ B hs₂ hc hstart₂
  rw [←he] at hsafe₂
  have htime := (firstGroupingAge_attained N C B hs hc).2.1
  ext D
  rw [mem_simultaneousBlocks,mem_simultaneousBlocks]
  constructor <;> rintro ⟨hDB,hD,hblock⟩ <;> refine ⟨hDB,hD,?_⟩
  · exact (equal_m3_laws_safe_sure_block_equivalence N C hcut H p common r
      N₂ C₂ hcut₂ H₂ p₂ common₂ r₂ hX B D hDB (Finset.card_pos.mp (by omega)) a0 _ htips htips₂
      (hstartAge.trans htime) hsafe hsafe₂ heq).mp hblock
  · exact (equal_m3_laws_safe_sure_block_equivalence N C hcut H p common r
      N₂ C₂ hcut₂ H₂ p₂ common₂ r₂ hX B D hDB (Finset.card_pos.mp (by omega)) a0 _ htips htips₂
      (hstartAge.trans htime) hsafe hsafe₂ heq).mpr hblock


theorem equal_m3_laws_simultaneous_deletion [LinearOrder X]
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (p₂ : HybridProbabilities N₂) (common₂ : Hybrid N₂ → Bool) (r₂ : PositivePairRates E₂)
    (hX : 3 ≤ Fintype.card X) (B : Finset X) (a0 s : ℝ)
    (htips : ∀ x, C.age (N.leaf x) = a0) (htips₂ : ∀ x, C₂.age (N₂.leaf x) = a0)
    (hstartAge : a0 ≤ s) (hs : s ≤ C.age N.root) (hs₂ : s ≤ C₂.age N₂.root) (hc : 2 ≤ B.card)
    (hstart : SafeAt N C B s) (hstart₂ : SafeAt N₂ C₂ B s)
    (heq : ∀ tip : Fin 3 ↪ X,
      naturalObservedFullLaw N C tip H p common r = naturalObservedFullLaw N₂ C₂ tip H₂ p₂ common₂ r₂) :
    firstGroupingAge N C B hs hc = firstGroupingAge N₂ C₂ B hs₂ hc ∧
    simultaneousBlocks N C B (firstGroupingAge N C B hs hc) =
      simultaneousBlocks N₂ C₂ B (firstGroupingAge N₂ C₂ B hs₂ hc) ∧
    survivors N C B (firstGroupingAge N C B hs hc) =
      survivors N₂ C₂ B (firstGroupingAge N₂ C₂ B hs₂ hc) := by
  obtain ⟨ha,hblocks⟩ := equal_m3_laws_simultaneous_blocks N C hcut H p common r
    N₂ C₂ hcut₂ H₂ p₂ common₂ r₂ hX B a0 s htips htips₂ hstartAge hs hs₂ hc hstart hstart₂ heq
  have hblocks' : simultaneousBlocks N C B (firstGroupingAge N C B hs hc) =
      simultaneousBlocks N₂ C₂ B (firstGroupingAge N₂ C₂ B hs₂ hc) := by rw [ha]; exact hblocks
  refine ⟨ha.symm,hblocks',?_⟩
  unfold survivors
  apply Finset.filter_congr
  intro x _
  constructor <;> intro h D hD hxD
  · have hDN : D ∈ simultaneousBlocks N C B (firstGroupingAge N C B hs hc) := by rwa [hblocks']
    exact h D hDN hxD
  · have hDN₂ : D ∈ simultaneousBlocks N₂ C₂ B (firstGroupingAge N₂ C₂ B hs₂ hc) := by rwa [←hblocks']
    exact h D hDN₂ hxD

/-- The existing cardinal-decreasing trace transfers stage by stage using
fresh original M3 laws from the same bank. No posterior is reused at a stage. -/
theorem deletionTrace_of_equal_m3_laws [LinearOrder X]
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (p₂ : HybridProbabilities N₂) (common₂ : Hybrid N₂ → Bool) (r₂ : PositivePairRates E₂)
    (hX : 3 ≤ Fintype.card X) (a0 : ℝ)
    (htips : ∀ x, C.age (N.leaf x) = a0) (htips₂ : ∀ x, C₂.age (N₂.leaf x) = a0)
    {B F : Finset X} {s u : ℝ} {n : Nat} (trace : DeletionTrace N C B s F u n)
    (hstartAge : a0 ≤ s) (hs₂ : s ≤ C₂.age N₂.root)
    (hstart : SafeAt N C B s) (hstart₂ : SafeAt N₂ C₂ B s)
    (heq : ∀ tip : Fin 3 ↪ X,
      naturalObservedFullLaw N C tip H p common r = naturalObservedFullLaw N₂ C₂ tip H₂ p₂ common₂ r₂) :
    DeletionTrace N₂ C₂ B s F u n := by
  induction trace with
  | terminal B s hB => exact DeletionTrace.terminal B s hB
  | @step B s hs hc F u n rest ih =>
    have hsame := equal_m3_laws_simultaneous_deletion N C hcut H p common r
      N₂ C₂ hcut₂ H₂ p₂ common₂ r₂ hX B a0 s htips htips₂ hstartAge hs hs₂ hc hstart hstart₂ heq
    let tau := firstGroupingAge N C B hs hc
    have htau := (firstGroupingAge_attained N C B hs hc).2.1
    have htaur₂ : tau ≤ C₂.age N₂.root := by
      dsimp [tau]
      rw [hsame.1]
      exact (firstGroupingAge_attained N₂ C₂ B hs₂ hc).2.2.1
    have hsa := safeAt_firstGroupingAge N C hcut B hs hc hstart
    have hsa₂ := safeAt_firstGroupingAge N₂ C₂ hcut₂ B hs₂ hc hstart₂
    rw [←hsame.1] at hsa₂
    have hsB := survivors_subset N C B tau
    have hrest := ih (hstartAge.trans htau) htaur₂
      (safeAt_subset N C hsB hsa) (safeAt_subset N₂ C₂ hsB hsa₂)
    apply DeletionTrace.step B s hs₂ hc
    rwa [hsame.2.2,hsame.1] at hrest

/-- From only the admitted ordinary M3 observation family, construct one
shared finite deletion chronology on ALL original taxa. Safe starts, shared
attained ages, simultaneous blocks and identical surviving originals are
derived. This is a chronology endpoint, not yet the final cluster/split union. -/
theorem m3_identifies_original_shared_chronology [LinearOrder X]
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (N₂ : RootedBinary V₂ E₂ X) (C₂ : Calendar N₂.graph)
    (hcut₂ : ∀ e, N₂.graph.IsHybrid (N₂.graph.source e) → N₂.graph.IsBridge e)
    (H₂ : OriginalParentRegistry N₂) (p₂ : HybridProbabilities N₂) (common₂ : Hybrid N₂ → Bool) (r₂ : PositivePairRates E₂)
    (hX : 3 ≤ Fintype.card X) (a0 : ℝ)
    (htips : ∀ x, C.age (N.leaf x) = a0) (htips₂ : ∀ x, C₂.age (N₂.leaf x) = a0)
    (heq : ∀ tip : Fin 3 ↪ X,
      naturalObservedFullLaw N C tip H p common r = naturalObservedFullLaw N₂ C₂ tip H₂ p₂ common₂ r₂) :
    ∃ F u n, DeletionTrace N C Finset.univ a0 F u n ∧
      DeletionTrace N₂ C₂ Finset.univ a0 F u n ∧ F.card = 1 ∧
      a0 ≤ u ∧ SafeAt N C F u ∧ n ≤ Fintype.card X - 1 := by
  have hA : (Finset.univ : Finset X).Nonempty := by
    apply Finset.card_pos.mp
    rw [Finset.card_univ]
    omega
  obtain ⟨F,u,n,htrace,hF,_,hau,_,hFs,hbound⟩ := contemporaneous_original_tip_chronology
    N C hcut Finset.univ hA (fun x _ => htips x)
  have hs₂ : a0 ≤ C₂.age N₂.root := by
    obtain ⟨x,_⟩ := hA
    rw [←htips₂ x]
    exact C₂.age_le_of_directed (N₂.rooted (N₂.leaf x))
  have htrace₂ := deletionTrace_of_equal_m3_laws N C hcut H p common r
    N₂ C₂ hcut₂ H₂ p₂ common₂ r₂ hX a0 htips htips₂ htrace le_rfl hs₂
    (safeAt_sampling_age N C Finset.univ a0 (fun x _ => htips x))
    (safeAt_sampling_age N₂ C₂ Finset.univ a0 (fun x _ => htips₂ x)) heq
  exact ⟨F,u,n,htrace,htrace₂,hF,hau,hFs,by simpa only [Finset.card_univ] using hbound⟩
end TwoSources

#print axioms actual_triple_safe_pair_relation
#print axioms actual_safe_pair_readout_exists
#print axioms equal_observed_triple_laws_safe_pair_support
#print axioms equal_m3_laws_safe_sure_block_equivalence
#print axioms equal_m3_laws_first_attained_age
#print axioms equal_m3_laws_simultaneous_blocks
#print axioms deletionTrace_of_equal_m3_laws
#print axioms m3_identifies_original_shared_chronology
end GProgram.G5.ObservedSureBlockChronology
