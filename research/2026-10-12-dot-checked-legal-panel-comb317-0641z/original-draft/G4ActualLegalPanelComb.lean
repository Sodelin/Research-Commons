import G4ActualPositiveGridUniqueness
import UnifiedLean.Source.SourceUnrankedAllPanels
import G2LiteralTimedObservationPruning

/-!
# One specified comb as a legal full-panel original-source event

Contributor: dot (OpenAI), 12 October 2026. UNCOMPILED draft.
Formal composition of the inherited D2/Oct8 legal observation argument.
The actual selected subtype, original graph/calendar/parameters and one COMMON
bank are retained. No arbitrary Code relabelling law is assumed.
-/
namespace DotG4.ActualLegalPanelComb
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.SourceCompletedUnrankedTree UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.SourceCopyCarrierTransport UnifiedLean.Source.SourceUnrankedCopyProjectivity
open UnifiedLean.Source.SourceUnrankedAllPanels
open GProgram.G5.SafePrefixRouteBridge GProgram.G5.SourcePairPersistence
open GProgram.G4.ActualCommonSelectorSupport GProgram.G2.LiteralTimedObservationPruning
open G1UnrankedActualFuture
open DotG34.SpecifiedCombEvent DotG34.SpecifiedCombSelectedObservation
open DotG4.ActualBankFirstMeeting DotG4.ActualFirstMeetingEntrance
open DotG4.ActualColocatedCompletion DotG4.ActualFirstMeetingCombMass
open DotG4.ActualFirstMeetingExposureScaling DotG4.ActualNaturalCombMoments
open DotG4.ActualObservableBankCertificate
open scoped Classical NNReal ENNReal BigOperators
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma selected_common_prefix (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (q : Nat) :
    CommonOnlyWord N ((compiledCalendarProgram N C H gamma (fun _ => true)).take q) := by
  have h := actual_common_compiled_word_only N C H gamma
  rw [show compiledCalendarProgram N C H gamma (fun _ => true) =
    (compiledCalendarProgram N C H gamma (fun _ => true)).take q ++
      (compiledCalendarProgram N C H gamma (fun _ => true)).drop q from
      (List.take_append_drop q _).symm] at h
  exact ((commonOnlyWord_append N _ _).mp h).1

lemma enumerated_cut_colocated (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (r : PositivePairRates E) (coin : Hybrid N → Bool) (i j : X)
    (sample : Copy → X) (b : Copy) (hb : sample b = j)
    (ha : ∀ x, x ≠ b → sample x = i)
    {s : Code N sample}
    (hs : s ∈ (sourceProgram N r
      ((compiledCalendarProgram N C H gamma (fun _ => true)).take
        (bankFirstMeetingIndex N C H gamma r coin i j))
      (initialCode N sample (originalRegister N coin))).support) : SharedLocation N s := by
  let P := compiledCalendarProgram N C H gamma (fun _ => true)
  let m := bankFirstMeetingIndex N C H gamma r coin i j
  have hl := actual_common_program_copy_locations N r (P.take m)
    (selected_common_prefix N C H gamma m) (initialCode N sample (originalRegister N coin)) hs
  have hm := (bankFirstMeeting_spec N C H gamma r coin i j).2
  refine ⟨copyLocation (state (pairReference N C H gamma coin i j m)) true,?_⟩
  intro x
  rw [hl x]
  by_cases hxb : x = b
  · subst x
    have he := initial_reference_location_cross_carrier N sample (pairSample i j)
      (originalRegister N coin) (P.take m) b false (by simpa [pairSample] using hb)
    exact he.trans hm.symm
  · exact initial_reference_location_cross_carrier N sample (pairSample i j)
      (originalRegister N coin) (P.take m) x true (by simpa [pairSample] using ha x hxb)

lemma enumerated_before_cut_B_isolated (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (r : PositivePairRates E) (coin : Hybrid N → Bool) (i j : X)
    (sample : Copy → X) (b : Copy) (hb : sample b = j)
    (ha : ∀ x, x ≠ b → sample x = i) (q : Nat)
    (hq : q < bankFirstMeetingIndex N C H gamma r coin i j)
    {s : Code N sample}
    (hs : s ∈ (sourceProgram N r
      ((compiledCalendarProgram N C H gamma (fun _ => true)).take q)
      (initialCode N sample (originalRegister N coin))).support) :
    ∀ x, (state s).ancestor x = (state s).ancestor b → x = b := by
  let P := compiledCalendarProgram N C H gamma (fun _ => true)
  have hl := actual_common_program_copy_locations N r (P.take q)
    (selected_common_prefix N C H gamma q) (initialCode N sample (originalRegister N coin)) hs
  intro x hx
  by_contra hxb
  have he : copyLocation (state s) x = copyLocation (state s) b := congrArg (state s).location hx
  rw [hl x,hl b] at he
  have hxa := initial_reference_location_cross_carrier N sample (pairSample i j)
    (originalRegister N coin) (P.take q) x true (by simpa [pairSample] using ha x hxb)
  have hbb := initial_reference_location_cross_carrier N sample (pairSample i j)
    (originalRegister N coin) (P.take q) b false (by simpa [pairSample] using hb)
  exact before_bankFirstMeeting_separated N C H gamma r coin i j q hq
    (hxa.symm.trans (he.trans hbb))

lemma enumerated_cut_B_isolated (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (r : PositivePairRates E) (coin : Hybrid N → Bool) (i j : X)
    (sample : Copy → X) (b : Copy) (hb : sample b = j)
    (ha : ∀ x, x ≠ b → sample x = i)
    {s : Code N sample}
    (hs : s ∈ (sourceProgram N r
      ((compiledCalendarProgram N C H gamma (fun _ => true)).take
        (bankFirstMeetingIndex N C H gamma r coin i j))
      (initialCode N sample (originalRegister N coin))).support) :
    ∀ x, (state s).ancestor x = (state s).ancestor b → x = b := by
  let P := compiledCalendarProgram N C H gamma (fun _ => true)
  generalize hm : bankFirstMeetingIndex N C H gamma r coin i j = m at hs
  cases m with
  | zero =>
    have he : s = initialCode N sample (originalRegister N coin) := by
      simpa only [List.take_zero,sourceProgram,PMF.mem_support_pure_iff] using hs
    subst s
    exact fun x hx => hx
  | succ q =>
    have hbound := (bankFirstMeeting_spec N C H gamma r coin i j).1
    have hq : q < P.length := by dsimp [P]; omega
    have htake := List.take_succ_eq_append_getElem hq
    cases hop : P[q] with
    | interval t =>
      have he := (bankFirstMeeting_spec N C H gamma r coin i j).2
      have href : pairReference N C H gamma coin i j (q+1) =
          pairReference N C H gamma coin i j q := by
        unfold pairReference
        rw [htake,hop,fixedRegisterPrefix_append]
        rfl
      rw [hm,href] at he
      exact False.elim (before_bankFirstMeeting_separated N C H gamma r coin i j q (by omega) he)
    | boundary op =>
      rw [htake,hop,sourceProgram_append] at hs
      obtain ⟨z,hz,hsz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
      have hboundary : s ∈ (boundaryKernel N op z).support := by
        simpa only [sourceProgram,sourceProgramStep,PMF.bind_pure] using hsz
      intro x hx
      rw [boundary_ancestor_eq N op z s hboundary] at hx
      exact enumerated_before_cut_B_isolated N C H gamma r coin i j sample b hb ha q
        (by omega) hz x hx

lemma enumerated_cut_comb_row [Nonempty Copy] (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (r : PositivePairRates E) (coin : Hybrid N → Bool) (i j : X)
    (sample : Copy → X) (b : Copy) (hb : sample b = j)
    (ha : ∀ x, x ≠ b → sample x = i) (as : List Copy)
    (hcover : ∀ x, x = b ∨ x ∈ as) (hnodup : as.Nodup) (hnot : b ∉ as) (hne : as ≠ [])
    {s : Code N sample}
    (hs : s ∈ (sourceProgram N r
      ((compiledCalendarProgram N C H gamma (fun _ => true)).take
        (bankFirstMeetingIndex N C H gamma r coin i j))
      (initialCode N sample (originalRegister N coin))).support) :
    completionReader N r Finset.univ unrankedViewForest s {toUnranked (comb b as)} =
      if liveCard s = Fintype.card Copy then
        ENNReal.ofReal (2^as.length /
          ((Nat.factorial (as.length+1) : ℝ) * (Nat.factorial as.length : ℝ))) else 0 := by
  by_cases hc : liveCard s = Fintype.card Copy
  · rw [if_pos hc]
    apply reader_flat_comb_mass N r s b as _ hcover hnodup hnot hne
    exact (flat_iff_full_card (state s) s.property.forest).mpr hc
  · rw [if_neg hc]
    rcases isolated_flat_or_bad (state s) s.property.forest b
      (enumerated_cut_B_isolated N C H gamma r coin i j sample b hb ha hs) with hf | hbad
    · exact False.elim (hc ((flat_iff_full_card (state s) s.property.forest).mp hf))
    · obtain ⟨x,hx⟩ := hbad
      exact reader_obstructed_comb_mass N r s b x as hx

lemma enumerated_fixed_bank_comb_mass [Nonempty Copy] (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (r : PositivePairRates E) (coin : Hybrid N → Bool) (i j : X)
    (sample : Copy → X) (b : Copy) (hb : sample b = j)
    (ha : ∀ x, x ≠ b → sample x = i) (as : List Copy)
    (hcover : ∀ x, x = b ∨ x ∈ as) (hnodup : as.Nodup) (hnot : b ∉ as) (hne : as ≠ []) :
    (((sourceProgram N r (compiledCalendarProgram N C H gamma (fun _ => true))
      (initialCode N sample (originalRegister N coin))).bind (completionKernel N r)).map
      (fun d => sourceUnrankedForest (state d) Finset.univ)) {toUnranked (comb b as)} =
    ENNReal.ofReal (2^as.length /
      ((Nat.factorial (as.length+1) : ℝ) * (Nat.factorial as.length : ℝ))) *
    ENNReal.ofReal (Real.exp (-referenceExposure N r
      ((compiledCalendarProgram N C H gamma (fun _ => true)).take
        (bankFirstMeetingIndex N C H gamma r coin i j))
      (initialCode N sample (originalRegister N coin)))) := by
  let P := compiledCalendarProgram N C H gamma (fun _ => true)
  let m := bankFirstMeetingIndex N C H gamma r coin i j
  let start := initialCode N sample (originalRegister N coin)
  let c : ℝ≥0∞ := ENNReal.ofReal (2^as.length /
    ((Nat.factorial (as.length+1) : ℝ) * (Nat.factorial as.length : ℝ)))
  have hc : CommonOnlyWord N (P.take m) := selected_common_prefix N C H gamma m
  have hcard : liveCard start = Fintype.card Copy := by
    change (Finset.univ : Finset Copy).card = _
    exact Finset.card_univ
  change (((sourceProgram N r P start).bind (completionKernel N r)).map _)
    {toUnranked (comb b as)} = c * _
  conv_lhs => rw [show P = P.take m ++ P.drop m from (List.take_append_drop m P).symm]
  rw [sourceProgram_append,PMF.bind_bind,PMF.map_bind,PMF.bind_apply]
  rw [← actual_common_no_loss_exposure N r (P.take m) hc start,
    PMF.map_apply,← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro s
  by_cases hs : sourceProgram N r (P.take m) start s = 0
  · simp only [hs,zero_mul,ite_self,mul_zero]
  · have hsupport := (PMF.mem_support_iff _ _).mpr hs
    have hreader := actual_initialized_common_suffix_completion N C sample H gamma r coin
      Finset.univ unrankedViewForest (P.take m) (P.drop m) (List.take_append_drop m P).symm
      s hsupport (enumerated_cut_colocated N C H gamma r coin i j sample b hb ha hsupport)
    simp only [← actual_unranked_view_forest] at hreader
    change ((sourceProgram N r (P.drop m) s).bind (completionKernel N r)).map
      (fun d => sourceUnrankedForest (state d) Finset.univ) =
      completionReader N r Finset.univ unrankedViewForest s at hreader
    rw [hreader,enumerated_cut_comb_row N C H gamma r coin i j sample b hb ha as
      hcover hnodup hnot hne hsupport,hcard]
    by_cases he : liveCard s = Fintype.card Copy
    · simp only [if_pos he,if_pos he.symm]
      exact mul_comm _ _
    · simp only [if_neg he,if_neg (Ne.symm he),mul_zero]

lemma enumerated_population_choose (s : State V E Copy) (b : Copy) (as : List Copy)
    (hcover : ∀ x, x = b ∨ x ∈ as) (hnodup : as.Nodup) (hnot : b ∉ as)
    (a z place : Location V E) (hsep : a ≠ z) (hlive : s.live = Finset.univ)
    (ha : ∀ x, x ≠ b → s.location x = a) (hb : s.location b = z) :
    (populationRoots s place).card.choose 2 = if a = place then as.length.choose 2 else 0 := by
  by_cases hap : a = place
  · have hzp : z ≠ place := by intro h; exact hsep (hap.trans h.symm)
    have he : populationRoots s place = as.toFinset := by
      ext x
      by_cases hx : x = b
      · subst x
        simp [populationRoots,hlive,hb,hzp,hnot]
      · have hm : x ∈ as := (hcover x).resolve_left hx
        simp [populationRoots,hlive,ha x hx,hap,hm]
    rw [he,List.toFinset_card_of_nodup hnodup]
    simp [hap]
  · by_cases hzp : z = place
    · have he : populationRoots s place = {b} := by
        ext x
        by_cases hx : x = b
        · subst x; simp [populationRoots,hlive,hb,hzp]
        · simp [populationRoots,hlive,ha x hx,hap,hx]
      simp [he,hap]
    · have he : populationRoots s place = ∅ := by
        ext x
        by_cases hx : x = b
        · subst x; simp [populationRoots,hlive,hb,hzp]
        · simp [populationRoots,hlive,ha x hx,hap]
      simp [he,hap]

lemma enumerated_prefix_rate (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (r : PositivePairRates E) (coin : Hybrid N → Bool) (i j : X)
    (sample : Copy → X) (b : Copy) (hb : sample b = j)
    (ha : ∀ x, x ≠ b → sample x = i) (as : List Copy)
    (hcover : ∀ x, x = b ∨ x ∈ as) (hnodup : as.Nodup) (hnot : b ∉ as)
    (q : Nat) (hq : q < bankFirstMeetingIndex N C H gamma r coin i j) :
    totalRate N r (fixedRegisterPrefix N
      ((compiledCalendarProgram N C H gamma (fun _ => true)).take q)
      (initialCode N sample (originalRegister N coin))) =
      (as.length.choose 2 : ℝ) * ∑ e : Option E,
        if copyLocation (state (pairReference N C H gamma coin i j q)) true = originalPlace N e
        then pairRate r e else 0 := by
  let P := (compiledCalendarProgram N C H gamma (fun _ => true)).take q
  let a := copyLocation (state (pairReference N C H gamma coin i j q)) true
  let z := copyLocation (state (pairReference N C H gamma coin i j q)) false
  let s := fixedRegisterPrefix N P (initialCode N sample (originalRegister N coin))
  have hsep : a ≠ z := before_bankFirstMeeting_separated N C H gamma r coin i j q hq
  have hl : (state s).live = Finset.univ := initial_reference_live N _ _ P
  have hanc (x : Copy) : (state s).ancestor x = x :=
    s.property.forest.representative x (by change x ∈ (state s).live; rw [hl]; exact Finset.mem_univ x)
  have haloc : ∀ x, x ≠ b → (state s).location x = a := by
    intro x hx
    have h := initial_reference_location_cross_carrier N sample (pairSample i j)
      (originalRegister N coin) P x true (by simpa [pairSample] using ha x hx)
    change copyLocation (state s) x = a at h
    simpa only [copyLocation,hanc] using h
  have hbloc : (state s).location b = z := by
    have h := initial_reference_location_cross_carrier N sample (pairSample i j)
      (originalRegister N coin) P b false (by simpa [pairSample] using hb)
    change copyLocation (state s) b = z at h
    simpa only [copyLocation,hanc] using h
  change totalRate N r s = (as.length.choose 2 : ℝ) * _
  rw [actual_rate_choose_two,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  rw [enumerated_population_choose (state s) b as hcover hnodup hnot a z (originalPlace N e)
    hsep hl haloc hbloc]
  by_cases h : a = originalPlace N e
  · simp only [if_pos h]
    exact mul_comm _ _
  · simp [h]

lemma enumerated_exposure_scale (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (r : PositivePairRates E) (coin : Hybrid N → Bool) (i j : X)
    (sample : Copy → X) (b : Copy) (hb : sample b = j)
    (ha : ∀ x, x ≠ b → sample x = i) (as : List Copy)
    (hcover : ∀ x, x = b ∨ x ∈ as) (hnodup : as.Nodup) (hnot : b ∉ as) :
    referenceExposure N r
      ((compiledCalendarProgram N C H gamma (fun _ => true)).take
        (bankFirstMeetingIndex N C H gamma r coin i j))
      (initialCode N sample (originalRegister N coin)) =
    (as.length.choose 2 : ℝ) * bankExclusiveExposure N C H gamma r coin i j := by
  unfold bankExclusiveExposure
  apply reference_exposure_scale_of_prefix_rates
  intro q hq
  have hm : q < bankFirstMeetingIndex N C H gamma r coin i j :=
    lt_of_lt_of_le hq (List.length_take_le _ _)
  have ht : (((compiledCalendarProgram N C H gamma (fun _ => true)).take
      (bankFirstMeetingIndex N C H gamma r coin i j)).take q) =
      (compiledCalendarProgram N C H gamma (fun _ => true)).take q := by
    rw [List.take_take,Nat.min_eq_left (Nat.le_of_lt hm)]
  rw [ht,enumerated_prefix_rate N C H gamma r coin i j sample b hb ha as hcover hnodup hnot q hm]
  have h2 := enumerated_prefix_rate N C H gamma r coin i j (repeatedSample 2 i j)
    (Sum.inr ()) rfl (by
      intro x hx
      cases x with
      | inl x => rfl
      | inr x => cases x; exact False.elim (hx rfl))
    (canonicalA 2) (canonicalA_cover 2) (canonicalA_nodup 2) (canonicalA_excludes_B 2) q hm
  have hlen : (canonicalA 2).length = 2 := by simp [canonicalA]
  rw [hlen] at h2
  norm_num at h2
  rw [h2]

lemma enumerated_fixed_bank_comb_power [Nonempty Copy] (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (coin : Hybrid N → Bool) (i j : X)
    (sample : Copy → X) (b : Copy) (hb : sample b = j)
    (ha : ∀ x, x ≠ b → sample x = i) (as : List Copy)
    (hcover : ∀ x, x = b ∨ x ∈ as) (hnodup : as.Nodup) (hnot : b ∉ as) (hne : as ≠ []) :
    (((sourceProgram N r (compiledCalendarProgram N C H (originalGamma p) (fun _ => true))
      (initialCode N sample (originalRegister N coin))).bind (completionKernel N r)).map
      (fun d => sourceUnrankedForest (state d) Finset.univ)) {toUnranked (comb b as)} =
    ENNReal.ofReal (2^as.length /
      ((Nat.factorial (as.length+1) : ℝ) * (Nat.factorial as.length : ℝ))) *
      (bankSurvival N C H p r coin i j)^(as.length.choose 2) := by
  rw [enumerated_fixed_bank_comb_mass N C H (originalGamma p) r coin i j sample b hb ha as
    hcover hnodup hnot hne,
    enumerated_exposure_scale N C H (originalGamma p) r coin i j sample b hb ha as hcover hnodup hnot]
  congr 1
  unfold bankSurvival
  rw [show -((as.length.choose 2 : ℝ) * bankExclusiveExposure N C H (originalGamma p) r coin i j) =
    (as.length.choose 2 : ℝ) * (-bankExclusiveExposure N C H (originalGamma p) r coin i j) by ring,
    Real.exp_nat_mul,ENNReal.ofReal_pow (Real.exp_pos _).le]

/-- The actual subtype initialization and source evolution, with the same
original prior, have the specified ordered-comb moment formula. -/
theorem enumerated_natural_comb_moment [Nonempty Copy] (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (i j : X) (sample : Copy → X)
    (b : Copy) (hb : sample b = j) (ha : ∀ x, x ≠ b → sample x = i) (as : List Copy)
    (hcover : ∀ x, x = b ∨ x ∈ as) (hnodup : as.Nodup) (hnot : b ∉ as) (hne : as ≠ []) :
    naturalCompletedUnrankedLaw N C sample H p (fun _ => true) r {toUnranked (comb b as)} =
      ENNReal.ofReal (2^as.length /
        ((Nat.factorial (as.length+1) : ℝ) * (Nat.factorial as.length : ℝ))) *
      ∑' coin : Hybrid N → Bool, (originalRegisterMeasure N p).toPMF coin *
        (bankSurvival N C H p r coin i j)^(as.length.choose 2) := by
  rw [naturalCompletedUnrankedLaw,naturalCompletedLaw,naturalCalendarLaw,
    originalRegisterPMF,PMF.bind_map,PMF.bind_bind,PMF.map_bind,PMF.bind_apply,
    ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro coin
  simp only [Function.comp_apply]
  have h := enumerated_fixed_bank_comb_power N C H p r coin i j sample b hb ha as
    hcover hnodup hnot hne
  change (((sourceProgram N r (compiledCalendarProgram N C H (originalGamma p) (fun _ => true))
    (initialCode N sample (originalRegister N coin))).bind
    (ancestralCompletion N r (Fintype.card Copy))).map
    (fun d => sourceUnrankedForest (state d) Finset.univ)) {toUnranked (comb b as)} =
    ENNReal.ofReal (2^as.length /
      ((Nat.factorial (as.length+1) : ℝ) * (Nat.factorial as.length : ℝ))) *
      (bankSurvival N C H p r coin i j)^(as.length.choose 2) at h
  rw [h]
  ac_rfl

section LabelMaps
variable {A B : Type*} [DecidableEq A] [DecidableEq B]

lemma mapLabels_leftInverse (f : A → B) (g : B → A) (h : Function.LeftInverse g f)
    (t : Genealogy A) : mapLabels g (mapLabels f t) = t := by
  induction t with
  | leaf a => simp [mapLabels,h a]
  | graft l r ihl ihr => simp [mapLabels,ihl,ihr]

lemma mapUnranked_leftInverse (f : A → B) (g : B → A) (hinv : Function.LeftInverse g f) :
    Function.LeftInverse (mapUnranked g) (mapUnranked f) := by
  intro q
  induction q using Quotient.inductionOn with
  | h t =>
    change toUnranked (mapLabels g (mapLabels f t)) = toUnranked t
    rw [mapLabels_leftInverse f g hinv]

lemma mapLabels_fold_comb (f : A → B) (as : List A) (t : Genealogy A) :
    mapLabels f (as.foldl (fun t a => .graft t (.leaf a)) t) =
      (as.map f).foldl (fun t a => .graft t (.leaf a)) (mapLabels f t) := by
  induction as generalizing t with
  | nil => rfl
  | cons a as ih =>
    simp only [List.foldl_cons,List.map_cons]
    exact ih _

lemma mapLabels_comb (f : A → B) (b : A) (as : List A) :
    mapLabels f (comb b as) = comb (f b) (as.map f) := by
  unfold comb
  rw [mapLabels_fold_comb]
  rfl
end LabelMaps

lemma selected_mapUnranked_injective (keep : Finset Copy) (b : SelectedCopy keep) :
    Function.Injective (mapUnranked (Subtype.val : SelectedCopy keep → Copy)) := by
  let g : Copy → SelectedCopy keep := fun x => if h : x ∈ keep then ⟨x,h⟩ else b
  have hg : Function.LeftInverse g (Subtype.val : SelectedCopy keep → Copy) := by
    intro x
    simp only [g,dif_pos x.property]
  exact (mapUnranked_leftInverse Subtype.val g hg).injective

lemma pmf_map_injective_mass {A B : Type*} (p : PMF A) (f : A → B)
    (hf : Function.Injective f) (a : A) : (p.map f) (f a) = p a := by
  rw [PMF.map_apply,tsum_eq_single a]
  · simp
  · intro b hb
    have hne : f a ≠ f b := by intro h; exact hb (hf h).symm
    simp [hne]

/-- A deterministic readout of the ORIGINAL full observed forest. All
initialization/projectivity work uses the actual selected subtype. -/
theorem actual_full_panel_selected_comb_moment (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (i j : X) (sample : Copy → X)
    (hsurj : Function.Surjective sample) (keep : Finset Copy)
    (b : SelectedCopy keep) (hb : sample b.val = j)
    (ha : ∀ x : SelectedCopy keep, x ≠ b → sample x.val = i)
    (as : List (SelectedCopy keep)) (hcover : ∀ x, x = b ∨ x ∈ as)
    (hnodup : as.Nodup) (hnot : b ∉ as) (hne : as ≠ []) :
    ((naturalCompletedUnrankedLaw N C sample H p (fun _ => true) r).map (pruneForest keep))
      {toUnranked (comb b.val (as.map Subtype.val))} =
    ENNReal.ofReal (2^as.length /
      ((Nat.factorial (as.length+1) : ℝ) * (Nat.factorial as.length : ℝ))) *
      ∑' coin : Hybrid N → Bool, (originalRegisterMeasure N p).toPMF coin *
        (bankSurvival N C H p r coin i j)^(as.length.choose 2) := by
  letI : Nonempty (SelectedCopy keep) := ⟨b⟩
  have hobs : (naturalCompletedUnrankedLaw N C sample H p (fun _ => true) r).map
      (pruneForest keep) =
      (naturalCompletedUnrankedLaw N C (selectedSample sample keep) H p (fun _ => true) r).map
        (fun F => F.image (mapUnranked Subtype.val)) := by
    calc
      _ = (naturalCompletedLaw N C sample H p (fun _ => true) r).map
          (fun s => sourceUnrankedForest (state s) keep) := by
        unfold naturalCompletedUnrankedLaw
        rw [PMF.map_comp]
        congr 1
        funext s
        exact prune_source_forest (state s) s.property.forest keep
      _ = _ := actual_complete_unranked_all_panel_projectivity N C sample keep H p (fun _ => true) r
  have he : ({toUnranked (comb b as)} : Finset (UnrankedTree (SelectedCopy keep))).image
      (mapUnranked Subtype.val) = {toUnranked (comb b.val (as.map Subtype.val))} := by
    simp only [Finset.image_singleton,mapUnranked_toUnranked,mapLabels_comb]
  rw [hobs,← he,pmf_map_injective_mass _ _
    (Finset.image_injective (selected_mapUnranked_injective keep b))]
  exact enumerated_natural_comb_moment N C H p r i j (selectedSample sample keep)
    b hb ha as hcover hnodup hnot hne

/-- Every original taxon has an explicit padding copy, at every queried
arity. Only the left canonical panel is retained by the passive readout. -/
def paddedSample (k : Nat) (i j : X) : ((Fin k ⊕ Unit) ⊕ X) → X :=
  Sum.elim (repeatedSample k i j) id

noncomputable def paddedKeep (k : Nat) : Finset ((Fin k ⊕ Unit) ⊕ X) :=
  Finset.univ.image Sum.inl

noncomputable def paddedCopy (k : Nat) (a : Fin k ⊕ Unit) : SelectedCopy (paddedKeep (X := X) k) :=
  ⟨Sum.inl a,Finset.mem_image.mpr ⟨a,Finset.mem_univ a,rfl⟩⟩

noncomputable def paddedB (k : Nat) : SelectedCopy (paddedKeep (X := X) k) := paddedCopy k (Sum.inr ())
noncomputable def paddedA (k : Nat) : List (SelectedCopy (paddedKeep (X := X) k)) :=
  (canonicalA k).map (paddedCopy k)

lemma paddedCopy_injective (k : Nat) : Function.Injective (paddedCopy (X := X) k) := by
  intro a b h
  exact Sum.inl_injective (congrArg Subtype.val h)

lemma padded_cover (k : Nat) (x : SelectedCopy (paddedKeep (X := X) k)) :
    x = paddedB k ∨ x ∈ paddedA k := by
  obtain ⟨a,_,ha⟩ := Finset.mem_image.mp x.property
  have hx : x = paddedCopy k a := Subtype.ext ha.symm
  rw [hx]
  rcases canonicalA_cover k a with hb | hm
  · left; subst a; rfl
  · exact Or.inr (List.mem_map.mpr ⟨a,hm,rfl⟩)

lemma padded_sample_A (k : Nat) (i j : X) (x : SelectedCopy (paddedKeep (X := X) k))
    (hx : x ≠ paddedB k) : paddedSample k i j x.val = i := by
  obtain ⟨a,_,ha⟩ := Finset.mem_image.mp x.property
  rw [← ha]
  cases a with
  | inl a => rfl
  | inr a =>
    cases a
    exact False.elim (hx (Subtype.ext ha.symm))

lemma paddedA_nodup (k : Nat) : (paddedA (X := X) k).Nodup :=
  (canonicalA_nodup k).map (paddedCopy_injective k)

lemma paddedA_excludes_B (k : Nat) : paddedB (X := X) k ∉ paddedA k := by
  intro h
  obtain ⟨a,ha,he⟩ := List.mem_map.mp h
  have hab : a = Sum.inr () := paddedCopy_injective k he
  exact canonicalA_excludes_B k (hab ▸ ha)

lemma paddedA_length (k : Nat) : (paddedA (X := X) k).length = k := by
  simp [paddedA,canonicalA]

noncomputable def legalCombProbability (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (k : Nat) : ℝ≥0∞ :=
  ((naturalCompletedUnrankedLaw N C (paddedSample k i j) H p (fun _ => true) r).map
    (pruneForest (paddedKeep k)))
    {toUnranked (comb (paddedB (X := X) k).val ((paddedA k).map Subtype.val))}

/-- End-to-end legal all-original-taxa query, uniformly for every k > 0.
It equals the canonical probability for the SAME source and original prior. -/
theorem actual_legal_comb_probability (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (k : Nat) (hk : 0 < k) :
    legalCombProbability N C H p r i j k =
      naturalCompletedUnrankedLaw N C (repeatedSample k i j) H p (fun _ => true) r
        {toUnranked (comb (Sum.inr ()) (canonicalA k))} := by
  have hsurj : Function.Surjective (paddedSample k i j) := fun x => ⟨Sum.inr x,rfl⟩
  have hne : paddedA (X := X) k ≠ [] := by
    intro h
    have hl := congrArg List.length h
    rw [paddedA_length,List.length_nil] at hl
    omega
  unfold legalCombProbability
  rw [actual_full_panel_selected_comb_moment N C H p r i j (paddedSample k i j) hsurj
    (paddedKeep k) (paddedB k) rfl (padded_sample_A k i j) (paddedA k) (padded_cover k)
    (paddedA_nodup k) (paddedA_excludes_B k) hne,paddedA_length,
    actual_natural_completed_comb_moment N C H p r i j k hk]

/-- This is the actual legal full-panel normalized moment used by the
semantic certificate and rival-uniqueness theorems, with no new oracle. -/
theorem actual_legal_observed_moment (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (i j : X) (k : Nat) (hk : 0 < k) :
    (legalCombProbability N C H p r i j k).toReal / combCoefficient k =
      observedMoment N C H p r i j k := by
  rw [actual_legal_comb_probability N C H p r i j k hk]
  rfl

#print axioms enumerated_natural_comb_moment
#print axioms actual_full_panel_selected_comb_moment
#print axioms actual_legal_observed_moment
end DotG4.ActualLegalPanelComb
