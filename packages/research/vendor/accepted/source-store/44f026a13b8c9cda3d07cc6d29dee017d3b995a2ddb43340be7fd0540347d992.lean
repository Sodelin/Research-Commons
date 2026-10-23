import G4ActualLegalPanelComb
import G5CommonSwitchingQuartetWitness
import G1InitializedFrontierPrefix
import G7EdgeExposureAccounting

/-!
# Same original bank: first-cut clock and original selected-edge path

Contributor: dot (OpenAI), 12 October 2026. UNCOMPILED candidate.
Formal composition of accepted D2-J hand work. The final path identity is
derived in this single source draft; no conditional weighted-tree law or
algorithmic RCF endpoint is assumed.
-/
namespace DotG4.ActualSelectedPathExposure
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeCommonPairGerm UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarTiming
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceNaturalInitialization
open GProgram.G5.SafePrefixRouteBridge GProgram.G5.OriginalEpochChart
open GProgram.G4.ActualCommonSelectorSupport
open G1NaturalCalendarNodes G1InitializedFrontierPrefix
open DotG4.ActualBankFirstMeeting DotG4.ActualFirstMeetingExposureScaling
open DotG4.ActualNaturalCombMoments DotG4.ActualLegalPanelComb
open scoped Classical NNReal ENNReal BigOperators
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Physical original edges, before any unary suppression. Shared stems cancel. -/
noncomputable def selectedDirectedExposure (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (r : PositivePairRates E) (coin : Hybrid N → Bool) (i j : X) : ℝ :=
  ∑ e : E, if e ∈ (commonRoutes N C H coin).edges i ∧
      e ∉ (commonRoutes N C H coin).edges j then
    pairRate r (some e) * (C.age (N.graph.source e) - C.age (N.graph.target e)) else 0

lemma selectedDirectedExposure_self (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (r : PositivePairRates E) (coin : Hybrid N → Bool) (i : X) :
    selectedDirectedExposure N C H r coin i i = 0 := by
  simp [selectedDirectedExposure]

/-- Exact deterministic source clock fold with an explicit state readout. -/
noncomputable def readoutExposure (N : RootedBinary V E X) {sample : Copy → X}
    (rate : Code N sample → ℝ) : List (ProgramStep N) → Code N sample → ℝ
  | [], _ => 0
  | .interval t :: ops, s => rate s * (t : ℝ) + readoutExposure N rate ops s
  | .boundary b :: ops, s => readoutExposure N rate ops (fixedRegisterBoundary N b s)

lemma readoutExposure_append (N : RootedBinary V E X) {sample : Copy → X}
    (rate : Code N sample → ℝ) (xs ys : List (ProgramStep N)) (s : Code N sample) :
    readoutExposure N rate (xs ++ ys) s = readoutExposure N rate xs s +
      readoutExposure N rate ys (fixedRegisterPrefix N xs s) := by
  induction xs generalizing s with
  | nil => simp [readoutExposure,fixedRegisterPrefix]
  | cons op xs ih =>
    cases op with
    | interval t => simp only [List.cons_append,readoutExposure,fixedRegisterPrefix,ih]; ring
    | boundary b => simpa only [List.cons_append,readoutExposure,fixedRegisterPrefix] using
        (ih (fixedRegisterBoundary N b s))

lemma reference_eq_readout_of_prefix_rates (N : RootedBinary V E X)
    {Other : Type*} [Fintype Other] [DecidableEq Other]
    {sample : Copy → X} {sample' : Other → X} (r : PositivePairRates E)
    (rate : Code N sample' → ℝ) (ops : List (ProgramStep N))
    (s : Code N sample) (z : Code N sample')
    (hr : ∀ q < ops.length,
      totalRate N r (fixedRegisterPrefix N (ops.take q) s) =
        rate (fixedRegisterPrefix N (ops.take q) z)) :
    referenceExposure N r ops s = readoutExposure N rate ops z := by
  induction ops generalizing s z with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | interval t =>
      have h0 := hr 0 (by simp)
      simp only [List.take_zero,fixedRegisterPrefix] at h0
      have ht : ∀ q < ops.length,
          totalRate N r (fixedRegisterPrefix N (ops.take q) s) =
            rate (fixedRegisterPrefix N (ops.take q) z) := by
        intro q hq
        have h := hr (q+1) (by simpa using Nat.succ_lt_succ hq)
        simpa only [List.take_succ_cons,fixedRegisterPrefix] using h
      simp only [referenceExposure,readoutExposure]
      rw [h0,ih s z ht]
    | boundary b =>
      apply ih (fixedRegisterBoundary N b s) (fixedRegisterBoundary N b z)
      intro q hq
      have h := hr (q+1) (by simpa using Nat.succ_lt_succ hq)
      simpa only [List.take_succ_cons,fixedRegisterPrefix] using h

noncomputable def separatedRate (N : RootedBinary V E X) (r : PositivePairRates E)
    {sample : Bool → X} (s : Code N sample) : ℝ :=
  if copyLocation (state s) true = copyLocation (state s) false then 0 else
    ∑ e : Option E, if copyLocation (state s) true = originalPlace N e then pairRate r e else 0

lemma separated_exposure_zero (N : RootedBinary V E X) (r : PositivePairRates E)
    {sample : Bool → X} (ops : List (ProgramStep N)) (s : Code N sample)
    (h : copyLocation (state s) true = copyLocation (state s) false) :
    readoutExposure N (separatedRate N r) ops s = 0 := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
    cases op with
    | interval t => simp [readoutExposure,separatedRate,h,ih s h]
    | boundary b =>
      apply ih (fixedRegisterBoundary N b s)
      rw [fixedRegisterBoundary_copyLocation,fixedRegisterBoundary_copyLocation,h]

/-- The same operation-index cut equals a full-calendar clock with the
post-meeting contribution proved zero, rather than dropped by assumption. -/
theorem bankExclusiveExposure_eq_whole_separated_clock (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (r : PositivePairRates E)
    (coin : Hybrid N → Bool) (i j : X) :
    bankExclusiveExposure N C H gamma r coin i j =
      readoutExposure N (separatedRate N r)
        (compiledCalendarProgram N C H gamma (fun _ => true))
        (initialCode N (pairSample i j) (originalRegister N coin)) := by
  let P := compiledCalendarProgram N C H gamma (fun _ => true)
  let m := bankFirstMeetingIndex N C H gamma r coin i j
  let z := initialCode N (pairSample i j) (originalRegister N coin)
  have hp : bankExclusiveExposure N C H gamma r coin i j =
      readoutExposure N (separatedRate N r) (P.take m) z := by
    unfold bankExclusiveExposure
    apply reference_eq_readout_of_prefix_rates
    intro q hq
    have hm : q < m := lt_of_lt_of_le hq (List.length_take_le _ _)
    have ht : (P.take m).take q = P.take q := by
      rw [List.take_take,Nat.min_eq_left hm.le]
    rw [ht]
    have hsep := before_bankFirstMeeting_separated N C H gamma r coin i j q hm
    have hr := enumerated_prefix_rate N C H gamma r coin i j (repeatedSample 2 i j)
      (Sum.inr ()) rfl (by
        intro x hx
        cases x with
        | inl x => rfl
        | inr x => cases x; exact False.elim (hx rfl))
      (canonicalA 2) (canonicalA_cover 2) (canonicalA_nodup 2) (canonicalA_excludes_B 2) q hm
    have hlen : (canonicalA 2).length = 2 := by simp [canonicalA]
    rw [hlen] at hr
    simp only [Nat.choose_self,Nat.cast_one,one_mul] at hr
    change totalRate N r (fixedRegisterPrefix N (P.take q)
      (initialCode N (repeatedSample 2 i j) (originalRegister N coin))) =
      separatedRate N r (pairReference N C H gamma coin i j q)
    rw [hr,separatedRate,if_neg hsep]
  have hz : readoutExposure N (separatedRate N r) (P.drop m)
      (fixedRegisterPrefix N (P.take m) z) = 0 := by
    apply separated_exposure_zero
    exact (bankFirstMeeting_spec N C H gamma r coin i j).2
  change bankExclusiveExposure N C H gamma r coin i j = readoutExposure N (separatedRate N r) P z
  conv_rhs => rw [show P = P.take m ++ P.drop m from (List.take_append_drop m P).symm]
  rw [readoutExposure_append,hz,add_zero,hp]

-- The next assembly binds the interval readout to active selected-route
-- difference edges, then applies the exact physical date telescope.

/-- Existing natural-node support supplies per-copy birth handling; no
contemporaneous-tip specialization is used. -/
lemma actual_epoch_natural_state (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (pre post : List ℝ) (guard : ℝ) (elapsed : ℝ≥0)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: post)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r
      (prefixThrough N C H gamma common pre guard ++ [.interval elapsed])
      (initialCode N sample register)).support) :
    NaturalState N C sample guard (state d) := by
  rw [sourceProgram_append] at hd
  obtain ⟨s,hs,hds⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  have hs' := hs
  rw [prefixThrough_eq_before_batch N C H gamma common pre post guard hsplit,
    sourceProgram_append] at hs'
  obtain ⟨z,hz,hsz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs'
  have hg : guard ∈ sortedOriginalDates N C := by rw [hsplit]; simp
  have hn := (actual_initialized_before_boundary_support N C sample register H gamma common r
    guard hg hz).2.1
  have hsn := actual_boundary_batch_natural N C H gamma common r guard z hn hsz
  apply actual_time_natural N C r elapsed s guard hsn
  simpa only [sourceProgram,sourceProgramStep,PMF.bind_pure] using hds

lemma common_route_edge_age_bounds (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (coin : Hybrid N → Bool) (x : X) (e : E)
    (he : e ∈ (commonRoutes N C H coin).edges x) :
    C.age (N.leaf x) ≤ C.age (N.graph.target e) ∧
      C.age (N.graph.source e) ≤ C.age N.root := by
  obtain ⟨pre,post,_,hpre,hpost⟩ :=
    GProgram.G5.ComponentCalendar.EdgePath.split_at_original_edge
      ((commonRoutes N C H coin).valid x) he
  exact ⟨C.age_le_of_directed hpost.directed,C.age_le_of_directed hpre.directed⟩

/-- The actual selector and existing natural/epoch invariants identify the
occupied selected edge at each positive-time epoch, including heterochronous
samples. This is an iff, stronger than route membership alone. -/
lemma natural_epoch_selected_edge_iff (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (coin : Hybrid N → Bool)
    {sample : Copy → X} (d : Code N sample) (guard next : ℝ) (hlt : guard < next)
    (hepoch : EpochCompatible N C guard next (state d))
    (hnatural : NaturalNodes N C sample guard (state d))
    (hselector : ∀ x, SelectorLocation N (coinSelector N H coin) (sample x)
      (copyLocation (state d) x)) (x : Copy) (e : E) :
    copyLocation (state d) x = .edge e ↔
      e ∈ (commonRoutes N C H coin).edges (sample x) ∧ C.Active guard e := by
  constructor
  · intro he
    refine ⟨?_,epoch_edge_active N C hepoch he le_rfl hlt⟩
    have hs := hselector x
    rw [he] at hs
    exact selectorLocation_edge_mem_compiled N C (coinSelector N H coin) (sample x) e hs
  · rintro ⟨hem,hea⟩
    have hb := common_route_edge_age_bounds N C H coin (sample x) e hem
    cases hl : copyLocation (state d) x with
    | node v =>
      have ht := hepoch x
      rw [hl] at ht
      rcases hnatural x v hl with hv | hv
      · subst v
        exact False.elim (not_lt_of_ge (ht.trans (hb.1.trans hea.1)) hlt)
      · exact False.elim (not_lt_of_ge (ht.trans hv) hlt)
    | edge f =>
      have hs := hselector x
      rw [hl] at hs
      have hfm : f ∈ (commonRoutes N C H coin).edges (sample x) :=
        selectorLocation_edge_mem_compiled N C (coinSelector N H coin) (sample x) f hs
      have hfa := epoch_edge_active N C hepoch hl le_rfl hlt
      have hfe : f = e := ((commonRoutes N C H coin).valid (sample x)).active_unique C hfm hem hfa hea
      exact congrArg Location.edge hfe
    | rootPopulation v =>
      have ht := hepoch x
      rw [hl] at ht
      exact False.elim (not_lt_of_ge (hb.2.trans ht.2) hea.2)

/-- Specialization to the actual same-bank deterministic calendar prefix.
The elapsed interval may be zero; all tied boundary operations are retained. -/
theorem actual_epoch_selected_edge_iff (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (coin : Hybrid N → Bool)
    (pre post : List ℝ) (guard next : ℝ) (elapsed : ℝ≥0)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post) :
    let past := prefixThrough N C H (originalGamma p) (fun _ => true) pre guard ++ [.interval elapsed]
    let d := fixedRegisterPrefix N past (initialCode N sample (originalRegister N coin))
    ∀ x e, copyLocation (state d) x = .edge e ↔
      e ∈ (commonRoutes N C H coin).edges (sample x) ∧ C.Active guard e := by
  dsimp only
  have hgeo := actual_fixed_cut_source_geometry N C sample H p (fun _ => true) r
    pre post guard next elapsed hsplit coin
  have hnat := actual_epoch_natural_state N C sample (originalRegister N coin) H (originalGamma p)
    (fun _ => true) r pre (next::post) guard elapsed hsplit hgeo.1
  have hord : (pre ++ guard :: next :: post).Pairwise (· < ·) := by
    rw [← hsplit]; exact original_dates_strict N C
  have hlt : guard < next := (List.pairwise_cons.mp (List.pairwise_append.mp hord).2.1).1 next (by simp)
  intro x e
  exact natural_epoch_selected_edge_iff N C H coin _ guard next hlt hgeo.2.1 hnat.1 hgeo.2.2 x e

-- Remaining assembly: evaluate separatedRate by this actual selected-edge
-- iff, sum the complete calendar's physical intervals, and telescope each
-- original selected edge to its full rate-times-duration.

lemma natural_epoch_root_location (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (coin : Hybrid N → Bool)
    {sample : Copy → X} (d : Code N sample) (guard next : ℝ) (hlt : guard < next)
    (hepoch : EpochCompatible N C guard next (state d))
    (hnatural : NaturalNodes N C sample guard (state d))
    (hselector : ∀ x, SelectorLocation N (coinSelector N H coin) (sample x)
      (copyLocation (state d) x)) (hroot : C.age N.root ≤ guard) (x : Copy) :
    copyLocation (state d) x = .rootPopulation N.root := by
  cases hl : copyLocation (state d) x with
  | node v =>
    have ht := hepoch x
    rw [hl] at ht
    rcases hnatural x v hl with hv | hv
    · subst v
      have hleaf := C.age_le_of_directed ((commonRoutes N C H coin).valid (sample x)).directed
      exact False.elim (not_lt_of_ge (ht.trans (hleaf.trans hroot)) hlt)
    · exact False.elim (not_lt_of_ge (ht.trans hv) hlt)
  | edge e =>
    have hh := (natural_epoch_selected_edge_iff N C H coin d guard next hlt hepoch hnatural
      hselector x e).mp hl
    have hb := common_route_edge_age_bounds N C H coin (sample x) e hh.1
    exact False.elim (not_lt_of_ge (hb.2.trans hroot) hh.2.2)
  | rootPopulation v =>
    have ht := hepoch x
    rw [hl] at ht
    exact congrArg Location.rootPopulation ht.1

noncomputable def selectedSeparatedRate (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E)
    (coin : Hybrid N → Bool) (i j : X) (t : ℝ) : ℝ :=
  ∑ e : E, if e ∈ (commonRoutes N C H coin).edges i ∧
      e ∉ (commonRoutes N C H coin).edges j ∧ C.Active t e then pairRate r (some e) else 0

lemma natural_epoch_separated_rate (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (coin : Hybrid N → Bool)
    (i j : X) (d : Code N (pairSample i j)) (guard next : ℝ) (hlt : guard < next)
    (hepoch : EpochCompatible N C guard next (state d))
    (hnatural : NaturalNodes N C (pairSample i j) guard (state d))
    (hselector : ∀ x, SelectorLocation N (coinSelector N H coin) (pairSample i j x)
      (copyLocation (state d) x)) :
    separatedRate N r d = selectedSeparatedRate N C H r coin i j guard := by
  have hA (e : E) : copyLocation (state d) true = .edge e ↔
      e ∈ (commonRoutes N C H coin).edges i ∧ C.Active guard e := by
    simpa only [pairSample,if_true] using natural_epoch_selected_edge_iff N C H coin d guard next
      hlt hepoch hnatural hselector true e
  have hB (e : E) : copyLocation (state d) false = .edge e ↔
      e ∈ (commonRoutes N C H coin).edges j ∧ C.Active guard e := by
    simpa only [pairSample,Bool.false_eq_true,if_false] using natural_epoch_selected_edge_iff
      N C H coin d guard next hlt hepoch hnatural hselector false e
  unfold separatedRate selectedSeparatedRate
  by_cases heq : copyLocation (state d) true = copyLocation (state d) false
  · rw [if_pos heq]
    symm
    apply Finset.sum_eq_zero
    intro e _
    have hn : ¬ (e ∈ (commonRoutes N C H coin).edges i ∧
        e ∉ (commonRoutes N C H coin).edges j ∧ C.Active guard e) := by
      rintro ⟨hi,hj,ha⟩
      have hl := (hA e).mpr ⟨hi,ha⟩
      rw [heq] at hl
      exact hj ((hB e).mp hl).1
    exact if_neg hn
  · rw [if_neg heq,Fintype.sum_option]
    have hn : copyLocation (state d) true ≠ originalPlace N none := by
      intro h
      have ht := hepoch true
      change copyLocation (state d) true = .rootPopulation N.root at h
      rw [h] at ht
      have hb := natural_epoch_root_location N C H coin d guard next hlt hepoch hnatural
        hselector ht.2 false
      exact heq (h.trans hb.symm)
    rw [if_neg hn,zero_add]
    apply Finset.sum_congr rfl
    intro e _
    have hc : copyLocation (state d) true = originalPlace N (some e) ↔
        e ∈ (commonRoutes N C H coin).edges i ∧
          e ∉ (commonRoutes N C H coin).edges j ∧ C.Active guard e := by
      constructor
      · intro h
        have hh := (hA e).mp h
        refine ⟨hh.1,?_,hh.2⟩
        intro hj
        exact heq (h.trans ((hB e).mpr ⟨hj,hh.2⟩).symm)
      · rintro ⟨hi,_,ha⟩
        exact (hA e).mpr ⟨hi,ha⟩
    simp only [hc]

/-- Source-native interval readout, with pending samples and the ancestral
population both accounted for by already derived actual invariants. -/
theorem actual_epoch_separated_rate (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (coin : Hybrid N → Bool) (i j : X)
    (pre post : List ℝ) (guard next : ℝ) (elapsed : ℝ≥0)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: next :: post) :
    separatedRate N r (fixedRegisterPrefix N
      (prefixThrough N C H (originalGamma p) (fun _ => true) pre guard ++ [.interval elapsed])
      (initialCode N (pairSample i j) (originalRegister N coin))) =
      selectedSeparatedRate N C H r coin i j guard := by
  have hgeo := actual_fixed_cut_source_geometry N C (pairSample i j) H p (fun _ => true) r
    pre post guard next elapsed hsplit coin
  have hnat := actual_epoch_natural_state N C (pairSample i j) (originalRegister N coin) H
    (originalGamma p) (fun _ => true) r pre (next::post) guard elapsed hsplit hgeo.1
  have hord : (pre ++ guard :: next :: post).Pairwise (· < ·) := by
    rw [← hsplit]; exact original_dates_strict N C
  have hlt : guard < next := (List.pairwise_cons.mp (List.pairwise_append.mp hord).2.1).1 next (by simp)
  exact natural_epoch_separated_rate N C H r coin i j _ guard next hlt hgeo.2.1 hnat.1 hgeo.2.2

/-- Scalar accumulation over the compiler's actual consecutive dates. -/
noncomputable def dateExposure (rate : ℝ → ℝ) : ℝ → List ℝ → ℝ
  | _, [] => 0
  | a, b :: bs => rate a * (b-a) + dateExposure rate b bs

noncomputable def activeDuration (lo hi : ℝ) (a : ℝ) (dates : List ℝ) : ℝ :=
  dateExposure (fun t => if lo ≤ t ∧ t < hi then 1 else 0) a dates

lemma activeDuration_after (lo hi a : ℝ) (dates : List ℝ)
    (ordered : (a::dates).Pairwise (· < ·)) (ha : hi ≤ a) :
    activeDuration lo hi a dates = 0 := by
  induction dates generalizing a with
  | nil => rfl
  | cons b bs ih =>
    rcases List.pairwise_cons.mp ordered with ⟨hab,hbs⟩
    have hb : a < b := hab b (by simp)
    have hn : ¬ (lo ≤ a ∧ a < hi) := fun h => (not_lt_of_ge ha) h.2
    simpa only [activeDuration,dateExposure,if_neg hn,zero_mul,zero_add] using
      ih b hbs (le_trans ha (le_of_lt hb))

/-- Reuse the accepted first-mark telescope after entering an original edge. -/
lemma activeDuration_eq_until (lo hi a : ℝ) (dates : List ℝ)
    (ordered : (a::dates).Pairwise (· < ·)) (present : hi ∈ dates)
    (hlo : lo ≤ a) :
    activeDuration lo hi a dates =
      GProgram.G7.EdgeExposureAccounting.untilDate (fun t => t = hi) a dates := by
  induction dates generalizing a with
  | nil => simp at present
  | cons b bs ih =>
    rcases List.pairwise_cons.mp ordered with ⟨ha,hbs⟩
    have ahi : a < hi := ha hi present
    have hactive : lo ≤ a ∧ a < hi := ⟨hlo,ahi⟩
    rcases List.mem_cons.mp present with h | h
    · subst b
      have hz := activeDuration_after lo hi hi bs hbs (le_refl _)
      simp only [activeDuration,dateExposure,if_pos hactive,one_mul,
        GProgram.G7.EdgeExposureAccounting.untilDate,if_true,add_zero]
      simpa only [activeDuration,add_zero] using congrArg (fun z => hi-a+z) hz
    · have bhi : b < hi := (List.pairwise_cons.mp hbs).1 hi h
      have hlo' : lo ≤ b := le_trans hlo (le_of_lt (ha b (by simp)))
      have hr := ih b hbs h hlo'
      simpa only [activeDuration,dateExposure,if_pos hactive,one_mul,
        GProgram.G7.EdgeExposureAccounting.untilDate,if_neg (ne_of_lt bhi)] using
        congrArg (fun z => b-a+z) hr

lemma activeDuration_from_start (lo hi : ℝ) (dates : List ℝ)
    (ordered : (lo::dates).Pairwise (· < ·)) (present : hi ∈ dates) :
    activeDuration lo hi lo dates = hi-lo := by
  rw [activeDuration_eq_until lo hi lo dates ordered present (le_refl _)]
  exact GProgram.G7.EdgeExposureAccounting.untilDate_first_mark
    (fun t => t = hi) lo hi dates ordered present rfl
    (fun d _ hd => ne_of_lt hd)

/-- Every original endpoint occurs in the compiler agenda. Dates before the
edge's own activation and after its exit add zero, including heterogeneous tips. -/
lemma activeDuration_full_dates (lo hi a : ℝ) (dates : List ℝ)
    (ordered : (a::dates).Pairwise (· < ·))
    (hlo : lo ∈ a::dates) (hhi : hi ∈ a::dates) (hlt : lo < hi) :
    activeDuration lo hi a dates = hi-lo := by
  induction dates generalizing a with
  | nil => simp only [List.mem_singleton] at hlo hhi; subst lo; subst hi; exact False.elim (lt_irrefl _ hlt)
  | cons b bs ih =>
    rcases List.pairwise_cons.mp ordered with ⟨ha,ht⟩
    rcases List.mem_cons.mp hlo with he | hlo
    · subst a
      have hhi' : hi ∈ b::bs := (List.mem_cons.mp hhi).resolve_left (ne_of_gt hlt)
      exact activeDuration_from_start lo hi (b::bs) ordered hhi'
    · have hal : a < lo := ha lo hlo
      have hhi' : hi ∈ b::bs := (List.mem_cons.mp hhi).resolve_left (by intro he; subst hi; linarith)
      have hn : ¬ (lo ≤ a ∧ a < hi) := fun h => (not_le_of_gt hal) h.1
      simpa only [activeDuration,dateExposure,if_neg hn,zero_mul,zero_add] using
        ih b ht hlo hhi'

lemma readoutExposure_boundary_map (N : RootedBinary V E X) {sample : Copy → X}
    (rate : Code N sample → ℝ) (bs : List (BoundaryOperation N)) (s : Code N sample) :
    readoutExposure N rate (bs.map ProgramStep.boundary) s = 0 := by
  induction bs generalizing s with
  | nil => rfl
  | cons b bs ih => simpa only [List.map_cons,readoutExposure] using ih (fixedRegisterBoundary N b s)

lemma readoutExposure_original_batch (N : RootedBinary V E X) {sample : Copy → X}
    (rate : Code N sample → ℝ) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (a : ℝ) (s : Code N sample) :
    readoutExposure N rate (boundaryOperations N C H gamma common a) s = 0 := by
  have hz (ops : List (ProgramStep N)) (z : Code N sample)
      (hb : ∀ op ∈ ops, ∃ b, op = ProgramStep.boundary b) :
      readoutExposure N rate ops z = 0 := by
    induction ops generalizing z with
    | nil => rfl
    | cons op ops ih =>
      obtain ⟨b,rfl⟩ := hb op (by simp)
      exact ih (fixedRegisterBoundary N b z)
        (fun q hq => hb q (List.mem_cons_of_mem _ hq))
  exact hz _ s (GProgram.G2.OriginalProgramSafety.original_batch_only_boundaries
    N C H gamma common a)

lemma prefixThrough_snoc (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (pre : List ℝ) (guard next : ℝ) :
    prefixThrough N C H gamma common (pre ++ [guard]) next =
      prefixThrough N C H gamma common pre guard ++
        .interval (Real.toNNReal (next-guard)) :: boundaryOperations N C H gamma common next := by
  cases pre with
  | nil => simp [prefixThrough,calendarTail]
  | cons a pre =>
    simp only [prefixThrough,List.cons_append,List.append_assoc,List.singleton_append,List.nil_append]
    rw [UnifiedLean.G6.PrivateRegisterCalendar.calendarTail_split_after_boundary
      N C H gamma common a guard pre [next]]
    simp only [calendarTail,List.append_nil,List.append_assoc]

lemma actual_tail_separated_clock (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (coin : Hybrid N → Bool) (i j : X) (pre : List ℝ) (guard : ℝ) (post : List ℝ)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: post) :
    readoutExposure N (separatedRate N r)
      (calendarTail N C H (originalGamma p) (fun _ => true) guard post)
      (fixedRegisterPrefix N (prefixThrough N C H (originalGamma p) (fun _ => true) pre guard)
        (initialCode N (pairSample i j) (originalRegister N coin))) =
      dateExposure (selectedSeparatedRate N C H r coin i j) guard post := by
  induction post generalizing pre guard with
  | nil => rfl
  | cons next post ih =>
    have hrate := actual_epoch_separated_rate N C H p r coin i j pre post guard next 0 hsplit
    simp only [fixedRegisterPrefix_append,fixedRegisterPrefix] at hrate
    have hord : (pre ++ guard :: next :: post).Pairwise (· < ·) := by
      rw [← hsplit]; exact original_dates_strict N C
    have hlt : guard < next := (List.pairwise_cons.mp (List.pairwise_append.mp hord).2.1).1 next (by simp)
    have hnext : sortedOriginalDates N C = (pre ++ [guard]) ++ next :: post := by
      simpa only [List.append_assoc,List.singleton_append] using hsplit
    have hrec := ih (pre ++ [guard]) next hnext
    rw [prefixThrough_snoc,fixedRegisterPrefix_append] at hrec
    simp only [fixedRegisterPrefix] at hrec
    rw [calendarTail,readoutExposure,readoutExposure_append,readoutExposure_original_batch,
      zero_add,hrate,Real.coe_toNNReal _ (sub_nonneg.mpr (le_of_lt hlt)),hrec]
    rfl

lemma dateExposure_selected_edges (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (coin : Hybrid N → Bool)
    (i j : X) (a : ℝ) (dates : List ℝ) :
    dateExposure (selectedSeparatedRate N C H r coin i j) a dates =
      ∑ e : E, if e ∈ (commonRoutes N C H coin).edges i ∧
        e ∉ (commonRoutes N C H coin).edges j then
        pairRate r (some e) * activeDuration (C.age (N.graph.target e))
          (C.age (N.graph.source e)) a dates else 0 := by
  induction dates generalizing a with
  | nil => simp [dateExposure,activeDuration]
  | cons b bs ih =>
    rw [dateExposure,ih,selectedSeparatedRate,Finset.sum_mul,← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro e _
    by_cases hi : e ∈ (commonRoutes N C H coin).edges i
    · by_cases hj : e ∈ (commonRoutes N C H coin).edges j
      · simp [hi,hj]
      · by_cases ha : C.age (N.graph.target e) ≤ a ∧ a < C.age (N.graph.source e)
        · simp only [hi,hj,not_false_eq_true,and_self,true_and,Calendar.Active,if_pos ha,
            if_true,activeDuration,dateExposure,one_mul]
          ring
        · simp [hi,hj,Calendar.Active,ha,activeDuration,dateExposure]
    · simp [hi]

/-- The actual first-meeting clock is exactly the directed exclusive path in
its own once-drawn original COMMON switching. All original date fragments,
including other taxa's activation dates, are retained in the telescope. -/
theorem actual_bank_cut_eq_selected_path (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N) (r : PositivePairRates E)
    (coin : Hybrid N → Bool) (i j : X) :
    bankExclusiveExposure N C H (originalGamma p) r coin i j =
      selectedDirectedExposure N C H r coin i j := by
  rw [bankExclusiveExposure_eq_whole_separated_clock]
  have hroot := original_date_scheduled N C N.root
  cases hd : sortedOriginalDates N C with
  | nil => simp [hd] at hroot
  | cons a dates =>
    have htail := actual_tail_separated_clock N C H p r coin i j [] a dates (by simpa using hd)
    simp only [prefixThrough,List.nil_append,calendarTail,List.append_nil] at htail
    unfold compiledCalendarProgram
    rw [hd,readoutExposure_append,readoutExposure_original_batch,zero_add,htail,
      dateExposure_selected_edges]
    unfold selectedDirectedExposure
    apply Finset.sum_congr rfl
    intro e _
    by_cases hex : e ∈ (commonRoutes N C H coin).edges i ∧ e ∉ (commonRoutes N C H coin).edges j
    · rw [if_pos hex,if_pos hex]
      congr 1
      apply activeDuration_full_dates
      · rw [← hd]; exact original_dates_strict N C
      · rw [← hd]; exact original_date_scheduled N C (N.graph.target e)
      · rw [← hd]; exact original_date_scheduled N C (N.graph.source e)
      · exact C.edge_older e
    · rw [if_neg hex,if_neg hex]

end DotG4.ActualSelectedPathExposure
