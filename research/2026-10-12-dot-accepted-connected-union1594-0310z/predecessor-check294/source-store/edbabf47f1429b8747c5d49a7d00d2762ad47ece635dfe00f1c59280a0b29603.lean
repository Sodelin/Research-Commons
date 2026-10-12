import G2LiteralMarkedClockTrace

/-!
First actual-law branches for the new marked trace renewal assembly.
Contributor: dot (OpenAI), 6 October 2026. New uncompiled development source.
No complete epoch, full-past or projectivity law is an assumption.
-/
namespace GProgram.G2.MarkedTraceRenewal
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceLiteralClockEndpoint
open UnifiedLean.Source.SourceRaceWinnerSelection
open UnifiedLean.Source.SourceMergerClockCatalogue
open GProgram.G2.LiteralMarkedClockTrace
open scoped Classical NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable

def NoMarkedEvent (N : RootedBinary V E X) {sample : Copy → X} (n : Nat)
    (z : Bool × ClockTrace N sample n) : Prop :=
  z.1 = true ∧ ∀ i, (z.2 i).1 = false

/-- The successful zero-event branch is exactly literal clock survival,
even on pathological vectors and at zero budget. Inactive padding is ignored. -/
theorem no_marked_event_iff (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (t : ℝ) (c : Choice N s → ℝ) :
    NoMarkedEvent N n (literalMarkedTrace N n t s c) ↔ ∀ p : Choice N s, t < c p := by
  cases n with
  | zero => simp [NoMarkedEvent,literalMarkedTrace,emptyTrace]
  | succ n =>
      by_cases hs : ∀ p : Choice N s, t < c p
      · simp [NoMarkedEvent,literalMarkedTrace,hs,emptyTrace]
      · simp only [literalMarkedTrace,if_neg hs]
        cases hw : selectedWinner c with
        | none => simp [NoMarkedEvent,hs]
        | some p =>
            by_cases hp : c p ≤ t
            · simp only [if_pos hp]
              constructor
              · intro h
                have hf := h.2 (0 : Fin (n+1))
                simp [prependTrace] at hf
              · exact False.elim ∘ hs
            · simp [hp,NoMarkedEvent,hs]

lemma no_marked_event_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) : MeasurableSet {z : Bool × ClockTrace N sample n | NoMarkedEvent N n z} := by
  have hs : MeasurableSet {z : Bool × ClockTrace N sample n | z.1 = true} :=
    measurableSet_eq_fun measurable_fst measurable_const
  have ha : MeasurableSet {z : Bool × ClockTrace N sample n | ∀ i, (z.2 i).1 = false} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_eq_fun
      (((measurable_pi_apply i).comp measurable_snd).fst) measurable_const)
  exact hs.inter ha

/-- The no-real-event mass of the actual trace law is the original exponential
product tail. This is one renewal branch, not the entire epoch distribution. -/
theorem actual_marked_no_event_mass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (t : ℝ≥0) :
    (actualMarkedTraceLaw N r n s (t : ℝ) {z | NoMarkedEvent N n z}).toReal =
      Real.exp (-(totalRate N r s*(t : ℝ))) := by
  rw [actualMarkedTraceLaw,Measure.map_apply (marked_trace_measurable N n s t)
    (no_marked_event_measurable N n)]
  have he : (literalMarkedTrace N n (t : ℝ) s) ⁻¹' {z | NoMarkedEvent N n z} =
      currentNoFirstMerger N s t := by
    ext c
    simp only [mem_preimage,mem_setOf_eq,no_marked_event_iff,currentNoFirstMerger,
      mem_pi,mem_univ,mem_Ioi,true_implies]
  rw [he]
  exact actual_current_clock_no_merger N r t s

/-- The trace's successful no-event statistic agrees with the corresponding
actual source-PMF diagonal, using the existing strict live-card descent proof. -/
theorem actual_marked_no_event_source_binding (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (t : ℝ≥0) :
    (actualMarkedTraceLaw N r n s (t : ℝ) {z | NoMarkedEvent N n z}).toReal =
      (UnifiedLean.Source.SourcePoissonKernel.sourceTimeKernel N r t s s).toReal := by
  rw [actual_marked_no_event_mass,actual_source_kernel_no_merger]

#print axioms no_marked_event_iff
#print axioms no_marked_event_measurable
#print axioms actual_marked_no_event_mass
#print axioms actual_marked_no_event_source_binding
open UnifiedLean.Source.SourceWinningClockReset
open UnifiedLean.Source.SourceDestinationClockReset
open UnifiedLean.Source.SourceExponentialRace

def firstJumpClockSet (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) (t : ℝ) : Set (Choice N s → ℝ) :=
  winningRegion p ∩ {c | c p ≤ t}

lemma first_jump_clock_set_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) (t : ℝ) :
    MeasurableSet (firstJumpClockSet N s p t) :=
  (measurable_winningRegion p).inter (measurableSet_le (measurable_pi_apply p) measurable_const)

noncomputable def firstJumpFuture (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (p : Choice N s) (t : ℝ)
    (z : ℝ × (Choice N (stepDestination N s (some p)) → ℝ)) :
    Bool × ClockTrace N sample (n+1) :=
  let w := literalMarkedTrace N n (t-z.1) (stepDestination N s (some p)) z.2
  (w.1,prependTrace N z.1 (stepDestination N s (some p)) w.2)

lemma first_jump_future_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (p : Choice N s) (t : ℝ) :
    Measurable (firstJumpFuture N n s p t) := by
  have hw : Measurable (fun z : ℝ × (Choice N (stepDestination N s (some p)) → ℝ) =>
      literalMarkedTrace N n (t-z.1) (stepDestination N s (some p)) z.2) :=
    (marked_trace_joint_measurable N n (stepDestination N s (some p))).comp
      ((measurable_const.sub measurable_fst).prodMk measurable_snd)
  apply hw.fst.prodMk
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_const.prodMk (measurable_fst.prodMk measurable_const)
  · exact (((measurable_pi_apply j).comp hw.snd).fst).prodMk
      ((measurable_fst.add (((measurable_pi_apply j).comp hw.snd).snd.fst)).prodMk
        (((measurable_pi_apply j).comp hw.snd).snd.snd))

theorem actual_trace_first_jump_eq (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (p : Choice N s) (t : ℝ) (c : Choice N s → ℝ)
    (hc : c ∈ firstJumpClockSet N s p t) :
    literalMarkedTrace N (n+1) t s c =
      firstJumpFuture N n s p t (destinationResetMap N s p c) := by
  have hw : selectedWinner c = some p := (selectedWinner_eq_some_iff c p).mpr hc.1
  have hcpt : c p ≤ t := hc.2
  have hs : ¬ ∀ q : Choice N s, t < c q := fun h => (not_lt_of_ge hcpt) (h p)
  simp only [literalMarkedTrace,if_neg hs,hw,if_pos hcpt]
  rfl

/-- One complete first-event branch of the ACTUAL trace law. Winner time is
restricted to the observation horizon before the exact merger is prepended.
This does not yet sum branches or assert the full epoch/source-PMF law. -/
theorem actual_marked_first_jump_branch (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (p : Choice N s) (t : ℝ) :
    ((currentPairClockMeasure N r s).restrict (firstJumpClockSet N s p t)).map
      (literalMarkedTrace N (n+1) t s) =
    (((ENNReal.ofReal (choiceRate N r s p/totalRate N r s) • expMeasure (totalRate N r s)).restrict
      (Iic t)).prod (currentPairClockMeasure N r (stepDestination N s (some p)))).map
        (firstJumpFuture N n s p t) := by
  letI := isProbabilityMeasure_expMeasure
    (UnifiedLean.Source.SourceFirstMarkDistribution.current_pair_total_positive N r s p)
  letI := Measure.smul_finite (expMeasure (totalRate N r s))
    (show ENNReal.ofReal (choiceRate N r s p/totalRate N r s) ≠ ∞ from ENNReal.ofReal_ne_top)
  letI : ∀ q : Choice N (stepDestination N s (some p)),
      IsProbabilityMeasure (expMeasure (choiceRate N r (stepDestination N s (some p)) q)) :=
    fun q => isProbabilityMeasure_expMeasure (div_pos (pairRate_pos r q.1) (by norm_num))
  letI : IsProbabilityMeasure (currentPairClockMeasure N r (stepDestination N s (some p))) := by
    unfold currentPairClockMeasure
    infer_instance
  have hm : Measurable (destinationResetMap N s p) := by
    unfold destinationResetMap
    fun_prop
  have hp : (destinationResetMap N s p) ⁻¹' (Iic t ×ˢ univ) = {c | c p ≤ t} := by
    ext c
    simp [destinationResetMap]
  have h := congrArg (fun mu : Measure (ℝ × (Choice N (stepDestination N s (some p)) → ℝ)) =>
      mu.restrict (Iic t ×ˢ univ)) (original_source_destination_clock_reset N r s p)
  rw [Measure.restrict_map hm (measurableSet_Iic.prod MeasurableSet.univ),hp,
    Measure.restrict_restrict (measurableSet_le (measurable_pi_apply p) measurable_const),
    ← Measure.restrict_prod_eq_prod_univ] at h
  have hi : {c : Choice N s → ℝ | c p ≤ t} ∩ winningRegion p = firstJumpClockSet N s p t :=
    inter_comm _ _
  rw [hi] at h
  calc
    _ = ((currentPairClockMeasure N r s).restrict (firstJumpClockSet N s p t)).map
        (firstJumpFuture N n s p t ∘ destinationResetMap N s p) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem (first_jump_clock_set_measurable N s p t)] with c hc
      exact actual_trace_first_jump_eq N n s p t c hc
    _ = (((currentPairClockMeasure N r s).restrict (firstJumpClockSet N s p t)).map
        (destinationResetMap N s p)).map (firstJumpFuture N n s p t) :=
      (Measure.map_map (first_jump_future_measurable N n s p t) hm).symm
    _ = _ := congrArg (fun mu => mu.map (firstJumpFuture N n s p t)) h

#print axioms first_jump_clock_set_measurable
#print axioms first_jump_future_measurable
#print axioms actual_trace_first_jump_eq
#print axioms actual_marked_first_jump_branch

open scoped BigOperators

def initialClockBranch (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (t : ℝ≥0) : Option (Choice N s) → Set (Choice N s → ℝ)
  | none => currentNoFirstMerger N s t
  | some p => firstJumpClockSet N s p t

lemma mem_no_first_merger_iff (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (t : ℝ≥0) (c : Choice N s → ℝ) :
    c ∈ currentNoFirstMerger N s t ↔ ∀ p, (t : ℝ) < c p := by
  simp [currentNoFirstMerger]

lemma initial_clock_branch_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (t : ℝ≥0) (b : Option (Choice N s)) :
    MeasurableSet (initialClockBranch N s t b) := by
  cases b with
  | none => exact MeasurableSet.univ_pi (fun _ => measurableSet_Ioi)
  | some p => exact first_jump_clock_set_measurable N s p t

lemma initial_clock_branches_disjoint (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (t : ℝ≥0) :
    _root_.Pairwise (fun a b : Option (Choice N s) =>
      Disjoint (initialClockBranch N s t a) (initialClockBranch N s t b)) := by
  intro a b hab
  apply Set.disjoint_left.mpr
  intro c ha hb
  cases a with
  | none =>
      cases b with
      | none => exact hab rfl
      | some p =>
          have hs := (mem_no_first_merger_iff N s t c).mp ha
          have hp : c p ≤ (t : ℝ) := hb.2
          exact (not_lt_of_ge hp) (hs p)
  | some p =>
      cases b with
      | none =>
          have hs := (mem_no_first_merger_iff N s t c).mp hb
          have hp : c p ≤ (t : ℝ) := ha.2
          exact (not_lt_of_ge hp) (hs p)
      | some q => exact hab (congrArg some (winning_coordinate_unique c ha.1 hb.1))

/-- Actual product clocks almost surely enter exactly one first-event branch.
The coverage proof uses proved regularity, not a postulated path law. -/
theorem actual_clock_branch_cover_ae (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0) :
    ∀ᵐ c ∂currentPairClockMeasure N r s,
      c ∈ ⋃ b : Option (Choice N s), initialClockBranch N s t b := by
  filter_upwards [actual_current_clock_regular_ae N r s] with c hc
  by_cases hs : ∀ p : Choice N s, (t : ℝ) < c p
  · exact Set.mem_iUnion.mpr ⟨none,(mem_no_first_merger_iff N s t c).mpr hs⟩
  · obtain ⟨q,hq⟩ := not_forall.mp hs
    letI : Nonempty (Choice N s) := ⟨q⟩
    obtain ⟨p,hp⟩ := regular_winner_exists c hc
    have hmin : c p ≤ c q := by
      by_cases he : q=p
      · simp [he]
      · exact ((selectedWinner_eq_some_iff c p).mp hp).2 ⟨q,he⟩ |>.le
    exact Set.mem_iUnion.mpr ⟨some p,
      ⟨(selectedWinner_eq_some_iff c p).mp hp,le_trans hmin (le_of_not_gt hq)⟩⟩

theorem actual_clock_branch_partition (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (t : ℝ≥0) :
    currentPairClockMeasure N r s =
      ∑ b : Option (Choice N s), (currentPairClockMeasure N r s).restrict (initialClockBranch N s t b) := by
  have h := Measure.restrict_eq_self_of_ae_mem (actual_clock_branch_cover_ae N r s t)
  rw [Measure.restrict_iUnion (initial_clock_branches_disjoint N s t)
    (initial_clock_branch_measurable N s t),Measure.sum_fintype] at h
  exact h.symm

theorem actual_no_jump_trace_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (t : ℝ≥0) :
    ((currentPairClockMeasure N r s).restrict (currentNoFirstMerger N s t)).map
      (literalMarkedTrace N n (t : ℝ) s) =
      ENNReal.ofReal (Real.exp (-(totalRate N r s*(t : ℝ)))) •
        Measure.dirac (true,emptyTrace N n s) := by
  letI : ∀ p : Choice N s, IsProbabilityMeasure (expMeasure (choiceRate N r s p)) :=
    fun p => isProbabilityMeasure_expMeasure (div_pos (pairRate_pos r p.1) (by norm_num))
  letI : IsProbabilityMeasure (currentPairClockMeasure N r s) := by
    unfold currentPairClockMeasure
    infer_instance
  have hs : MeasurableSet (currentNoFirstMerger N s t) :=
    MeasurableSet.univ_pi (fun _ => measurableSet_Ioi)
  have hm : currentPairClockMeasure N r s (currentNoFirstMerger N s t) =
      ENNReal.ofReal (Real.exp (-(totalRate N r s*(t : ℝ)))) := by
    rw [← actual_current_clock_no_merger N r t s,ENNReal.ofReal_toReal (measure_ne_top _ _)]
  calc
    _ = ((currentPairClockMeasure N r s).restrict (currentNoFirstMerger N s t)).map
        (fun _ => (true,emptyTrace N n s)) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem hs] with c hc
      have hh := (mem_no_first_merger_iff N s t c).mp hc
      cases n <;> simp [literalMarkedTrace,hh]
    _ = _ := by rw [Measure.map_const,Measure.restrict_apply MeasurableSet.univ,univ_inter,hm]

/-- Full finite marked-trace first-event renewal. The no-jump atom and every
winner-before-horizon branch are derived from the original clock space and
actual residual reset; the entire recursive future stays inside the map.
Identification with the old source-PMF kernel is a separate next theorem. -/
theorem actual_marked_trace_first_jump_renewal (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (t : ℝ≥0) :
    actualMarkedTraceLaw N r (n+1) s (t : ℝ) =
      ENNReal.ofReal (Real.exp (-(totalRate N r s*(t : ℝ)))) •
        Measure.dirac (true,emptyTrace N (n+1) s) +
      ∑ p : Choice N s,
        (((ENNReal.ofReal (choiceRate N r s p/totalRate N r s) • expMeasure (totalRate N r s)).restrict
          (Iic (t : ℝ))).prod (currentPairClockMeasure N r (stepDestination N s (some p)))).map
            (firstJumpFuture N n s p t) := by
  rw [actualMarkedTraceLaw,actual_clock_branch_partition N r s t,
    Measure.map_finset_sum' (marked_trace_measurable N (n+1) s t).aemeasurable,Fintype.sum_option]
  simp only [initialClockBranch]
  rw [actual_no_jump_trace_law N r (n+1) s t]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  exact actual_marked_first_jump_branch N r n s p t

#print axioms mem_no_first_merger_iff
#print axioms initial_clock_branch_measurable
#print axioms initial_clock_branches_disjoint
#print axioms actual_clock_branch_cover_ae
#print axioms actual_clock_branch_partition
#print axioms actual_no_jump_trace_law
#print axioms actual_marked_trace_first_jump_renewal

end GProgram.G2.MarkedTraceRenewal
