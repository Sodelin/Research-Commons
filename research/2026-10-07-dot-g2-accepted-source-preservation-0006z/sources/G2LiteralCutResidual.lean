import G2LiteralEpochLaw

/-!
New literal retained-clock compiler at an observation cut.
Contributor: dot (OpenAI), 6 October 2026. Development source.
The output retains the same original coordinates after the elapsed duration;
no conditional independence or full-past factorization is assumed here.
-/
namespace GProgram.G2.LiteralCutResidual
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceMergerClockCatalogue
open UnifiedLean.Source.SourceRaceWinnerSelection
open UnifiedLean.Source.SourceLiteralClockEndpoint
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.LiteralEpochLaw
open scoped Classical NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable
  GProgram.G2.LiteralMarkedClockTrace.choiceOptionMeasurable

/-- A measurable sum of the failure point and all actual terminal clock
fibres. The uncountable clock fibres keep their product Borel sigma algebra. -/
abbrev CutResidual (N : RootedBinary V E X) (sample : Copy → X) :=
  Unit ⊕ (Σ d : Code N sample, Choice N d → ℝ)

def encodeResidual (N : RootedBinary V E X) {sample : Copy → X}
    (d : Code N sample) (c : Choice N d → ℝ) : CutResidual N sample := .inr ⟨d,c⟩

def cutEndpoint (N : RootedBinary V E X) {sample : Copy → X} :
    CutResidual N sample → Option (Code N sample) :=
  Sum.elim (fun _ => none) (fun z => some z.1)

lemma encode_residual_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (d : Code N sample) : Measurable (encodeResidual N d) := by
  have hm : Measurable (fun c : Choice N d → ℝ =>
      (⟨d,c⟩ : Σ z : Code N sample, Choice N z → ℝ)) := by
    intro A hA
    exact (MeasurableSpace.measurableSet_iInf.mp hA) d
  exact measurable_inr.comp hm

lemma cut_endpoint_measurable (N : RootedBinary V E X) {sample : Copy → X} :
    Measurable (cutEndpoint N (sample := sample)) := by
  have hm : Measurable (fun z : (Σ d : Code N sample, Choice N d → ℝ) =>
      (some z.1 : Option (Code N sample))) := by
    intro A _
    apply MeasurableSpace.measurableSet_iInf.mpr
    intro d
    change MeasurableSet {c : Choice N d → ℝ | some d ∈ A}
    by_cases h : some d ∈ A <;> simp [h]
  exact measurable_const.sumElim hm

noncomputable def literalCutResidual (N : RootedBinary V E X) {sample : Copy → X} :
    Nat → ℝ → (s : Code N sample) → (Choice N s → ℝ) → CutResidual N sample
  | 0,t,s,c => if ∀ p : Choice N s, t < c p then
      encodeResidual N s (fun p => c p-t) else .inl ()
  | n+1,t,s,c => if ∀ p : Choice N s, t < c p then
      encodeResidual N s (fun p => c p-t) else
      match selectedWinner c with
      | none => .inl ()
      | some p => if c p ≤ t then
          literalCutResidual N n (t-c p) (stepDestination N s (some p))
            (fun q => c (destinationClockEmbedding N s p q).val-c p)
        else .inl ()

/-- The residual compiler's terminal code is exactly the unchanged literal
endpoint, including failures and exhausted budgets. -/
theorem cut_endpoint_eq_literal (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (t : ℝ) (c : Choice N s → ℝ) :
    cutEndpoint N (literalCutResidual N n t s c) = literalClockEndpoint N n t s c := by
  induction n generalizing s t with
  | zero =>
      by_cases h : ∀ p : Choice N s, t < c p <;>
        simp [literalCutResidual,literalClockEndpoint,cutEndpoint,encodeResidual,h]
  | succ n ih =>
      by_cases h : ∀ p : Choice N s, t < c p
      · simp [literalCutResidual,literalClockEndpoint,cutEndpoint,encodeResidual,h]
      · simp only [literalCutResidual,literalClockEndpoint,if_neg h]
        cases hw : selectedWinner c with
        | none => rfl
        | some p =>
            simp only
            by_cases hp : c p ≤ t
            · simp only [if_pos hp]
              exact ih (stepDestination N s (some p)) (t-c p)
                (fun q => c (destinationClockEmbedding N s p q).val-c p)
            · simp [hp,cutEndpoint]

/-- Joint horizon/clock measurability of the retained original residuals. -/
theorem literal_cut_joint_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) :
    Measurable (fun z : ℝ × (Choice N s → ℝ) => literalCutResidual N n z.1 s z.2) := by
  induction n generalizing s with
  | zero =>
      have hm : Measurable (fun z : ℝ × (Choice N s → ℝ) =>
          encodeResidual N s (fun p => z.2 p-z.1)) :=
        (encode_residual_measurable N s).comp (by fun_prop)
      exact Measurable.ite (measurable_no_jump N s) hm measurable_const
  | succ n ih =>
      let dispatch : (ℝ × (Choice N s → ℝ)) × Option (Choice N s) → CutResidual N sample :=
        fun z => match z.2 with
        | none => .inl ()
        | some p => if z.1.2 p ≤ z.1.1 then
            literalCutResidual N n (z.1.1-z.1.2 p) (stepDestination N s (some p))
              (fun q => z.1.2 (destinationClockEmbedding N s p q).val-z.1.2 p)
          else .inl ()
      have hd : Measurable dispatch := by
        apply measurable_from_prod_countable_left
        intro p
        cases p with
        | none => exact measurable_const
        | some p =>
            change Measurable (fun z : ℝ × (Choice N s → ℝ) =>
              if z.2 p ≤ z.1 then literalCutResidual N n (z.1-z.2 p) (stepDestination N s (some p))
                (fun q => z.2 (destinationClockEmbedding N s p q).val-z.2 p) else .inl ())
            apply Measurable.ite
            · exact measurableSet_le ((measurable_pi_apply p).comp measurable_snd) measurable_fst
            · have ht : Measurable (fun z : ℝ × (Choice N s → ℝ) => z.1-z.2 p) :=
                measurable_fst.sub ((measurable_pi_apply p).comp measurable_snd)
              have hc : Measurable (fun z : ℝ × (Choice N s → ℝ) =>
                  fun q : Choice N (stepDestination N s (some p)) =>
                    z.2 (destinationClockEmbedding N s p q).val-z.2 p) := by
                apply measurable_pi_lambda
                intro q
                exact ((measurable_pi_apply (destinationClockEmbedding N s p q).val).comp measurable_snd).sub
                  ((measurable_pi_apply p).comp measurable_snd)
              exact (ih (stepDestination N s (some p))).comp (ht.prodMk hc)
            · exact measurable_const
      have hselect : Measurable (fun z : ℝ × (Choice N s → ℝ) => (z,selectedWinner z.2)) :=
        measurable_id.prodMk (selectedWinner_measurable.comp measurable_snd)
      have hm : Measurable (fun z : ℝ × (Choice N s → ℝ) =>
          encodeResidual N s (fun p => z.2 p-z.1)) :=
        (encode_residual_measurable N s).comp (by fun_prop)
      exact Measurable.ite (measurable_no_jump N s) hm (hd.comp hselect)

lemma literal_cut_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (t : ℝ) : Measurable (literalCutResidual N n t s) :=
  (literal_cut_joint_measurable N n s).comp (measurable_const.prodMk measurable_id)

#print axioms encode_residual_measurable
#print axioms cut_endpoint_measurable
#print axioms cut_endpoint_eq_literal
#print axioms literal_cut_joint_measurable
#print axioms literal_cut_measurable

/-- One exact joint history/residual branch: when no original clock rings
before the cut, the history is empty and the original residual product is
retained with its unnormalized survival weight. -/
theorem actual_no_event_joint_residual (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (t : ℝ≥0) :
    ((currentPairClockMeasure N r s).restrict (currentNoFirstMerger N s t)).map
      (fun c => (literalMarkedTrace N n (t : ℝ) s c,literalCutResidual N n (t : ℝ) s c)) =
      ENNReal.ofReal (Real.exp (-(totalRate N r s*(t : ℝ)))) •
        (currentPairClockMeasure N r s).map
          (fun c => ((true,emptyTrace N n s),encodeResidual N s c)) := by
  let F : (Choice N s → ℝ) → (Bool × ClockTrace N sample n) × CutResidual N sample :=
    fun c => ((true,emptyTrace N n s),encodeResidual N s c)
  let shift : (Choice N s → ℝ) → (Choice N s → ℝ) := fun c p => c p-(t : ℝ)
  have hF : Measurable F := measurable_const.prodMk (encode_residual_measurable N s)
  have hs : Measurable shift := by fun_prop
  have hreset : ((currentPairClockMeasure N r s).restrict (currentNoFirstMerger N s t)).map shift =
      ENNReal.ofReal (Real.exp (-(totalRate N r s*(t : ℝ)))) • currentPairClockMeasure N r s :=
    UnifiedLean.Source.SourceExponentialResiduals.actual_exponential_product_residual_measure
      (choiceRate N r s) (fun p => div_pos (pairRate_pos r p.1) (by norm_num)) t
  calc
    _ = ((currentPairClockMeasure N r s).restrict (currentNoFirstMerger N s t)).map (F ∘ shift) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem
        (MeasurableSet.univ_pi (fun _ => measurableSet_Ioi) : MeasurableSet (currentNoFirstMerger N s t))] with c hc
      have hstop : ∀ p : Choice N s, (t : ℝ) < c p := by simpa [currentNoFirstMerger] using hc
      cases n <;> simp [literalMarkedTrace,literalCutResidual,hstop,F,shift]
    _ = (((currentPairClockMeasure N r s).restrict (currentNoFirstMerger N s t)).map shift).map F :=
      (Measure.map_map hF hs).symm
    _ = _ := by rw [hreset,Measure.map_smul]

#print axioms actual_no_event_joint_residual

open GProgram.G2.MarkedTraceRenewal
open UnifiedLean.Source.SourceDestinationClockReset
open UnifiedLean.Source.SourceWinningClockReset
open scoped BigOperators

noncomputable def firstJumpJointFuture (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (p : Choice N s) (t : ℝ)
    (z : ℝ × (Choice N (stepDestination N s (some p)) → ℝ)) :
    (Bool × ClockTrace N sample (n+1)) × CutResidual N sample :=
  (firstJumpFuture N n s p t z,
    literalCutResidual N n (t-z.1) (stepDestination N s (some p)) z.2)

lemma first_jump_joint_future_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (p : Choice N s) (t : ℝ) :
    Measurable (firstJumpJointFuture N n s p t) :=
  (first_jump_future_measurable N n s p t).prodMk
    ((literal_cut_joint_measurable N n (stepDestination N s (some p))).comp
      ((measurable_const.sub measurable_fst).prodMk measurable_snd))

theorem actual_joint_first_jump_eq (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (p : Choice N s) (t : ℝ) (c : Choice N s → ℝ)
    (hc : c ∈ firstJumpClockSet N s p t) :
    (literalMarkedTrace N (n+1) t s c,literalCutResidual N (n+1) t s c) =
      firstJumpJointFuture N n s p t (destinationResetMap N s p c) := by
  apply Prod.ext
  · exact actual_trace_first_jump_eq N n s p t c hc
  · have hw : selectedWinner c = some p := (selectedWinner_eq_some_iff c p).mpr hc.1
    have hp : c p ≤ t := hc.2
    have hs : ¬ ∀ q : Choice N s, t < c q := fun h => (not_lt_of_ge hp) (h p)
    simp [literalCutResidual,hs,hw,hp,firstJumpJointFuture,destinationResetMap]

/-- The original winning-region reset transports the complete history and
all retained residual clocks together on one first-event branch. -/
theorem actual_joint_first_jump_branch (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (p : Choice N s) (t : ℝ) :
    ((currentPairClockMeasure N r s).restrict (firstJumpClockSet N s p t)).map
      (fun c => (literalMarkedTrace N (n+1) t s c,literalCutResidual N (n+1) t s c)) =
    (((ENNReal.ofReal (choiceRate N r s p/totalRate N r s) • expMeasure (totalRate N r s)).restrict
      (Iic t)).prod (currentPairClockMeasure N r (stepDestination N s (some p)))).map
        (firstJumpJointFuture N n s p t) := by
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
        (firstJumpJointFuture N n s p t ∘ destinationResetMap N s p) := by
      apply Measure.map_congr
      filter_upwards [ae_restrict_mem (first_jump_clock_set_measurable N s p t)] with c hc
      exact actual_joint_first_jump_eq N n s p t c hc
    _ = (((currentPairClockMeasure N r s).restrict (firstJumpClockSet N s p t)).map
        (destinationResetMap N s p)).map (firstJumpJointFuture N n s p t) :=
      (Measure.map_map (first_jump_joint_future_measurable N n s p t) hm).symm
    _ = _ := congrArg (fun mu => mu.map (firstJumpJointFuture N n s p t)) h

noncomputable def actualCutJointLaw (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (t : ℝ) :
    Measure ((Bool × ClockTrace N sample n) × CutResidual N sample) :=
  (currentPairClockMeasure N r s).map
    (fun c => (literalMarkedTrace N n t s c,literalCutResidual N n t s c))

/-- Exact finite-budget renewal of the joint history/retained-clock law.
This still does not assume or assert the full terminal-fibre factorization. -/
theorem actual_cut_joint_first_jump_renewal (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (t : ℝ≥0) :
    actualCutJointLaw N r (n+1) s (t : ℝ) =
      ENNReal.ofReal (Real.exp (-(totalRate N r s*(t : ℝ)))) •
        (currentPairClockMeasure N r s).map
          (fun c => ((true,emptyTrace N (n+1) s),encodeResidual N s c)) +
      ∑ p : Choice N s,
        (((ENNReal.ofReal (choiceRate N r s p/totalRate N r s) • expMeasure (totalRate N r s)).restrict
          (Iic (t : ℝ))).prod (currentPairClockMeasure N r (stepDestination N s (some p)))).map
            (firstJumpJointFuture N n s p t) := by
  conv_lhs =>
    rw [actualCutJointLaw,actual_clock_branch_partition N r s t,
      Measure.map_finset_sum' ((marked_trace_measurable N (n+1) s t).prodMk
        (literal_cut_measurable N (n+1) s t)).aemeasurable,Fintype.sum_option]
  simp only [initialClockBranch]
  rw [actual_no_event_joint_residual N r (n+1) s t]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  exact actual_joint_first_jump_branch N r n s p t

#print axioms first_jump_joint_future_measurable
#print axioms actual_joint_first_jump_eq
#print axioms actual_joint_first_jump_branch
#print axioms actual_cut_joint_first_jump_renewal

end GProgram.G2.LiteralCutResidual
