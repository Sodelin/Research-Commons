import G2LiteralCutResidual

/-!
Explicit retained-clock attachment functional and ordinary measure algebra.
Contributor: dot (OpenAI), 6 October 2026. Development source.
Defining this functional does not assert that it is the actual joint law;
that equality must be proved separately from the original clock renewal.
-/
namespace GProgram.G2.HistoryResidualAttachment
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.LiteralEpochLaw
open GProgram.G2.LiteralCutResidual
open scoped Classical NNReal ENNReal BigOperators

section MeasureTools
variable {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]

theorem map_bind_measurable (μ : Measure α) (κ : α → Measure β) (f : β → γ)
    (hκ : Measurable κ) (hf : Measurable f) :
    (μ.bind κ).map f = μ.bind (fun x => (κ x).map f) := by
  rw [Measure.bind,← Measure.join_map_map hf,
    Measure.map_map (Measure.measurable_map f hf) hκ]
  rfl

theorem bind_map_measurable (μ : Measure α) (f : α → β) (κ : β → Measure γ)
    (hf : Measurable f) (hκ : Measurable κ) :
    (μ.map f).bind κ = μ.bind (fun x => κ (f x)) := by
  rw [Measure.bind,Measure.map_map hκ hf]
  rfl

theorem parameterized_map_measurable (μ : Measure β) [SFinite μ]
    (f : α × β → γ) (hf : Measurable f) :
    Measurable (fun a => μ.map (fun b => f (a,b))) := by
  have h : Measurable (fun a : α => (μ.map (Prod.mk a)).map f) :=
    (Measure.measurable_map f hf).comp Measurable.map_prodMk_left
  have he : (fun a : α => (μ.map (Prod.mk a)).map f) =
      (fun a => μ.map (fun b => f (a,b))) := by
    funext a
    exact Measure.map_map hf measurable_prodMk_left
  rwa [he] at h

theorem product_map_eq_bind (ν : Measure α) (μ : Measure β) [SFinite μ]
    (f : α × β → γ) (hf : Measurable f) :
    (ν.prod μ).map f = ν.bind (fun a => μ.map (fun b => f (a,b))) := by
  rw [Measure.prod,map_bind_measurable _ _ _ Measurable.map_prodMk_left hf]
  apply congrArg (Measure.bind ν)
  funext a
  exact Measure.map_map hf measurable_prodMk_left

theorem bind_add_measurable (μ ν : Measure α) (κ : α → Measure β) (hκ : Measurable κ) :
    (μ+ν).bind κ = μ.bind κ + ν.bind κ := by
  ext A hA
  simp only [Measure.bind_apply hA hκ.aemeasurable,Measure.add_apply,lintegral_add_measure]

theorem bind_finset_sum_measurable {ι : Type*} (s : Finset ι)
    (μ : ι → Measure α) (κ : α → Measure β) (hκ : Measurable κ) :
    (∑ i ∈ s, μ i).bind κ = ∑ i ∈ s, (μ i).bind κ := by
  ext A hA
  simp only [Measure.bind_apply hA hκ.aemeasurable,Measure.finsetSum_apply,lintegral_finsetSum_measure]
end MeasureTools

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable

local instance current_clock_probability (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) : IsProbabilityMeasure (currentPairClockMeasure N r s) := by
  letI : ∀ p : Choice N s, IsProbabilityMeasure (expMeasure (choiceRate N r s p)) :=
    fun p => isProbabilityMeasure_expMeasure (div_pos (pairRate_pos r p.1) (by norm_num))
  unfold currentPairClockMeasure
  infer_instance

/-- Explicit original-clock attachment to a supplied history. A failed
history is assigned the zero measure. This definition is not a law premise. -/
noncomputable def historyResidualKernel (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (h : Bool × ClockTrace N sample n) :
    Measure ((Bool × ClockTrace N sample n) × CutResidual N sample) :=
  match decodedEndpoint N n s h with
  | none => 0
  | some d => (currentPairClockMeasure N r d).map (fun c => (h,encodeResidual N d c))

theorem history_residual_kernel_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) :
    Measurable (historyResidualKernel N r n s) := by
  let dispatch : (Bool × ClockTrace N sample n) × Option (Code N sample) →
      Measure ((Bool × ClockTrace N sample n) × CutResidual N sample) := fun z =>
    match z.2 with
    | none => 0
    | some d => (currentPairClockMeasure N r d).map (fun c => (z.1,encodeResidual N d c))
  have hd : Measurable dispatch := by
    apply measurable_from_prod_countable_left
    intro o
    cases o with
    | none => exact measurable_const
    | some d =>
        exact parameterized_map_measurable (currentPairClockMeasure N r d)
          (fun z => (z.1,encodeResidual N d z.2))
          (measurable_fst.prodMk ((encode_residual_measurable N d).comp measurable_snd))
  exact hd.comp (measurable_id.prodMk (decoded_endpoint_measurable N n s))

noncomputable def attachResiduals (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample)
    (ν : Measure (Bool × ClockTrace N sample n)) :
    Measure ((Bool × ClockTrace N sample n) × CutResidual N sample) :=
  ν.bind (historyResidualKernel N r n s)

def prependHistory (N : RootedBinary V E X) {sample : Copy → X} (n : Nat)
    (d : Code N sample) (u : ℝ) (h : Bool × ClockTrace N sample n) : Bool × ClockTrace N sample (n+1) :=
  (h.1,prependTrace N u d h.2)

lemma prepend_history_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (d : Code N sample) (u : ℝ) : Measurable (prependHistory N n d u) := by
  apply measurable_fst.prodMk
  apply measurable_pi_lambda
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact measurable_const
  · exact (((measurable_pi_apply j).comp measurable_snd).fst).prodMk
      ((measurable_const.add (((measurable_pi_apply j).comp measurable_snd).snd.fst)).prodMk
        (((measurable_pi_apply j).comp measurable_snd).snd.snd))

lemma decoded_prepend_history (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s d : Code N sample) (u : ℝ) (h : Bool × ClockTrace N sample n) :
    decodedEndpoint N (n+1) s (prependHistory N n d u h) = decodedEndpoint N n d h := by
  simp [prependHistory,decodedEndpoint,prepend_trace_endpoint]

/-- Attaching the same original residual law commutes with an actual
history prepend because its terminal code is deterministically unchanged. -/
theorem residual_kernel_prepend (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s d : Code N sample) (u : ℝ)
    (h : Bool × ClockTrace N sample n) :
    historyResidualKernel N r (n+1) s (prependHistory N n d u h) =
      (historyResidualKernel N r n d h).map
        (Prod.map (prependHistory N n d u) (id : CutResidual N sample → CutResidual N sample)) := by
  simp only [historyResidualKernel,decoded_prepend_history]
  cases he : decodedEndpoint N n d h with
  | none => simp
  | some e =>
      simp only
      rw [Measure.map_map ((prepend_history_measurable N n d u).prodMap measurable_id)
        (measurable_const.prodMk (encode_residual_measurable N e))]
      rfl

theorem attach_residuals_prepend (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s d : Code N sample) (u : ℝ)
    (ν : Measure (Bool × ClockTrace N sample n)) :
    attachResiduals N r (n+1) s (ν.map (prependHistory N n d u)) =
      (attachResiduals N r n d ν).map
        (Prod.map (prependHistory N n d u) (id : CutResidual N sample → CutResidual N sample)) := by
  rw [attachResiduals,bind_map_measurable _ _ _ (prepend_history_measurable N n d u)
    (history_residual_kernel_measurable N r (n+1) s),attachResiduals,
    map_bind_measurable _ _ _ (history_residual_kernel_measurable N r n d)
      ((prepend_history_measurable N n d u).prodMap measurable_id)]
  apply Measure.bind_congr_right
  exact Filter.Eventually.of_forall (fun h => residual_kernel_prepend N r n s d u h)

#print axioms map_bind_measurable
#print axioms bind_map_measurable
#print axioms parameterized_map_measurable
#print axioms product_map_eq_bind
#print axioms bind_add_measurable
#print axioms bind_finset_sum_measurable
#print axioms history_residual_kernel_measurable
#print axioms prepend_history_measurable
#print axioms decoded_prepend_history
#print axioms residual_kernel_prepend
#print axioms attach_residuals_prepend

open UnifiedLean.Source.SourceFiniteJumpExpansion
open GProgram.G2.MarkedTraceRenewal

theorem attach_residuals_add (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample)
    (μ ν : Measure (Bool × ClockTrace N sample n)) :
    attachResiduals N r n s (μ+ν) = attachResiduals N r n s μ + attachResiduals N r n s ν :=
  bind_add_measurable μ ν _ (history_residual_kernel_measurable N r n s)

theorem attach_residuals_smul (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (a : ℝ≥0∞)
    (ν : Measure (Bool × ClockTrace N sample n)) :
    attachResiduals N r n s (a • ν) = a • attachResiduals N r n s ν :=
  Measure.bind_smul a ν _

theorem attach_residuals_finset_sum (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) {ι : Type*} (I : Finset ι)
    (ν : ι → Measure (Bool × ClockTrace N sample n)) :
    attachResiduals N r n s (∑ i ∈ I, ν i) = ∑ i ∈ I, attachResiduals N r n s (ν i) :=
  bind_finset_sum_measurable I ν _ (history_residual_kernel_measurable N r n s)

theorem attach_residuals_bind (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample)
    {α : Type*} [MeasurableSpace α] (ν : Measure α)
    (κ : α → Measure (Bool × ClockTrace N sample n)) (hκ : Measurable κ) :
    attachResiduals N r n s (ν.bind κ) = ν.bind (fun u => attachResiduals N r n s (κ u)) :=
  Measure.bind_bind hκ.aemeasurable (history_residual_kernel_measurable N r n s).aemeasurable

theorem attach_empty_history (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) :
    attachResiduals N r n s (Measure.dirac (true,emptyTrace N n s)) =
      (currentPairClockMeasure N r s).map (fun c => ((true,emptyTrace N n s),encodeResidual N s c)) := by
  rw [attachResiduals,Measure.dirac_bind (history_residual_kernel_measurable N r n s)]
  simp [historyResidualKernel,decodedEndpoint]

/-- Candidate full-past theorem: the complete unconditioned actual history
and retained-clock law equals the explicit original residual attachment.
The factorization is proved by actual-clock recursion, never assumed. -/
theorem actual_full_past_residual_factorization (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (t : ℝ≥0)
    (hn : liveCard s ≤ n) :
    actualCutJointLaw N r n s (t : ℝ) =
      attachResiduals N r n s (actualMarkedTraceLaw N r n s (t : ℝ)) := by
  induction n generalizing s t with
  | zero =>
      letI := choice_empty_of_zero_live N s (by omega)
      have hz : totalRate N r s = 0 := by simp [totalRate]
      have hs : currentNoFirstMerger N s t = univ := by
        ext c
        simp [currentNoFirstMerger]
      have hj := actual_no_event_joint_residual N r 0 s t
      have hh := actual_no_jump_trace_law N r 0 s t
      rw [hs,Measure.restrict_univ,hz,zero_mul,neg_zero,Real.exp_zero,ENNReal.ofReal_one,one_smul] at hj hh
      change actualCutJointLaw N r 0 s t = attachResiduals N r 0 s _
      have htrace : actualMarkedTraceLaw N r 0 s t = Measure.dirac (true,emptyTrace N 0 s) := hh
      rw [htrace,attach_empty_history]
      exact hj
  | succ n ih =>
      have hbranch (p : Choice N s) :
          (((ENNReal.ofReal (choiceRate N r s p/totalRate N r s) • expMeasure (totalRate N r s)).restrict
            (Iic (t : ℝ))).prod (currentPairClockMeasure N r (stepDestination N s (some p)))).map
              (firstJumpJointFuture N n s p t) =
          attachResiduals N r (n+1) s
            ((((ENNReal.ofReal (choiceRate N r s p/totalRate N r s) • expMeasure (totalRate N r s)).restrict
              (Iic (t : ℝ))).prod (currentPairClockMeasure N r (stepDestination N s (some p)))).map
                (firstJumpFuture N n s p t)) := by
        let e := stepDestination N s (some p)
        let ν := (ENNReal.ofReal (choiceRate N r s p/totalRate N r s) • expMeasure (totalRate N r s)).restrict (Iic (t : ℝ))
        let κH (u : ℝ) := (currentPairClockMeasure N r e).map (fun c => firstJumpFuture N n s p t (u,c))
        let κJ (u : ℝ) := (currentPairClockMeasure N r e).map (fun c => firstJumpJointFuture N n s p t (u,c))
        have hHmeas : Measurable κH := parameterized_map_measurable _ _ (first_jump_future_measurable N n s p t)
        have hbudget : liveCard e ≤ n := by
          have hc := merger_destination_card N s p
          dsimp only [e]
          omega
        have hpoint (u : ℝ) (hu : u ≤ (t : ℝ)) : κJ u = attachResiduals N r (n+1) s (κH u) := by
          have htime : ((Real.toNNReal ((t : ℝ)-u) : ℝ≥0) : ℝ) = (t : ℝ)-u :=
            Real.coe_toNNReal _ (sub_nonneg.mpr hu)
          have hi := ih e (Real.toNNReal ((t : ℝ)-u)) hbudget
          rw [htime] at hi
          have hH : κH u = (actualMarkedTraceLaw N r n e ((t : ℝ)-u)).map (prependHistory N n e u) := by
            rw [actualMarkedTraceLaw,Measure.map_map (prepend_history_measurable N n e u)
              (marked_trace_measurable N n e ((t : ℝ)-u))]
            rfl
          have hJ : κJ u = (actualCutJointLaw N r n e ((t : ℝ)-u)).map
              (Prod.map (prependHistory N n e u) (id : CutResidual N sample → CutResidual N sample)) := by
            rw [actualCutJointLaw,Measure.map_map ((prepend_history_measurable N n e u).prodMap measurable_id)
              ((marked_trace_measurable N n e ((t : ℝ)-u)).prodMk
                (literal_cut_measurable N n e ((t : ℝ)-u)))]
            rfl
          rw [hJ,hi,← attach_residuals_prepend N r n s e u,← hH]
        change ((ν.prod (currentPairClockMeasure N r e)).map (firstJumpJointFuture N n s p t)) =
          attachResiduals N r (n+1) s ((ν.prod (currentPairClockMeasure N r e)).map (firstJumpFuture N n s p t))
        rw [product_map_eq_bind _ _ _ (first_jump_joint_future_measurable N n s p t),
          product_map_eq_bind _ _ _ (first_jump_future_measurable N n s p t),
          attach_residuals_bind _ _ _ _ _ _ hHmeas]
        apply Measure.bind_congr_right
        filter_upwards [ae_restrict_mem measurableSet_Iic] with u hu
        exact hpoint u hu
      rw [actual_cut_joint_first_jump_renewal,actual_marked_trace_first_jump_renewal,
        attach_residuals_add,attach_residuals_smul,attach_empty_history,attach_residuals_finset_sum]
      congr 1
      apply Finset.sum_congr rfl
      intro p _
      exact hbranch p

#print axioms attach_residuals_add
#print axioms attach_residuals_smul
#print axioms attach_residuals_finset_sum
#print axioms attach_residuals_bind
#print axioms attach_empty_history
#print axioms actual_full_past_residual_factorization


/-- The explicit attachment is exactly a sum of unnormalized history fibres
times the original current-clock products. This is algebra of the defined
functional, not an assumed identity with the actual joint law. -/
theorem attachment_eq_terminal_fibre_sum (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample)
    (ν : Measure (Bool × ClockTrace N sample n)) :
    attachResiduals N r n s ν =
      ∑ d : Code N sample,
        ((ν.restrict {h | decodedEndpoint N n s h = some d}).prod (currentPairClockMeasure N r d)).map
          (fun z => (z.1,encodeResidual N d z.2)) := by
  ext A hA
  let F (d : Code N sample) (h : Bool × ClockTrace N sample n) : ℝ≥0∞ :=
    ((currentPairClockMeasure N r d).map (fun c => (h,encodeResidual N d c))) A
  have hF (d : Code N sample) : Measurable (F d) :=
    (Measure.measurable_coe hA).comp
      (parameterized_map_measurable (currentPairClockMeasure N r d)
        (fun z => (z.1,encodeResidual N d z.2))
        (measurable_fst.prodMk ((encode_residual_measurable N d).comp measurable_snd)))
  have hD (d : Code N sample) : MeasurableSet {h | decodedEndpoint N n s h = some d} :=
    (decoded_endpoint_measurable N n s) (show MeasurableSet ({some d} : Set (Option (Code N sample))) by trivial)
  have he (h : Bool × ClockTrace N sample n) :
      (historyResidualKernel N r n s h) A =
        ∑ d : Code N sample, {z | decodedEndpoint N n s z = some d}.indicator (F d) h := by
    cases hd : decodedEndpoint N n s h <;> simp [historyResidualKernel,hd,Set.indicator,F]
  rw [attachResiduals,Measure.bind_apply hA (history_residual_kernel_measurable N r n s).aemeasurable,
    Measure.finsetSum_apply]
  simp_rw [he]
  rw [lintegral_finsetSum _ (fun d _ => (hF d).indicator (hD d))]
  apply Finset.sum_congr rfl
  intro d _
  have hm : Measurable (fun z : (Bool × ClockTrace N sample n) × (Choice N d → ℝ) =>
      (z.1,encodeResidual N d z.2)) :=
    measurable_fst.prodMk ((encode_residual_measurable N d).comp measurable_snd)
  rw [lintegral_indicator (hD d),Measure.map_apply hm hA,Measure.prod_apply (hm hA)]
  apply lintegral_congr
  intro h
  dsimp only [F]
  rw [Measure.map_apply (measurable_const.prodMk (encode_residual_measurable N d)) hA]
  rfl

/-- Candidate explicit terminal-fibre form of the actual full recorded-past
law. Every fibre remains unnormalized, including null fibres. -/
theorem actual_full_past_terminal_fibres (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (t : ℝ≥0)
    (hn : liveCard s ≤ n) :
    actualCutJointLaw N r n s (t : ℝ) =
      ∑ d : Code N sample,
        (((actualMarkedTraceLaw N r n s (t : ℝ)).restrict
          {h | decodedEndpoint N n s h = some d}).prod (currentPairClockMeasure N r d)).map
            (fun z => (z.1,encodeResidual N d z.2)) := by
  rw [actual_full_past_residual_factorization N r n s t hn,attachment_eq_terminal_fibre_sum]

#print axioms attachment_eq_terminal_fibre_sum
#print axioms actual_full_past_terminal_fibres

end GProgram.G2.HistoryResidualAttachment
