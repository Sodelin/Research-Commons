import UnifiedLean.Source.SourceLiteralClockEndpoint

/-!
# Reconstructed actual marked clock trace

Contributor: dot, 2026-10-06. NEW source after partial preservation of the
historical timed-G2 package. This follows the unchanged literal endpoint
provider on the actual current-pair clock catalogue. It is not a recovered
historical file or a completed timed-projectivity certificate.
-/
namespace GProgram.G2.LiteralMarkedClockTrace
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceMergerClockCatalogue
open UnifiedLean.Source.SourceRaceWinnerSelection
open UnifiedLean.Source.SourceLiteralClockEndpoint
open UnifiedLean.Source.SourceExponentialRace
open UnifiedLean.Source.SourceExponentialResiduals
open UnifiedLean.Source.SourceWinningClockReset
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceActualHoldingClocks
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

local instance codeMeasurable (N : RootedBinary V E X) (sample : Copy → X) :
    MeasurableSpace (Code N sample) := ⊤
local instance codeOptionMeasurable (N : RootedBinary V E X) (sample : Copy → X) :
    MeasurableSpace (Option (Code N sample)) := ⊤
local instance choiceOptionMeasurable (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : MeasurableSpace (Option (Choice N s)) := ⊤

abbrev ClockTrace (N : RootedBinary V E X) (sample : Copy → X) (n : Nat) :=
  Fin n → Bool × ℝ × Code N sample

def emptyTrace (N : RootedBinary V E X) {sample : Copy → X} (n : Nat)
    (s : Code N sample) : ClockTrace N sample n := fun _ => (false,0,s)

def prependTrace (N : RootedBinary V E X) {sample : Copy → X} {n : Nat}
    (age : ℝ) (d : Code N sample) (z : ClockTrace N sample n) : ClockTrace N sample (n+1) :=
  Fin.cases (true,age,d) (fun i => ((z i).1,age+(z i).2.1,(z i).2.2))

def traceEndpoint (N : RootedBinary V E X) {sample : Copy → X} :
    (n : Nat) → Code N sample → ClockTrace N sample n → Code N sample
  | 0,s,_ => s
  | n+1,_,z => (z (Fin.last n)).2.2

def decodedEndpoint (N : RootedBinary V E X) {sample : Copy → X} (n : Nat)
    (s : Code N sample) (z : Bool × ClockTrace N sample n) : Option (Code N sample) :=
  if z.1 then some (traceEndpoint N n s z.2) else none

noncomputable def literalMarkedTrace (N : RootedBinary V E X) {sample : Copy → X} :
    (n : Nat) → ℝ → (s : Code N sample) → (Choice N s → ℝ) → Bool × ClockTrace N sample n
  | 0,t,s,c => (decide (∀ p : Choice N s, t < c p),emptyTrace N 0 s)
  | n+1,t,s,c => if ∀ p : Choice N s, t < c p then (true,emptyTrace N (n+1) s) else
      match selectedWinner c with
      | none => (false,emptyTrace N (n+1) s)
      | some p => if c p ≤ t then
          let z := literalMarkedTrace N n (t-c p) (stepDestination N s (some p))
            (fun q => c (destinationClockEmbedding N s p q).val-c p)
          (z.1,prependTrace N (c p) (stepDestination N s (some p)) z.2)
        else (false,emptyTrace N (n+1) s)

@[simp] theorem empty_trace_endpoint (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) : traceEndpoint N n s (emptyTrace N n s) = s := by
  cases n <;> rfl

@[simp] theorem prepend_trace_endpoint (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s d : Code N sample) (age : ℝ) (z : ClockTrace N sample n) :
    traceEndpoint N (n+1) s (prependTrace N age d z) = traceEndpoint N n d z := by
  cases n with
  | zero => rfl
  | succ n => simp [traceEndpoint,prependTrace,← Fin.succ_last]

/-- The trace's endpoint is the exact previously proved literal clock compiler,
including pathological and exhausted-budget outcomes. -/
theorem marked_trace_endpoint_eq (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (t : ℝ) (c : Choice N s → ℝ) :
    decodedEndpoint N n s (literalMarkedTrace N n t s c) = literalClockEndpoint N n t s c := by
  induction n generalizing s t with
  | zero =>
      by_cases h : ∀ p : Choice N s, t < c p <;>
        simp [literalMarkedTrace,literalClockEndpoint,decodedEndpoint,traceEndpoint,h]
  | succ n ih =>
      by_cases h : ∀ p : Choice N s, t < c p
      · simp [literalMarkedTrace,literalClockEndpoint,h,decodedEndpoint]
      · simp only [literalMarkedTrace,literalClockEndpoint,if_neg h]
        cases hw : selectedWinner c with
        | none => simp [decodedEndpoint]
        | some p =>
          by_cases hp : c p ≤ t
          · simp only [if_pos hp,decodedEndpoint,prepend_trace_endpoint]
            exact ih (stepDestination N s (some p)) (t-c p)
              (fun q => c (destinationClockEmbedding N s p q).val-c p)
          · simp [hp,decodedEndpoint]


/-- A deterministic full clock event: every coordinate is nonnegative and
no two original coordinates coincide. The probabilistic full-mass proof is a
separate obligation below, never a replacement input law. -/
def ClockRegular {I : Type*} (c : I → ℝ) : Prop :=
  (∀ p, 0 ≤ c p) ∧ Function.Injective c

lemma destination_residual_regular (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (c : Choice N s → ℝ) (p : Choice N s)
    (hc : ClockRegular c) (hp : selectedWinner c = some p) :
    ClockRegular (fun q : Choice N (stepDestination N s (some p)) =>
      c (destinationClockEmbedding N s p q).val-c p) := by
  have hw := (selectedWinner_eq_some_iff c p).mp hp
  constructor
  · intro q
    exact (sub_pos.mpr (hw.2 (destinationClockEmbedding N s p q))).le
  · intro q u h
    apply (destinationClockEmbedding N s p).injective
    apply Subtype.ext
    exact hc.2 (sub_left_injective h)

lemma regular_winner_exists {I : Type*} [Fintype I] [DecidableEq I] [Nonempty I]
    (c : I → ℝ) (hc : ClockRegular c) : ∃ p, selectedWinner c = some p := by
  obtain ⟨p,_,hp⟩ := Finset.exists_min_image Finset.univ c Finset.univ_nonempty
  refine ⟨p,(selectedWinner_eq_some_iff c p).mpr ⟨hc.1 p,?_⟩⟩
  intro q
  apply lt_of_le_of_ne (hp q.val (Finset.mem_univ _))
  intro he
  exact q.property (hc.2 he.symm)

theorem marked_trace_success_on_regular (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (t : ℝ) (c : Choice N s → ℝ)
    (hn : UnifiedLean.Source.SourceActualHoldingClocks.liveCard s ≤ n)
    (hc : ClockRegular c) : (literalMarkedTrace N n t s c).1 = true := by
  induction n generalizing s t with
  | zero =>
      have hstop : ∀ p : Choice N s, t < c p := by
        intro p
        have hcard := UnifiedLean.Source.SourceActualHoldingClocks.merger_destination_card N s p
        omega
      simp [literalMarkedTrace,hstop]
  | succ n ih =>
      by_cases hstop : ∀ p : Choice N s, t < c p
      · simp [literalMarkedTrace,hstop]
      · obtain ⟨q,hq⟩ := not_forall.mp hstop
        letI : Nonempty (Choice N s) := ⟨q⟩
        obtain ⟨p,hp⟩ := regular_winner_exists c hc
        have hmin : c p ≤ c q := by
          by_cases he : q=p
          · simp [he]
          · exact ((selectedWinner_eq_some_iff c p).mp hp).2 ⟨q,he⟩ |>.le
        have hpt : c p ≤ t := le_trans hmin (le_of_not_gt hq)
        have hcard := UnifiedLean.Source.SourceActualHoldingClocks.merger_destination_card N s p
        have hbudget : UnifiedLean.Source.SourceActualHoldingClocks.liveCard
            (stepDestination N s (some p)) ≤ n := by omega
        simpa only [literalMarkedTrace,if_neg hstop,hp,if_pos hpt] using
          ih (stepDestination N s (some p)) (t-c p)
            (fun u => c (destinationClockEmbedding N s p u).val-c p) hbudget
            (destination_residual_regular N s c p hc hp)

lemma exponential_clock_nonnegative_ae (r : ℝ) (hr : 0 < r) :
    ∀ᵐ x ∂expMeasure r, 0 ≤ x := by
  letI := isProbabilityMeasure_expMeasure hr
  have hz : (expMeasure r) (Iic 0) = 0 := by
    rw [← ENNReal.ofReal_toReal (measure_ne_top _ _)]
    change ENNReal.ofReal ((expMeasure r).real (Iic 0)) = 0
    rw [exponential_real_Iic hr]
    simp
  rw [ae_iff]
  apply measure_mono_null _ hz
  intro x hx
  exact (lt_of_not_ge hx).le

lemma exponential_clock_pair_ne_ae {I : Type*} [Fintype I] [DecidableEq I]
    (rate : I → ℝ) (hr : ∀ p, 0 < rate p) (p q : I) (hpq : q ≠ p) :
    ∀ᵐ c ∂Measure.pi (fun i => expMeasure (rate i)), c p ≠ c q := by
  letI : ∀ i, IsProbabilityMeasure (expMeasure (rate i)) :=
    fun i => isProbabilityMeasure_expMeasure (hr i)
  letI : ∀ i, NullSingletonClass (expMeasure (rate i)) := fun i => by
    change NullSingletonClass (volume.withDensity (gammaPDF 1 (rate i)))
    infer_instance
  have hprod : ∀ᵐ z ∂(expMeasure (rate p)).prod
      (Measure.pi (fun i : Other p => expMeasure (rate i.val))), z.1 ≠ z.2 ⟨q,hpq⟩ := by
    have hmeas : MeasurableSet {z : ℝ × (Other p → ℝ) | z.1 ≠ z.2 ⟨q,hpq⟩} := by
      simpa only [Set.compl_setOf,Function.comp_apply] using
        (measurableSet_eq_fun
          (measurable_fst : Measurable (fun z : ℝ × (Other p → ℝ) => z.1))
          ((measurable_pi_apply (⟨q,hpq⟩ : Other p)).comp measurable_snd)).compl
    apply (Measure.ae_prod_iff_ae_ae hmeas).mpr
    apply Filter.Eventually.of_forall
    intro x
    filter_upwards [Measure.ae_eval_ne (fun i : Other p => expMeasure (rate i.val)) ⟨q,hpq⟩ x]
      with c hc
    exact Ne.symm hc
  have hm := (splitClock_measurePreserving (fun i => expMeasure (rate i)) p).map_eq
  rw [← hm] at hprod
  exact ae_of_ae_map (splitClock p).measurable.aemeasurable hprod

theorem actual_current_clock_regular_ae (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) :
    ∀ᵐ c ∂currentPairClockMeasure N r s, ClockRegular c := by
  let rate : Choice N s → ℝ := fun p => choiceRate N r s p
  have hr : ∀ p, 0 < rate p := fun p => div_pos (pairRate_pos r p.1) (by norm_num)
  letI : ∀ p, IsProbabilityMeasure (expMeasure (rate p)) :=
    fun p => isProbabilityMeasure_expMeasure (hr p)
  have hn : ∀ᵐ c ∂Measure.pi (fun p => expMeasure (rate p)), ∀ p, 0 ≤ c p := by
    apply ae_all_iff.mpr
    intro p
    exact Measure.tendsto_eval_ae_ae.eventually (exponential_clock_nonnegative_ae (rate p) (hr p))
  have hi : ∀ᵐ c ∂Measure.pi (fun p => expMeasure (rate p)), ∀ p q, p ≠ q → c p ≠ c q := by
    apply ae_all_iff.mpr
    intro p
    apply ae_all_iff.mpr
    intro q
    by_cases hpq : p=q
    · exact Filter.Eventually.of_forall (fun _ h => False.elim (h hpq))
    · filter_upwards [exponential_clock_pair_ne_ae rate hr p q (Ne.symm hpq)] with c hc
      exact fun _ => hc
  filter_upwards [hn,hi] with c hc hd
  exact ⟨hc,fun p q he => by by_contra hpq; exact hd p q hpq he⟩

/-- The marked trace is jointly measurable in horizon and the original clock
vector; recursive destination clocks are the actual retained residuals. -/
theorem marked_trace_joint_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) :
    Measurable (fun z : ℝ × (Choice N s → ℝ) => literalMarkedTrace N n z.1 s z.2) := by
  induction n generalizing s with
  | zero =>
      have h : Measurable (fun z : ℝ × (Choice N s → ℝ) =>
          if ∀ p : Choice N s, z.1 < z.2 p then
            (true,emptyTrace N 0 s) else (false,emptyTrace N 0 s)) :=
        Measurable.ite (measurable_no_jump N s) measurable_const measurable_const
      convert h using 1
      funext z
      by_cases hz : ∀ p : Choice N s, z.1 < z.2 p <;> simp [literalMarkedTrace,hz]
  | succ n ih =>
      let dispatch : (ℝ × (Choice N s → ℝ)) × Option (Choice N s) →
          Bool × ClockTrace N sample (n+1) := fun z =>
        match z.2 with
        | none => (false,emptyTrace N (n+1) s)
        | some p => if z.1.2 p ≤ z.1.1 then
            let w := literalMarkedTrace N n (z.1.1-z.1.2 p)
              (stepDestination N s (some p))
              (fun q => z.1.2 (destinationClockEmbedding N s p q).val-z.1.2 p)
            (w.1,prependTrace N (z.1.2 p) (stepDestination N s (some p)) w.2)
          else (false,emptyTrace N (n+1) s)
      have hd : Measurable dispatch := by
        apply measurable_from_prod_countable_left
        intro p
        cases p with
        | none => exact measurable_const
        | some p =>
            apply Measurable.ite
            · exact measurableSet_le ((measurable_pi_apply p).comp measurable_snd) measurable_fst
            · have hinput : Measurable (fun z : ℝ × (Choice N s → ℝ) =>
                  (z.1-z.2 p,fun q : Choice N (stepDestination N s (some p)) =>
                    z.2 (destinationClockEmbedding N s p q).val-z.2 p)) := by fun_prop
              have hw := (ih (stepDestination N s (some p))).comp hinput
              apply hw.fst.prodMk
              apply measurable_pi_lambda
              intro i
              refine Fin.cases ?_ (fun j => ?_) i
              · exact measurable_const.prodMk
                  (((measurable_pi_apply p).comp measurable_snd).prodMk measurable_const)
              · exact (((measurable_pi_apply j).comp hw.snd).fst).prodMk
                  ((((measurable_pi_apply p).comp measurable_snd).add
                    (((measurable_pi_apply j).comp hw.snd).snd.fst)).prodMk
                    (((measurable_pi_apply j).comp hw.snd).snd.snd))
            · exact measurable_const
      have hselect : Measurable (fun z : ℝ × (Choice N s → ℝ) => (z,selectedWinner z.2)) :=
        measurable_id.prodMk (selectedWinner_measurable.comp measurable_snd)
      exact Measurable.ite (measurable_no_jump N s) measurable_const (hd.comp hselect)

theorem marked_trace_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (t : ℝ) :
    Measurable (literalMarkedTrace N n t s) :=
  (marked_trace_joint_measurable N n s).comp (measurable_const.prodMk measurable_id)

/-- The law retains the actual original clock measure, without conditioning on
success or drawing endpoint topology separately. -/
noncomputable def actualMarkedTraceLaw (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (t : ℝ) :
    Measure (Bool × ClockTrace N sample n) :=
  (UnifiedLean.Source.SourceActualHoldingClocks.currentPairClockMeasure N r s).map
    (literalMarkedTrace N n t s)

#print axioms empty_trace_endpoint
#print axioms prepend_trace_endpoint
#print axioms marked_trace_endpoint_eq
#print axioms destination_residual_regular
#print axioms regular_winner_exists
#print axioms marked_trace_success_on_regular
#print axioms exponential_clock_nonnegative_ae
#print axioms exponential_clock_pair_ne_ae
#print axioms actual_current_clock_regular_ae
#print axioms marked_trace_joint_measurable
#print axioms marked_trace_measurable
end GProgram.G2.LiteralMarkedClockTrace
