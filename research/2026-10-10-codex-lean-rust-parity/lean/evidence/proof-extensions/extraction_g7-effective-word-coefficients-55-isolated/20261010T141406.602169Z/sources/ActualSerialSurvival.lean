import G5ActualRoutingSupport

/-! Exact weighted no-merger route recursion for the original finite program.
Contributor: dot (OpenAI), 9 October 2026.
Prior: research/2026-10-07-dot-resumed-g5-conditional-2138z/
WHOLE-PREFIX-POSTERIOR-CANDIDATE-r2.md, Section 4.
Implements the accepted whole-prefix mass expansion using the existing actual
source kernels. This does not grant an internal-cut observation to G4. -/
namespace DotG34.ActualSerialSurvival
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceActualHoldingClocks
open GProgram.G5.ActualNoMergerReadout GProgram.G5.ActualRoutingSupport
open scoped Classical NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Subprobability kernel: intervals hold with their ACTUAL holding mass;
all original boundary routing, owners and shared registers are retained. -/
noncomputable def weightedRoute (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) : List (ProgramStep N) → Code N sample → Code N sample → ℝ≥0∞
  | [], s, d => PMF.pure s d
  | .interval t :: ops, s, d => sourceTimeKernel N r t s s * weightedRoute N r ops s d
  | .boundary b :: ops, s, d => ∑' m, boundaryKernel N b s m * weightedRoute N r ops m d

lemma weightedRoute_zero (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s d : Code N sample)
    (hc : liveCard d ≠ liveCard s) : weightedRoute N r ops s d=0 := by
  induction ops generalizing s with
  | nil =>
      have hd : d≠s := by intro h; exact hc (congrArg liveCard h)
      simp [weightedRoute,PMF.pure_apply,hd,Ne.symm hd]
  | cons op ops ih =>
      cases op with
      | interval t => simp [weightedRoute,ih s hc]
      | boundary b =>
          change (∑' m, boundaryKernel N b s m * weightedRoute N r ops m d)=0
          have hpoint (m : Code N sample) : boundaryKernel N b s m * weightedRoute N r ops m d=0 := by
            by_cases hm : boundaryKernel N b s m=0
            · simp [hm]
            · have hcard := boundary_live_card N b s m hm
              have hne : liveCard d≠liveCard m := by omega
              rw [ih m hne,mul_zero]
          simp only [hpoint,tsum_zero]

/-- No source-history equality is a premise. Lost roots cannot be recreated. -/
theorem actual_same_count_mass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s d : Code N sample)
    (hc : liveCard d=liveCard s) :
    sourceProgram N r ops s d=weightedRoute N r ops s d := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih =>
      cases op with
      | interval t =>
          change ((sourceTimeKernel N r t s).bind (sourceProgram N r ops)) d = _
          rw [PMF.bind_apply]
          rw [tsum_eq_single s]
          · exact congrArg (fun z => sourceTimeKernel N r t s s*z) (ih s hc)
          · intro m hms
            by_cases hm : sourceTimeKernel N r t s m=0
            · simp [hm]
            · by_cases hmd : sourceProgram N r ops m d=0
              · simp [hmd]
              · have hstep := epoch_card_le N r t s m hm
                have htail := program_card_le N r ops m d hmd
                have hcard : liveCard m=liveCard s := by omega
                exact False.elim (hms (actual_kernel_same_card_eq N r t s m hm hcard))
      | boundary b =>
          change ((boundaryKernel N b s).bind (sourceProgram N r ops)) d = _
          rw [PMF.bind_apply]
          apply tsum_congr
          intro m
          by_cases hm : boundaryKernel N b s m=0
          · simp [hm]
          · have hcard := boundary_live_card N b s m hm
            have hcm : liveCard d=liveCard m := hc.trans hcard.symm
            rw [ih m hcm]

/-- Pointwise equality of the restricted actual law and the weighted route law. -/
theorem weightedRoute_eq_restricted (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s d : Code N sample) :
    weightedRoute N r ops s d =
      if liveCard d=liveCard s then sourceProgram N r ops s d else 0 := by
  by_cases hc : liveCard d=liveCard s
  · rw [if_pos hc,actual_same_count_mass N r ops s d hc]
  · rw [if_neg hc,weightedRoute_zero N r ops s d hc]

/-- The actual no-loss event mass is the sum of the derived route weights. -/
theorem actual_no_loss_event (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample) :
    ((sourceProgram N r ops s).map liveCard) (liveCard s) =
      ∑' d, weightedRoute N r ops s d := by
  rw [PMF.map_apply]
  apply tsum_congr
  intro d
  simp [weightedRoute_eq_restricted,eq_comm]

/-- The interval weight is the proved original holding exponential. -/
theorem actual_holding_weight (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) :
    sourceTimeKernel N r t s s = ENNReal.ofReal (Real.exp (-(totalRate N r s*(t:ℝ)))) := by
  rw [← actual_source_kernel_no_merger N r t s]
  exact (ENNReal.ofReal_toReal (PMF.apply_ne_top _ _)).symm

theorem weightedRoute_interval (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (ops : List (ProgramStep N)) (s d : Code N sample) :
    weightedRoute N r (.interval t::ops) s d =
      ENNReal.ofReal (Real.exp (-(totalRate N r s*(t:ℝ)))) * weightedRoute N r ops s d := by
  rw [weightedRoute,actual_holding_weight]

#print axioms actual_same_count_mass
#print axioms weightedRoute_eq_restricted
#print axioms weightedRoute_interval
end DotG34.ActualSerialSurvival
