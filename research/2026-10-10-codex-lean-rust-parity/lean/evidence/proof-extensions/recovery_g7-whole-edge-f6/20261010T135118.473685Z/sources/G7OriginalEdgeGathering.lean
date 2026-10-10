import G7OriginalEdgeBoundary
import UnifiedLean.Source.SourceNaturalInitialization

/-!
Complete right-to-left original-edge exposure gathering algorithm. Its input
is the literal finite chronological event syntax; pending exposure is dropped
only after the edge's actual exit, and flushed only at its original entry node.
All source operators are constructed in the preceding implementation files.
Uncompiled candidate, dot 2026-10-10. The final arbitrary-calendar comparison
requires the calendar accumulator identity and topology-order consumer below.
-/
namespace GProgram.G7.OriginalEdgeGathering
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceBoundaryLocations
open UnifiedLean.Source.SourceCalendarPhysicalSupport UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.MatrixProjectionExponential
open GProgram.G7.NodeActions GProgram.G7.OriginalEdgeOperators GProgram.G7.OriginalEdgeBoundary
open Matrix NormedSpace
open scoped Classical BigOperators NNReal Matrix.Norms.Operator
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

abbrev ExposureBank (E : Type*) := Option E → ℝ
noncomputable def bankGenerator (N : RootedBinary V E X) {sample : Copy → X}
    (w : ExposureBank E) : Matrix (Code N sample) (Code N sample) ℝ :=
  ∑ i : Option E, w i • populationGenerator N i
noncomputable def bankExponential (N : RootedBinary V E X) {sample : Copy → X}
    (w : ExposureBank E) : Matrix (Code N sample) (Code N sample) ℝ := exp (bankGenerator N w)

lemma bankGenerator_add (N : RootedBinary V E X) {sample : Copy → X} (w z : ExposureBank E) :
    bankGenerator N (sample:=sample) (w+z) = bankGenerator N w + bankGenerator N z := by
  simp [bankGenerator,add_smul,Finset.sum_add_distrib]
lemma bankGenerator_commute (N : RootedBinary V E X) {sample : Copy → X} (w z : ExposureBank E) :
    Commute (bankGenerator N (sample:=sample) w) (bankGenerator N z) := by
  exact Commute.sum_left _ _ _ (fun i _ => Commute.sum_right _ _ _ (fun j _ =>
    ((population_generators_commute N i j).smul_left (w i)).smul_right (z j)))
lemma bankExponential_add (N : RootedBinary V E X) {sample : Copy → X} (w z : ExposureBank E) :
    bankExponential N (sample:=sample) (w+z) = bankExponential N w * bankExponential N z := by
  simp only [bankExponential,bankGenerator_add,exp_add_of_commute (bankGenerator_commute N w z)]
@[simp] lemma bankExponential_zero (N : RootedBinary V E X) {sample : Copy → X} :
    bankExponential N (sample:=sample) 0 = 1 := by simp [bankExponential,bankGenerator]

noncomputable def retain (P : Option E → Prop) (w : ExposureBank E) : ExposureBank E :=
  fun i => if P i then w i else 0
lemma retain_split (P : Option E → Prop) (w : ExposureBank E) :
    w = retain P w + retain (fun i => ¬ P i) w := by
  funext i
  by_cases h : P i <;> simp [retain,h]

def Opens (N : RootedBinary V E X) (v : V) : Option E → Prop
  | none => v = N.root
  | some e => v = N.graph.target e

/-- Outside a node's actual incoming original populations, each generator
commutes with the node. Ancestor/root is handled as its own original slot. -/
lemma node_remainder_commutes (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) (w : ExposureBank E) :
    Commute (bankExponential N (sample:=sample) (retain (fun i => ¬ Opens N v i) w))
      (boundaryMatrix N (originalNodeOperation N H gamma common v)) := by
  apply Commute.exp_left
  apply Commute.sum_left _ _ _
  intro i _
  by_cases hi : Opens N v i
  · simp [retain,hi,Commute.zero_left]
  · rw [retain,if_pos hi]
    rw [←original_operation N H gamma common v]
    apply Commute.smul_left
    cases i with
    | none => exact node_population_generator_commute _ none (original_node_avoids_root N H gamma common v hi)
    | some e => exact node_population_generator_commute _ (some e) (original_node_avoids_other_edge N H gamma common v e hi)

lemma node_flush_bank (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (v : V) (w : ExposureBank E) :
    boundaryMatrix N (sample:=sample) (originalNodeOperation N H gamma common v) * bankExponential N w =
      bankExponential N (retain (fun i => ¬ Opens N v i) w) *
        (boundaryMatrix N (originalNodeOperation N H gamma common v) *
          bankExponential N (retain (Opens N v) w)) := by
  have hs : w = retain (fun i => ¬ Opens N v i) w + retain (Opens N v) w := by
    simpa only [not_not] using retain_split (fun i => ¬ Opens N v i) w
  rw [hs,bankExponential_add,←Matrix.mul_assoc,
    (node_remainder_commutes N H gamma common v w).eq.symm,Matrix.mul_assoc]

lemma exit_has_no_pair (N : RootedBinary V E X) {sample : Copy → X}
    (e : E) (s : Code N sample) (p : Copy × Copy) : ¬ PairAt N (some e) p (exitCode N s e) := by
  intro hp
  have pp := (pairAt_iff N (some e) p (exitCode N s e)).mp hp
  apply exit_removes_edge N s e p.1
  change (state (exitCode N s e)).location ((state (exitCode N s e)).ancestor p.1) = _
  rw [(exitCode N s e).property.forest.representative p.1 pp.1]
  exact pp.2.1

lemma exit_absorbs_pair_matrix (N : RootedBinary V E X) {sample : Copy → X} (e : E) (p : Copy × Copy) :
    boundaryMatrix N (sample:=sample) (.exit e) * pairMatrix N (some e) p = boundaryMatrix N (.exit e) := by
  ext s d
  simp only [Matrix.mul_apply,boundaryMatrix,boundaryKernel,PMF.pure_apply,pairMatrix]
  simp [mergeAt_of_not_mem N (some e) p (exitCode N s e) (exit_has_no_pair N e s p)]

/-- Correct row-vector orientation: execute the exit, then its own generator. -/
theorem exit_annihilates_own_generator (N : RootedBinary V E X) {sample : Copy → X} (e : E) :
    boundaryMatrix N (sample:=sample) (.exit e) * populationGenerator N (some e) = 0 := by
  simp only [populationGenerator,Matrix.mul_smul,Finset.mul_sum,Matrix.mul_sub,
    exit_absorbs_pair_matrix,Matrix.mul_one,sub_self,Finset.sum_const_zero,smul_zero]

theorem exit_absorbs_own_exponential (N : RootedBinary V E X) {sample : Copy → X} (e : E) (a : ℝ) :
    boundaryMatrix N (sample:=sample) (.exit e) * populationExponential N (some e) a =
      boundaryMatrix N (.exit e) := by
  have h := rectangular_scaled_exp_intertwining
    (0 : Matrix (Code N sample) (Code N sample) ℝ) (populationGenerator N (some e))
    (boundaryMatrix N (.exit e)) (by simp [exit_annihilates_own_generator]) a
  simpa [populationExponential] using h.symm

lemma single_bank_exponential (N : RootedBinary V E X) {sample : Copy → X} (i : Option E) (w : ExposureBank E) :
    bankExponential N (sample:=sample) (retain (fun j => j=i) w) = populationExponential N i (w i) := by
  simp [bankExponential,bankGenerator,retain,populationExponential]

lemma exit_remainder_commutes (N : RootedBinary V E X) {sample : Copy → X}
    (e : E) (w : ExposureBank E) :
    Commute (bankExponential N (sample:=sample) (retain (fun i => i ≠ some e) w))
      (boundaryMatrix N (.exit e)) := by
  apply Commute.exp_left
  apply Commute.sum_left _ _ _
  intro i _
  by_cases hi : i = some e
  · simp [retain,hi,Commute.zero_left]
  · rw [retain,if_pos hi]
    exact (exit_population_generator_commute N i e hi).smul_left (w i)

lemma exit_drop_bank (N : RootedBinary V E X) {sample : Copy → X} (e : E) (w : ExposureBank E) :
    boundaryMatrix N (sample:=sample) (.exit e) * bankExponential N w =
      bankExponential N (retain (fun i => i ≠ some e) w) * boundaryMatrix N (.exit e) := by
  have hs : w = retain (fun i => i ≠ some e) w + retain (fun i => i = some e) w := by
    simpa only [not_not] using retain_split (fun i => i ≠ some e) w
  rw [hs,bankExponential_add,single_bank_exponential,←Matrix.mul_assoc,
    (exit_remainder_commutes N e w).eq.symm,Matrix.mul_assoc,exit_absorbs_own_exponential]

noncomputable def initialRow (N : RootedBinary V E X) (sample : Copy → X) (register : V → Bool) :
    Matrix Unit (Code N sample) ℝ := fun _ s => if initialCode N sample register = s then 1 else 0

lemma initial_has_no_pair (N : RootedBinary V E X) (sample : Copy → X) (register : V → Bool)
    (i : Option E) (p : Copy × Copy) : ¬ PairAt N i p (initialCode N sample register) := by
  intro hp
  have hh := ((pairAt_iff N i p (initialCode N sample register)).mp hp).2.1
  cases i <;> simp [initialCode,state,admittedCode,encodeSnapshot,decodeSnapshot,initial,originalPlace] at hh

lemma initial_absorbs_pair (N : RootedBinary V E X) (sample : Copy → X) (register : V → Bool)
    (i : Option E) (p : Copy × Copy) :
    initialRow N sample register * pairMatrix N i p = initialRow N sample register := by
  ext u d
  simp [Matrix.mul_apply,initialRow,pairMatrix,
    mergeAt_of_not_mem N i p (initialCode N sample register) (initial_has_no_pair N sample register i p)]

lemma initial_annihilates_population (N : RootedBinary V E X) (sample : Copy → X) (register : V → Bool)
    (i : Option E) : initialRow N sample register * populationGenerator N i = 0 := by
  simp only [populationGenerator,Matrix.mul_smul,Finset.mul_sum,Matrix.mul_sub,
    initial_absorbs_pair,Matrix.mul_one,sub_self,Finset.sum_const_zero,smul_zero]

theorem actual_initial_absorbs_pending_bank (N : RootedBinary V E X) (sample : Copy → X)
    (register : V → Bool) (w : ExposureBank E) :
    initialRow N sample register * bankExponential N w = initialRow N sample register := by
  have hz : initialRow N sample register * bankGenerator N w = 0 := by
    simp [bankGenerator,Finset.mul_sum,Matrix.mul_smul,initial_annihilates_population]
  have h := rectangular_exp_intertwining (0 : Matrix Unit Unit ℝ) (bankGenerator N w)
    (initialRow N sample register) (by simpa using hz.symm)
  simpa [bankExponential] using h.symm

/-- This finite syntax contains only the original clock interval, exit ID and
node ID. It does not replace any biological primitive by an oracle. -/
inductive Event (V E : Type*)
  | interval (time : ℝ≥0)
  | exit (edge : E)
  | node (vertex : V)

inductive Gathered (V E : Type*)
  | exit (edge : E)
  | node (vertex : V) (exposure : ExposureBank E)

noncomputable def eventMatrix (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) : Event V E → Matrix (Code N sample) (Code N sample) ℝ
  | .interval t => bankExponential N (fun i => (t:ℝ)*pairRate r i)
  | .exit e => boundaryMatrix N (.exit e)
  | .node v => boundaryMatrix N (originalNodeOperation N H gamma common v)

noncomputable def gatheredMatrix (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) : Gathered V E → Matrix (Code N sample) (Code N sample) ℝ
  | .exit e => boundaryMatrix N (.exit e)
  | .node v w => boundaryMatrix N (originalNodeOperation N H gamma common v) * bankExponential N w

/-- The complete finite algorithm. Each processed suffix supplies its pending
bank. An exit erases its own later exposure; its entry flushes only its own
incoming populations. All other pending work is moved left by proved safety. -/
noncomputable def gather (N : RootedBinary V E X) (r : PositivePairRates E) :
    List (Event V E) → ExposureBank E × List (Gathered V E)
  | [] => (0,[])
  | .interval t :: rest =>
      let next := gather N r rest
      ((fun i => (t:ℝ)*pairRate r i) + next.1,next.2)
  | .exit e :: rest =>
      let next := gather N r rest
      (retain (fun i => i ≠ some e) next.1,.exit e :: next.2)
  | .node v :: rest =>
      let next := gather N r rest
      (retain (fun i => ¬ Opens N v i) next.1,.node v (retain (Opens N v) next.1) :: next.2)

/-- Whole-word equality, not a one-boundary lemma: every finite chronological
word is factored into the residual initial bank and the gathered original
node/edge program. No physical-kernel identity is an input. -/
theorem gather_entire_word (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (ops : List (Event V E)) :
    (ops.map (eventMatrix N (sample:=sample) H gamma common r)).prod =
      bankExponential N (gather N r ops).1 *
        ((gather N r ops).2.map (gatheredMatrix N H gamma common)).prod := by
  induction ops with
  | nil => simp [gather]
  | cons op ops ih =>
    cases op with
    | interval t =>
      simp only [List.map_cons,List.prod_cons,eventMatrix,gather]
      rw [ih,←Matrix.mul_assoc,←bankExponential_add]
    | exit e =>
      simp only [List.map_cons,List.prod_cons,eventMatrix,gather]
      rw [ih,←Matrix.mul_assoc,exit_drop_bank,Matrix.mul_assoc]
      rfl
    | node v =>
      simp only [List.map_cons,List.prod_cons,eventMatrix,gather]
      rw [ih,←Matrix.mul_assoc,node_flush_bank,Matrix.mul_assoc]
      rfl

/-- The actual original initialization removes the residual pre-entry bank.
This is proved separately for EACH register realization; natural mixing is
performed once afterward, with its unchanged original parameter assignment. -/
theorem initialized_entire_word_gathering (N : RootedBinary V E X) (sample : Copy → X)
    (register : V → Bool) (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (ops : List (Event V E)) :
    initialRow N sample register * (ops.map (eventMatrix N H gamma common r)).prod =
      initialRow N sample register * ((gather N r ops).2.map (gatheredMatrix N H gamma common)).prod := by
  rw [gather_entire_word,←Matrix.mul_assoc,actual_initial_absorbs_pending_bank]

end GProgram.G7.OriginalEdgeGathering
