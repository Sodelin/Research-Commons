import UnifiedLean.Source.SourceRaceWinnerSelection

/-!
# Literal source clock-vector endpoint compiler

Contributor: dot, 2026-10-02. On the ACTUAL finite original CURRENT pair clock
vector, stop at the supplied elapsed duration, or select its actual unique
winner, perform the actual merger, retain exactly the proved destination
residual clock catalogue, and recurse. Joint elapsed-time/clock measurability
is proved. None records a pathological/tie or exhausted-budget outcome; its
zero mass at the original copy cap is a subsequent distribution theorem.
No clock-path probability or desired source kernel is an input field.
-/
namespace UnifiedLean.Source.SourceLiteralClockEndpoint
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Set
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceMergerClockCatalogue
open UnifiedLean.Source.SourceRaceWinnerSelection
open scoped Classical NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

local instance codeOptionMeasurable (N : RootedBinary V E X) (sample : Copy → X) :
    MeasurableSpace (Option (Code N sample)) := ⊤
local instance choiceOptionMeasurable (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : MeasurableSpace (Option (Choice N s)) := ⊤

/-- Stop without a merger iff all actual clocks exceed the elapsed duration.
Otherwise use the literal winning pair and actual destination residuals.
The recursion budget counts REAL mergers, never dummy uniformization holds. -/
noncomputable def literalClockEndpoint (N : RootedBinary V E X) {sample : Copy → X} :
    Nat → ℝ → (s : Code N sample) → (Choice N s → ℝ) → Option (Code N sample)
  | 0,t,s,c => if ∀ p : Choice N s, t < c p then some s else none
  | n+1,t,s,c => if ∀ p : Choice N s, t < c p then some s else
      match selectedWinner c with
      | none => none
      | some p => if c p ≤ t then
          literalClockEndpoint N n (t-c p) (stepDestination N s (some p))
            (fun q => c (destinationClockEmbedding N s p q).val-c p)
        else none

lemma measurable_no_jump (N : RootedBinary V E X) {sample : Copy → X} (s : Code N sample) :
    MeasurableSet {z : ℝ × (Choice N s → ℝ) | ∀ p : Choice N s, z.1 < z.2 p} := by
  have hh : MeasurableSet (⋂ p : Choice N s, {z : ℝ × (Choice N s → ℝ) | z.1 < z.2 p}) :=
    MeasurableSet.iInter (fun p : Choice N s => measurableSet_lt measurable_fst
      ((measurable_pi_apply p).comp measurable_snd))
  simpa only [Set.setOf_forall] using hh

/-- Joint time/clock measurability is derived through the actual recursive
destination catalogue; it is not assumed from an abstract stochastic path. -/
theorem literal_endpoint_joint_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) :
    Measurable (fun z : ℝ × (Choice N s → ℝ) => literalClockEndpoint N n z.1 s z.2) := by
  induction n generalizing s with
  | zero =>
      change Measurable (fun z : ℝ × (Choice N s → ℝ) =>
        if ∀ p : Choice N s, z.1 < z.2 p then some s else none)
      exact Measurable.ite (measurable_no_jump N s) measurable_const measurable_const
  | succ n ih =>
      let dispatch : (ℝ × (Choice N s → ℝ)) × Option (Choice N s) → Option (Code N sample) :=
        fun z => match z.2 with
        | none => none
        | some p => if z.1.2 p ≤ z.1.1 then
            literalClockEndpoint N n (z.1.1-z.1.2 p) (stepDestination N s (some p))
              (fun q => z.1.2 (destinationClockEmbedding N s p q).val-z.1.2 p)
          else none
      have hd : Measurable dispatch := by
        apply measurable_from_prod_countable_left
        intro p
        cases p with
        | none => exact measurable_const
        | some p =>
            change Measurable (fun z : ℝ × (Choice N s → ℝ) =>
              if z.2 p ≤ z.1 then literalClockEndpoint N n (z.1-z.2 p) (stepDestination N s (some p))
                (fun q => z.2 (destinationClockEmbedding N s p q).val-z.2 p) else none)
            apply Measurable.ite
            · exact measurableSet_le ((measurable_pi_apply p).comp measurable_snd) measurable_fst
            · have hinput : Measurable (fun z : ℝ × (Choice N s → ℝ) =>
                  (z.1-z.2 p,fun q : Choice N (stepDestination N s (some p)) =>
                    z.2 (destinationClockEmbedding N s p q).val-z.2 p)) := by fun_prop
              exact (ih (stepDestination N s (some p))).comp hinput
            · exact measurable_const
      have hselect : Measurable (fun z : ℝ × (Choice N s → ℝ) => (z,selectedWinner z.2)) :=
        measurable_id.prodMk (selectedWinner_measurable.comp measurable_snd)
      have hall : Measurable (fun z : ℝ × (Choice N s → ℝ) =>
          if ∀ p : Choice N s, z.1 < z.2 p then some s else dispatch (z,selectedWinner z.2)) :=
        Measurable.ite (measurable_no_jump N s) measurable_const (hd.comp hselect)
      exact hall

/-- Each fixed actual epoch-duration readout is therefore measurable on the
literal original finite exponential clock space. -/
theorem literal_endpoint_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (n : Nat) (s : Code N sample) (t : ℝ) :
    Measurable (literalClockEndpoint N n t s) := by
  exact (literal_endpoint_joint_measurable N n s).comp (measurable_const.prodMk measurable_id)

#print axioms literal_endpoint_joint_measurable
#print axioms literal_endpoint_measurable
end UnifiedLean.Source.SourceLiteralClockEndpoint
