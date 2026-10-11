import G1SourceMacroComposition

/-! Complete original unranked interface checkpoint histories through repeated
SOURCE-derived K substitutions. Original populations and Γ are retained at
EVERY checkpoint, and an arbitrary quotient continuation stays joint with the
entire history. Within-epoch clock paths are not observed. Contributor: dot. -/
namespace G1SourceMacroInterfaceHistory
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport
open G1UnrankedSourceView G1UnrankedActualFuture
open G1OriginalWholeCausalView G1SourceMacroComposition
open scoped Classical
variable {V E X Copy Obs : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

abbrev InterfaceHistory (V E Copy Obs : Type*) := List (UnrankedView V E Copy) × Obs

def prependView (v : UnrankedView V E Copy) (h : InterfaceHistory V E Copy Obs) :
    InterfaceHistory V E Copy Obs := (v::h.1,h.2)

noncomputable def actualOriginalInterfaceHistory (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (terminal : UnrankedView V E Copy → PMF Obs) :
    List (SourceMacroStage N sample r) → Code N sample → PMF (InterfaceHistory V E Copy Obs)
  | [],s => (terminal (wholeOriginalView N s)).map (fun x => ([],x))
  | a::as,s => (sourceProgram N r a.phase s).bind
      (fun d => (actualOriginalInterfaceHistory N r terminal as d).map (prependView (wholeOriginalView N d)))

noncomputable def sourceMacroInterfaceHistory (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (terminal : UnrankedView V E Copy → PMF Obs) :
    List (SourceMacroStage N sample r) → Code N sample → PMF (InterfaceHistory V E Copy Obs)
  | [],s => (terminal (wholeOriginalView N s)).map (fun x => ([],x))
  | a::as,s => (admittedMacroRow N r a.phase a.planner s).bind
      (fun d => (sourceMacroInterfaceHistory N r terminal as d).map (prependView (wholeOriginalView N d)))

theorem actual_original_interface_history_row_independent (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (terminal : UnrankedView V E Copy → PMF Obs)
    (stages : List (SourceMacroStage N sample r)) (s z : Code N sample)
    (h : wholeOriginalView N s = wholeOriginalView N z) :
    actualOriginalInterfaceHistory N r terminal stages s =
      actualOriginalInterfaceHistory N r terminal stages z := by
  induction stages generalizing s z with
  | nil => simp only [actualOriginalInterfaceHistory,h]
  | cons a as ih =>
    rw [actualOriginalInterfaceHistory,actualOriginalInterfaceHistory]
    apply bind_through_equal_view s _ _ (wholeOriginalView N)
      (actual_unranked_future_row_independent N r Finset.univ a.phase s z h id)
    intro d w hw
    rw [ih d w hw,hw]

/-- Entire ORIGINAL unranked checkpoint trajectory, concurrently evolving
exterior state, Γ and terminal quotient continuation remain JOINT. This is a
joint path law, not a collection of matching separate marginals. -/
theorem actual_repeated_macro_whole_interface_history (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (terminal : UnrankedView V E Copy → PMF Obs)
    (stages : List (SourceMacroStage N sample r)) (s : Code N sample) :
    sourceMacroInterfaceHistory N r terminal stages s =
      actualOriginalInterfaceHistory N r terminal stages s := by
  induction stages generalizing s with
  | nil => rfl
  | cons a as ih =>
    rw [sourceMacroInterfaceHistory,actualOriginalInterfaceHistory]
    simp_rw [ih]
    apply bind_through_equal_view s _ _ (wholeOriginalView N)
      (actual_admitted_macro_row N r a.phase a.planner s)
    intro d w hw
    rw [actual_original_interface_history_row_independent N r terminal as d w hw,hw]

/-- Arbitrarily correlated real entering state and retained exterior/root
history are integrated in the SAME case. Γ, opaque carried subtrees and hidden
root history are never replaced by freshly sampled independent marginals. -/
theorem actual_joint_entering_history_macro_substitution {History : Type*}
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (terminal : History → UnrankedView V E Copy → PMF Obs)
    (stages : List (SourceMacroStage N sample r)) (prior : PMF (Code N sample × History)) :
    prior.bind (fun c => (sourceMacroInterfaceHistory N r (terminal c.2) stages c.1).map
      (fun h => (c.2,h))) =
    prior.bind (fun c => (actualOriginalInterfaceHistory N r (terminal c.2) stages c.1).map
      (fun h => (c.2,h))) := by
  congr 1
  funext c
  rw [actual_repeated_macro_whole_interface_history]

#print axioms actual_repeated_macro_whole_interface_history
#print axioms actual_joint_entering_history_macro_substitution
end G1SourceMacroInterfaceHistory
