import G1ActualSourceKMacroTransition

/-! Physical K-plan admission and repeated actual-source macro interpretation.
Each step uses one literal original program, with actual physical hypotheses.
No output-law identity is a plan field. Contributor: dot, 2026-10-03. -/
namespace G1SourceMacroComposition
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceProgramTransport
open G1ActualJointProgram G1SameOriginalExteriorContinuation
open G1UnrankedSourceView G1UnrankedActualFuture
open G1UnrankedActualGenerator G1ActualUnrankedKMacro
open G1OriginalWholeCausalView G1ActualSourceKMacroTransition
open scoped Classical
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- General quotient bind lemma, instantiated below with the DERIVED actual
source causal quotient. No stochastic output equality is a physical field. -/
lemma bind_through_equal_view {A B C : Type*} (fallback : A)
    (p q : PMF A) (view : A → B) (h : p.map view = q.map view)
    (next : A → PMF C) (stable : ∀ a b, view a = view b → next a = next b) :
    p.bind next = q.bind next := by
  let continuation : B → PMF C := fun v =>
    if hv : ∃ a, view a = v then next (Classical.choose hv) else next fallback
  have hc (a : A) : continuation (view a) = next a := by
    have ha : ∃ b, view b = view a := ⟨a,rfl⟩
    dsimp [continuation]
    rw [dif_pos ha]
    exact stable _ a (Classical.choose_spec ha)
  calc
    p.bind next = (p.map view).bind continuation := by
      rw [PMF.bind_map]
      change p.bind next = p.bind (fun a => continuation (view a))
      congr 1
      funext a
      exact (hc a).symm
    _ = (q.map view).bind continuation := by rw [h]
    _ = q.bind next := by
      rw [PMF.bind_map]
      change q.bind (fun a => continuation (view a)) = q.bind next
      congr 1
      funext a
      exact hc a

structure PhysicalMacroPlan (N : RootedBinary V E X) (sample : Copy → X)
    (r : PositivePairRates E) (phase : List (ProgramStep N)) (s : Code N sample) where
  inside : Finset Copy
  outside : Finset Copy
  exitPopulation : Location V E
  inside_live : inside ⊆ (state s).live
  outside_live : outside ⊆ (state s).live
  partition : inside ∪ outside = (state s).live
  separated : SeparatedAgenda N r inside outside phase s
  physical : ∀ d ∈ (sourceProgram N r phase s).support,
    PhysicalKExit N inside outside exitPopulation d

/-- Missing physical admission leaves the actual original source phase in
place. An admitted case runs its source-derived K and actual exterior source.
This total interpreter does not silently assume every Code is a real frontier. -/
noncomputable def admittedMacroRow (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (phase : List (ProgramStep N))
    (planner : (s : Code N sample) → Option (PhysicalMacroPlan N sample r phase s))
    (s : Code N sample) : PMF (Code N sample) :=
  match planner s with
  | none => sourceProgram N r phase s
  | some a => sourceKMacro N r a.inside a.outside phase s a.inside_live a.outside_live

theorem actual_admitted_macro_row (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (phase : List (ProgramStep N))
    (planner : (s : Code N sample) → Option (PhysicalMacroPlan N sample r phase s))
    (s : Code N sample) :
    (admittedMacroRow N r phase planner s).map (wholeOriginalView N) =
      (sourceProgram N r phase s).map (wholeOriginalView N) := by
  unfold admittedMacroRow
  cases h : planner s with
  | none => rfl
  | some a =>
    exact actual_source_K_macro_whole_row N r a.inside a.outside a.exitPopulation
      phase s a.inside_live a.outside_live a.partition a.separated a.physical

theorem actual_admitted_macro_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (phase : List (ProgramStep N))
    (planner : (s : Code N sample) → Option (PhysicalMacroPlan N sample r phase s))
    (s : Code N sample) {d : Code N sample}
    (hd : d ∈ (admittedMacroRow N r phase planner s).support) :
    d ∈ (sourceProgram N r phase s).support := by
  unfold admittedMacroRow at hd
  cases h : planner s with
  | none => simpa [h] using hd
  | some a =>
    exact actual_source_K_macro_support N r a.inside a.outside phase s
      a.inside_live a.outside_live a.separated (by simpa [h] using hd)

/-- Even different admissible planners/current representative choices produce
the same complete ORIGINAL quotient row when the entering causal view agrees. -/
theorem actual_macro_representation_independent (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (phase : List (ProgramStep N))
    (planner₁ planner₂ : (s : Code N sample) → Option (PhysicalMacroPlan N sample r phase s))
    (s z : Code N sample) (h : wholeOriginalView N s = wholeOriginalView N z) :
    (admittedMacroRow N r phase planner₁ s).map (wholeOriginalView N) =
      (admittedMacroRow N r phase planner₂ z).map (wholeOriginalView N) := by
  rw [actual_admitted_macro_row,actual_admitted_macro_row]
  exact actual_unranked_future_row_independent N r Finset.univ phase s z h id

structure SourceMacroStage (N : RootedBinary V E X) (sample : Copy → X)
    (r : PositivePairRates E) where
  phase : List (ProgramStep N)
  planner : (s : Code N sample) → Option (PhysicalMacroPlan N sample r phase s)

def literalProgram (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (stages : List (SourceMacroStage N sample r)) : List (ProgramStep N) :=
  stages.flatMap SourceMacroStage.phase

noncomputable def sourceMacroInterpreter (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) : List (SourceMacroStage N sample r) → Code N sample → PMF (Code N sample)
  | [],s => PMF.pure s
  | a::as,s => (admittedMacroRow N r a.phase a.planner s).bind (sourceMacroInterpreter N r as)

/-- Arbitrarily many source-derived K macros compose on the ORIGINAL Code
carrier, exposing only the complete original unranked causal view. Their whole
row equals the concatenated actual original source program, with no supplied
macro/interpreter equality and no fitted synthetic demographic parameter. -/
theorem actual_repeated_source_K_macro_interpreter (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E)
    (stages : List (SourceMacroStage N sample r)) (s : Code N sample) :
    (sourceMacroInterpreter N r stages s).map (wholeOriginalView N) =
      (sourceProgram N r (literalProgram N r stages) s).map (wholeOriginalView N) := by
  induction stages generalizing s with
  | nil => simp [sourceMacroInterpreter,literalProgram,sourceProgram]
  | cons a as ih =>
    rw [sourceMacroInterpreter,PMF.map_bind]
    simp_rw [ih]
    have h := bind_through_equal_view s (admittedMacroRow N r a.phase a.planner s)
      (sourceProgram N r a.phase s) (wholeOriginalView N)
      (actual_admitted_macro_row N r a.phase a.planner s)
      (fun d => (sourceProgram N r (literalProgram N r as) d).map (wholeOriginalView N))
      (fun d z hz => actual_unranked_future_row_independent N r Finset.univ
        (literalProgram N r as) d z hz id)
    rw [h]
    simp only [literalProgram,List.flatMap_cons]
    rw [actual_source_program_append,PMF.map_bind]

theorem actual_repeated_macro_support (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (stages : List (SourceMacroStage N sample r))
    (s : Code N sample) {d : Code N sample}
    (hd : d ∈ (sourceMacroInterpreter N r stages s).support) :
    d ∈ (sourceProgram N r (literalProgram N r stages) s).support := by
  induction stages generalizing s with
  | nil => simpa [sourceMacroInterpreter,literalProgram,sourceProgram] using hd
  | cons a as ih =>
    obtain ⟨z,hz,hd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
    simp only [literalProgram,List.flatMap_cons]
    rw [actual_source_program_append]
    exact (PMF.mem_support_bind_iff _ _ _).mpr ⟨z,actual_admitted_macro_support N r a.phase a.planner s hz,
      ih z hd⟩

#print axioms actual_macro_representation_independent
#print axioms actual_repeated_source_K_macro_interpreter
#print axioms actual_repeated_macro_support
end G1SourceMacroComposition
