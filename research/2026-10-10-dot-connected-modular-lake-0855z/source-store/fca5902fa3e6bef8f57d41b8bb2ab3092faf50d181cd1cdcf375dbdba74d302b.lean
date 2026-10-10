import G7BoundaryRelabelling
import UnifiedLean.Source.SourcePoissonKernel

/-!
Actual uniformized source clock/merger step under original graph bijections.
Contributor: dot, 2026-10-09. Rates, current roots and merger destinations are
transported from the existing source constructors, not assumed equal.
-/
namespace GProgram.G7.SourceStepRelabelling
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanPopulationProjection
open GProgram.G7.OriginalRelabelling
open GProgram.G7.SnapshotRelabelling
open GProgram.G7.BoundaryRelabelling
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel
open scoped Classical BigOperators
variable {V E W F Copy X : Type*}
variable [Fintype V] [Fintype E] [Fintype W] [Fintype F] [Fintype X]
variable [DecidableEq V] [DecidableEq W] [DecidableEq E] [DecidableEq F]
variable [Fintype Copy] [DecidableEq Copy]

@[simp] theorem pair_rate (e : E ≃ F) (r : PositivePairRates E) (i : Option E) :
    pairRate (rates e r) ((Equiv.optionCongr e) i) = pairRate r i := by
  cases i <;> simp [rates,pairRate]

@[simp] theorem place (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F) (i : Option E) :
    originalPlace (network N v e) ((Equiv.optionCongr e) i) =
      GProgram.G7.SourceStateRelabelling.location v e (originalPlace N i) := by
  cases i <;> rfl

theorem roots (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (s : Code N sample) (i : Option E) :
    populationRoots (state (code N v e s)) (originalPlace (network N v e) ((Equiv.optionCongr e) i)) =
      populationRoots (state s) (originalPlace N i) := by
  rw [code_state,place]
  ext l
  simp [populationRoots,GProgram.G7.SourceStateRelabelling.state]

noncomputable def choices (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (s : Code N sample) : Choice N s ≃ Choice (network N v e) (code N v e s) :=
  Equiv.sigmaCongr (Equiv.optionCongr e) (fun i =>
    Equiv.subtypeEquivRight (fun p => by rw [roots]))

@[simp] theorem choice_place (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (s : Code N sample) (p : Choice N s) :
    (choices N v e s p).1 = (Equiv.optionCongr e) p.1 := rfl
@[simp] theorem choice_pair (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (s : Code N sample) (p : Choice N s) :
    (choices N v e s p).2.val = p.2.val := rfl

@[simp] theorem choice_rate (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (p : Choice N s) :
    choiceRate (network N v e) (rates e r) (code N v e s) (choices N v e s p) = choiceRate N r s p := by
  simp only [choiceRate,choice_place,pair_rate]

@[simp] theorem total_rate (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) :
    totalRate (network N v e) (rates e r) (code N v e s) = totalRate N r s := by
  unfold totalRate
  symm
  apply Fintype.sum_equiv (choices N v e s)
  intro p
  exact (choice_rate N v e r s p).symm

@[simp] theorem global_rate (e : E ≃ F) (r : PositivePairRates E) :
    globalRateBound (Copy:=Copy) (rates e r) = globalRateBound (Copy:=Copy) r := by
  have hs : (∑ i : Option E, pairRate r i) = ∑ j : Option F, pairRate (rates e r) j := by
    apply Fintype.sum_equiv (Equiv.optionCongr e)
    intro i
    exact (pair_rate e r i).symm
  simp only [globalRateBound,hs]

@[simp] theorem choice_mass (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) (p : Option (Choice N s)) :
    choiceMass (network N v e) (rates e r) (code N v e s)
      ((Equiv.optionCongr (choices N v e s)) p) = choiceMass N r s p := by
  cases p <;> simp [choiceMass]

lemma pmf_map_equiv_apply {A B : Type*} (q : A ≃ B) (p : PMF A) (a : A) :
    (p.map q) (q a) = p a := by
  simp [PMF.map_apply]

theorem choice_pmf (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) :
    (choicePMF N r s).map (Equiv.optionCongr (choices N v e s)) =
      choicePMF (network N v e) (rates e r) (code N v e s) := by
  apply PMF.ext
  intro b
  obtain ⟨a,rfl⟩ := (Equiv.optionCongr (choices N v e s)).surjective b
  rw [pmf_map_equiv_apply]
  change ENNReal.ofReal (choiceMass N r s a) = ENNReal.ofReal (choiceMass (network N v e) (rates e r) (code N v e s) ((Equiv.optionCongr (choices N v e s)) a))
  rw [choice_mass]

theorem destination (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (s : Code N sample) (p : Option (Choice N s)) :
    code N v e (stepDestination N s p) =
      stepDestination (network N v e) (code N v e s) ((Equiv.optionCongr (choices N v e s)) p) := by
  cases p with
  | none => rfl
  | some p =>
    simp only [Equiv.optionCongr,Equiv.coe_fn_mk,Option.map_some,stepDestination]
    rw [admittedCode_commutes]
    apply admitted_congr
    change GProgram.G7.SourceStateRelabelling.state v e (merge (state s) p.2.val.1 p.2.val.2) = merge (state (code N v e s)) p.2.val.1 p.2.val.2
    rw [code_state]
    exact GProgram.G7.SourceStateRelabelling.merge_commutes v e (state s) p.2.val.1 p.2.val.2

/-- Full normalized holding-or-merger row equality on the genuine source
snapshot. Every retained old genealogy follows the transported destination. -/
theorem source_step (N : RootedBinary V E X) (v : V ≃ W) (e : E ≃ F)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample) :
    (sourceStep N r s).map (code N v e) =
      sourceStep (network N v e) (rates e r) (code N v e s) := by
  unfold sourceStep
  rw [PMF.map_comp]
  have hf : (code N v e ∘ stepDestination N s) =
      stepDestination (network N v e) (code N v e s) ∘ Equiv.optionCongr (choices N v e s) := by
    funext p
    exact destination N v e s p
  rw [hf,← PMF.map_comp,choice_pmf]

#print axioms roots
#print axioms choice_pmf
#print axioms source_step
end GProgram.G7.SourceStepRelabelling
