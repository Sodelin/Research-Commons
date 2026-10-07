import UnifiedLean.Source.UniformizedSourceStep

/-!
UNCHECKED first typed consumer of CAUSAL-PRIVATE-REGISTER-PROJECTION.md.
CLOUD-G6-SOL-ULTRA-20261007, 7 October 2026.
Admitted SAME-graph register erasure, exact old fields and current catalogue.
This does not establish row/program/marked-history erasure or a cross-graph
carrier. No conditional law, desired kernel equation or master is assumed.
-/
namespace UnifiedLean.G6.PrivateRegisterErasure
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw
open scoped Classical

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def erasePrivateSnapshot (P : Finset V) (s : Snapshot V E Copy) :
    Snapshot V E Copy :=
  { s with register := fun v => if v ∈ P then false else s.register v }

/-- Rebuild source validity: none of its five fields reads the register. -/
theorem erasePrivateSnapshot_sourceValid (N : RootedBinary V E X)
    (sample : Copy → X) (P : Finset V) (s : Snapshot V E Copy)
    (hs : SourceValid N sample (decodeSnapshot N.root s)) :
    SourceValid N sample (decodeSnapshot N.root (erasePrivateSnapshot P s)) := by
  refine ⟨?_, ?_⟩
  · refine ⟨?_, ?_, ?_, ?_⟩
    · exact hs.forest.ancestor_live
    · exact hs.forest.representative
    · exact hs.forest.leaf_fiber
    · exact hs.forest.wellLabelled
  · exact hs.original_descendant

noncomputable def erasePrivateCode (N : RootedBinary V E X) {sample : Copy → X}
    (P : Finset V) (s : Code N sample) : Code N sample :=
  ⟨erasePrivateSnapshot P s.val,
    erasePrivateSnapshot_sourceValid N sample P s.val s.property⟩

theorem erasePrivateCode_live (N : RootedBinary V E X) {sample : Copy → X}
    (P : Finset V) (s : Code N sample) :
    (state (erasePrivateCode N P s)).live = (state s).live := rfl

theorem erasePrivateCode_ancestor (N : RootedBinary V E X) {sample : Copy → X}
    (P : Finset V) (s : Code N sample) :
    (state (erasePrivateCode N P s)).ancestor = (state s).ancestor := rfl

theorem erasePrivateCode_genealogy (N : RootedBinary V E X) {sample : Copy → X}
    (P : Finset V) (s : Code N sample) :
    (state (erasePrivateCode N P s)).genealogy = (state s).genealogy := rfl

theorem erasePrivateCode_population (N : RootedBinary V E X) {sample : Copy → X}
    (P : Finset V) (s : Code N sample) :
    (erasePrivateCode N P s).val.population = s.val.population := rfl

theorem erasePrivateCode_location (N : RootedBinary V E X) {sample : Copy → X}
    (P : Finset V) (s : Code N sample) :
    (state (erasePrivateCode N P s)).location = (state s).location := rfl

theorem erasePrivateCode_register_inside (N : RootedBinary V E X)
    {sample : Copy → X} (P : Finset V) (s : Code N sample) (v : V) (hv : v ∈ P) :
    (state (erasePrivateCode N P s)).register v = false := by
  change (if v ∈ P then false else s.val.register v) = false
  exact if_pos hv

theorem erasePrivateCode_register_outside (N : RootedBinary V E X)
    {sample : Copy → X} (P : Finset V) (s : Code N sample) (v : V) (hv : v ∉ P) :
    (state (erasePrivateCode N P s)).register v = (state s).register v := by
  change (if v ∈ P then false else s.val.register v) = s.val.register v
  exact if_neg hv

theorem erasePrivateCode_idempotent (N : RootedBinary V E X) {sample : Copy → X}
    (P : Finset V) (s : Code N sample) :
    erasePrivateCode N P (erasePrivateCode N P s) = erasePrivateCode N P s := by
  apply Subtype.ext
  apply Snapshot.ext <;> try rfl
  funext v
  by_cases hv : v ∈ P <;> simp only [erasePrivateCode, erasePrivateSnapshot,
    if_pos hv, if_neg hv]

/-- Current legal pairs use live roots/populations, whose fields are unchanged. -/
noncomputable def eraseChoiceEquiv (N : RootedBinary V E X) {sample : Copy → X}
    (P : Finset V) (s : Code N sample) :
    Choice N s ≃ Choice N (erasePrivateCode N P s) where
  toFun p := p
  invFun p := p
  left_inv _ := rfl
  right_inv _ := rfl

theorem erasePrivateCode_choiceRate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (P : Finset V) (s : Code N sample) (p : Choice N s) :
    choiceRate N r (erasePrivateCode N P s) (eraseChoiceEquiv N P s p) =
      choiceRate N r s p := rfl

theorem erasePrivateCode_totalRate (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (P : Finset V) (s : Code N sample) :
    totalRate N r (erasePrivateCode N P s) = totalRate N r s := rfl

#print axioms erasePrivateSnapshot_sourceValid
#print axioms erasePrivateCode_idempotent
#print axioms erasePrivateCode_choiceRate
#print axioms erasePrivateCode_totalRate

end UnifiedLean.G6.PrivateRegisterErasure
