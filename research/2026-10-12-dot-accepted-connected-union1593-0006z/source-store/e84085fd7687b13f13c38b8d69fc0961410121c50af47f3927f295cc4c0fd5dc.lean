import G7EffectiveCoefficientSupport

/-!
# Canonical original encoding image bounds coefficient support

Contributor: Codex / lean_reuse_successor, 10 October 2026.
SourceValid of a decoded raw snapshot permits option-field garbage. This module
keeps the stronger actual encodeActual-image premise and proves that the
literal merger support preserves it. Fresh checking is required.
-/
namespace GProgram.G7.EncodedMergerSupport

open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open GProgram.G7.SinglePopulationPolynomialKernel
open GProgram.G7.EffectiveSourceEnumeration GProgram.G7.EffectivePopulationCoefficients
open GProgram.G7.EffectiveCoefficientSupport

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

def Encoded (N : RootedBinary V E X) {sample : Copy → X} (s : Code N sample) : Prop :=
  ∃ (q : State V E Copy) (hq : SourceValid N sample q), s = encodeActual N sample q hq

theorem merger_encoded (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) : Encoded N (merger N s p) := by
  unfold Encoded merger
  exact ⟨_, _, rfl⟩

theorem destinations_encoded (N : RootedBinary V E X) {sample : Copy → X}
    (fuel : Nat) (s d : Code N sample) (hs : Encoded N s)
    (hd : d ∈ destinations N fuel s) : Encoded N d := by
  induction fuel generalizing s with
  | zero =>
      have he : d = s := by simpa [destinations] using hd
      subst d
      exact hs
  | succ fuel ih =>
      by_cases hk : s.val.live.card ≤ 1
      · have he : d = s := by simpa [destinations, hk] using hd
        subst d
        exact hs
      · simp only [destinations, if_neg hk, List.mem_cons, List.mem_flatMap] at hd
        rcases hd with he | ⟨p, _, hp⟩
        · subst d
          exact hs
        · exact ih (merger N s p) (merger_encoded N s p) hp

/-- No noncanonical raw destination can carry a nonzero term from an encoded
input, even though it may satisfy SourceValid after decoding. -/
theorem coefficients_zero_of_not_encoded (N : RootedBinary V E X)
    {sample : Copy → X} (fuel : Nat) (s d : Code N sample)
    (hs : Encoded N s) (hd : ¬ Encoded N d) :
    ∀ z ∈ coefficients N fuel s d, z.2 = 0 := by
  apply coefficients_zero_of_not_mem N fuel s d
  intro hm
  exact hd (destinations_encoded N fuel s d hs hm)

theorem encoded_dead_fields (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : Encoded N s) (x : Copy) (hx : x ∉ s.val.live) :
    s.val.genealogy x = none ∧ s.val.population x = none := by
  rcases hs with ⟨q, hq, rfl⟩
  change x ∉ q.live at hx
  change (if h : x ∈ q.live then
    some (⟨q.genealogy x, hq.forest.wellLabelled x h⟩ : {g : Genealogy Copy // g.WellLabelled})
    else none) = none ∧
    (if x ∈ q.live then some (q.location x) else none) = none
  rw [dif_neg hx, if_neg hx]
  exact ⟨rfl, rfl⟩

theorem encoded_live_fields (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : Encoded N s) (x : Copy) (hx : x ∈ s.val.live) :
    (s.val.genealogy x).isSome = true ∧ (s.val.population x).isSome = true := by
  rcases hs with ⟨q, hq, rfl⟩
  change x ∈ q.live at hx
  change (if h : x ∈ q.live then
    some (⟨q.genealogy x, hq.forest.wellLabelled x h⟩ : {g : Genealogy Copy // g.WellLabelled})
    else none).isSome = true ∧
    (if x ∈ q.live then some (q.location x) else none).isSome = true
  rw [dif_pos hx, if_pos hx]
  exact ⟨rfl, rfl⟩

#print axioms coefficients_zero_of_not_encoded
#print axioms encoded_dead_fields
#print axioms encoded_live_fields

end GProgram.G7.EncodedMergerSupport
