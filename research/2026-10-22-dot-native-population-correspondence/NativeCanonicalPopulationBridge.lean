import G7EffectivePopulationCoefficients

/-!
Contributor: dot, 2026-10-22. SOURCE PROPOSAL, UNELABORATED.
No native, Lean, Lake, CI or backend execution has occurred for this source.
This is the canonical-state part of the native population correspondence,
not a Rust operational-semantics or whole-provider verification.
The original Code carrier is NOT restricted or replaced.
-/

namespace Dot.NativeCanonicalPopulationBridge

open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open GProgram.G7.EffectiveSourceEnumeration
open GProgram.G7.EffectivePopulationCoefficients
open GProgram.G7.SinglePopulationPolynomialKernel

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

/-- Exactly the live/dead option discipline checked by validate_snapshot.
This is stronger than the original admitted Code's SourceValid predicate. -/
def Canonical (s : Snapshot V E Copy) : Prop :=
  (∀ l ∈ s.live, s.genealogy l ≠ none ∧ s.population l ≠ none) ∧
  (∀ l ∉ s.live, s.genealogy l = none ∧ s.population l = none)

theorem encode_canonical (s : State V E Copy) (hs : Valid s) :
    Canonical (encode s hs) := by
  constructor
  · intro l hl
    simp [encode, hl]
  · intro l hl
    simp [encode, hl]

/-- All fields, not merely the observed selected view, survive the round trip.
No equation is asserted for a noncanonical admitted snapshot. -/
theorem encode_decode_of_canonical (root : V) (s : Snapshot V E Copy)
    (hs : Valid (decode root s)) (hc : Canonical s) :
    encode (decode root s) hs = s := by
  apply Snapshot.ext
  · rfl
  · rfl
  · funext l
    by_cases hl : l ∈ s.live
    · obtain ⟨hgene, _⟩ := hc.1 l hl
      cases hg : s.genealogy l with
      | none => exact False.elim (hgene hg)
      | some t => simp [encode, decode, hl, hg]
    · simp [encode, decode, hl, (hc.2 l hl).1]
  · funext l
    by_cases hl : l ∈ s.live
    · obtain ⟨_, hpop⟩ := hc.1 l hl
      cases hp : s.population l with
      | none => exact False.elim (hpop hp)
      | some p => simp [encode, decode, hl, hp]
    · simp [encode, decode, hl, (hc.2 l hl).2]
  · rfl

theorem merger_canonical (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) :
    Canonical (merger N s p).val := by
  exact encode_canonical _ _

/-- Stronger than a polynomial-zero conclusion: every raw rational term to
a noncanonical destination is zero. Hence list duplication/cancellation and
the native omission of zero terms cannot create a missing destination mass. -/
theorem coefficients_noncanonical_zero_terms (N : RootedBinary V E X)
    {sample : Copy → X} (fuel : Nat) (s d : Code N sample)
    (hs : Canonical s.val) (hd : ¬ Canonical d.val) :
    ∀ z ∈ coefficients N fuel s d, z.2 = 0 := by
  induction fuel generalizing s with
  | zero =>
      have hsd : s ≠ d := fun h => hd (h ▸ hs)
      simp [coefficients, hsd]
  | succ fuel ih =>
      have hsd : s ≠ d := fun h => hd (h ▸ hs)
      by_cases hk : s.val.live.card ≤ 1
      · simp [coefficients, hk, hsd]
      · intro z hz
        simp only [coefficients, if_neg hk, List.mem_append,
          List.mem_cons, List.not_mem_nil, or_false] at hz
        rcases hz with hz | hz
        · subst z
          simp [hsd]
        · obtain ⟨p, _, hz⟩ := List.mem_flatMap.mp hz
          obtain ⟨w, hw, hz⟩ := List.mem_flatMap.mp hz
          have hwzero := ih (merger N s p) (merger_canonical N s p) w hw
          simp only [liftTerm, List.mem_cons, List.not_mem_nil, or_false] at hz
          rcases hz with hz | hz
          · subst z
            simp [hwzero]
          · subst z
            simp [hwzero]

theorem exprPolynomial_zero_of_zero_terms (p : Expr)
    (hp : ∀ z ∈ p, z.2 = 0) : exprPolynomial p = 0 := by
  induction p with
  | nil => rfl
  | cons z p ih =>
      rw [exprPolynomial_cons, hp z (by simp), Polynomial.C_0, zero_mul,
        zero_add]
      exact ih (fun w hw => hp w (by simp [hw]))

/-- Total destination statement on the ORIGINAL Code carrier. This avoids
the false demand that canonical native snapshots enumerate every Code. -/
theorem coefficients_noncanonical_zero (N : RootedBinary V E X)
    {sample : Copy → X} (fuel : Nat) (s d : Code N sample)
    (hs : Canonical s.val) (hd : ¬ Canonical d.val) :
    exprPolynomial (coefficients N fuel s d) = 0 :=
  exprPolynomial_zero_of_zero_terms _
    (coefficients_noncanonical_zero_terms N fuel s d hs hd)

end Dot.NativeCanonicalPopulationBridge
