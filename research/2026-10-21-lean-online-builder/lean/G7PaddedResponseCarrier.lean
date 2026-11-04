import G7ExactLawResourceGame

/-!
Finite response-carrier adapter for the retained exact-law game. Padding adds
only fixed zero coordinates. It does not add an observation, source row,
resource cost, Rust output field or native AST/refinement theorem.
-/
namespace Astra.G7PaddedResponseCarrier

open GProgram.G7.ExactLawResourceGame

def pad {n : Nat} (K : Nat) (y : Fin n → ℝ) : Fin K → ℝ :=
  fun i => if hi : i.val < n then y ⟨i.val,hi⟩ else 0

def restrict {n K : Nat} (hn : n ≤ K) (z : Fin K → ℝ) : Fin n → ℝ :=
  fun i => z ⟨i.val,lt_of_lt_of_le i.isLt hn⟩

theorem pad_outside {n K : Nat} (y : Fin n → ℝ) (i : Fin K)
    (hi : n ≤ i.val) : pad K y i = 0 := by
  simp [pad,Nat.not_lt.mpr hi]

theorem restrict_pad {n K : Nat} (hn : n ≤ K) (y : Fin n → ℝ) :
    restrict hn (pad K y) = y := by
  funext i
  simp [restrict,pad,i.isLt]

theorem pad_restrict {n K : Nat} (hn : n ≤ K) (z : Fin K → ℝ)
    (hz : ∀ i, n ≤ i.val → z i = 0) : pad K (restrict hn z) = z := by
  funext i
  by_cases hi : i.val < n
  · simp [pad,restrict,hi]
  · simp [pad,hi,hz i (Nat.le_of_not_gt hi)]

theorem pad_add {n K : Nat} (x y : Fin n → ℝ) :
    pad K (fun i => x i+y i) = fun i => pad K x i+pad K y i := by
  funext i
  by_cases hi : i.val < n <;> simp [pad,hi]

theorem pad_smul {n K : Nat} (c : ℝ) (x : Fin n → ℝ) :
    pad K (fun i => c*x i) = fun i => c*pad K x i := by
  funext i
  by_cases hi : i.val < n <;> simp [pad,hi]

theorem pad_zero_outputs (K : Nat) (y : Fin 0 → ℝ) : pad K y = 0 := by
  funext i
  simp [pad]

/-- All padded replies are quantified. Replies outside the zero-padding
image may be removed only after proving the continuation holds there. -/
theorem forall_replies_iff {n K : Nat} (hn : n ≤ K)
    (P : (Fin K → ℝ) → Prop)
    (outside : ∀ z, (∃ i : Fin K, n ≤ i.val ∧ z i ≠ 0) → P z) :
    (∀ z, P z) ↔ ∀ y : Fin n → ℝ, P (pad K y) := by
  constructor
  · intro h y; exact h (pad K y)
  · intro h z
    by_cases hz : ∀ i : Fin K, n ≤ i.val → z i = 0
    · rw [← pad_restrict hn z hz]
      exact h (restrict hn z)
    · apply outside z
      by_contra hnone
      apply hz
      intro i hi
      by_contra hzero
      exact hnone ⟨i,hi,hzero⟩

variable {S A T R : Type*}

theorem inconsistent_nonzero_padding {n K : Nat}
    (E : Experiment S A (Fin K → ℝ) T R) (a : A) (h : History A (Fin K → ℝ))
    (zero_response : ∀ s (i : Fin K), n ≤ i.val → E.response s a i = 0)
    (z : Fin K → ℝ) (bad : ∃ i : Fin K, n ≤ i.val ∧ z i ≠ 0) :
    ∀ s, ¬ Consistent E ((a,z)::h) s := by
  intro s hs
  obtain ⟨i,hi,hnz⟩ := bad
  have he := (consistent_extend E h s a z).mp hs
  exact hnz ((congrFun he.2 i).symm.trans (zero_response s i hi))

/-- Impossible padded replies have an empty consistent-source set and hence
are homogeneous at EVERY horizon, without physical source selection. -/
theorem impossible_padding_winning {n K : Nat}
    (E : Experiment S A (Fin K → ℝ) T R) (a : A) (h : History A (Fin K → ℝ))
    (zero_response : ∀ s (i : Fin K), n ≤ i.val → E.response s a i = 0)
    (z : Fin K → ℝ) (bad : ∃ i : Fin K, n ≤ i.val ∧ z i ≠ 0)
    (k : Nat) (u : R) : Winning E k ((a,z)::h) u := by
  have empty := inconsistent_nonzero_padding E a h zero_response z bad
  have homogeneous : Homogeneous E ((a,z)::h) :=
    fun s _ hs _ => (empty s hs).elim
  cases k with
  | zero => exact homogeneous
  | succ k => exact Or.inl homogeneous

/-- This is the response-quantifier obligation for one case with n outputs
inside a fixed Fin K carrier. Active coordinate order is unchanged. -/
theorem winning_reply_quantifier_iff {n K : Nat} (hn : n ≤ K)
    (E : Experiment S A (Fin K → ℝ) T R) (a : A) (h : History A (Fin K → ℝ))
    (zero_response : ∀ s (i : Fin K), n ≤ i.val → E.response s a i = 0)
    (k : Nat) (u : R) :
    (∀ z : Fin K → ℝ, Winning E k ((a,z)::h) u) ↔
      ∀ y : Fin n → ℝ, Winning E k ((a,pad K y)::h) u := by
  apply forall_replies_iff hn
  intro z bad
  exact impossible_padding_winning E a h zero_response z bad k u

end Astra.G7PaddedResponseCarrier
