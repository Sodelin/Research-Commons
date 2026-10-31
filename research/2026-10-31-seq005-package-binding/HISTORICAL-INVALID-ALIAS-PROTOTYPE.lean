import SamuelAlexanderResearch.FiniteEditOptimum

/-! Existing CB-SEQ-005 owner/type correspondence, not yet adopted.
Original Samuel source proofs and definitions are retained. The finite cutoff
is a location bound, not a count of edits or a practical complexity guarantee.
This is an exact Lean interface, not a native Rust implementation. -/
namespace ResearchCommons.Claims.FiniteEditOptimum
open FiniteEditStability FiniteEditAlgorithm

 theorem actual_height := FiniteEditExact.height_isMaximum
 theorem cutoff_formula (m : Nat) : cutoff m = 3*2^(m+3)+m := rfl

/-- The finite maximum includes exactly every positive start through N(m). -/
theorem finite_maximum (s : Nat → Bool) (m : Nat) :
    (∀ v, 1 ≤ v → v ≤ cutoff m →
      residual s m v ≤ best s m (cutoff m-1)) ∧
    ∃ v, 1 ≤ v ∧ v ≤ cutoff m ∧
      residual s m v = best s m (cutoff m-1) := by
  have hc := cutoff_pos m
  constructor
  · intro v hv hn
    exact residual_le_best s m (cutoff m-1) v hv (by omega)
  · obtain ⟨v,hv,hn,he⟩ := best_attained s m (cutoff m-1)
    exact ⟨v,hv,by omega,he⟩

 theorem global_optimum := _root_.FiniteEditOptimum.individual_optimum_attained
 theorem integer_allowance_iff := _root_.FiniteEditOptimum.individual_additive_constant_iff

/-- The integer allowance retains the unedited value minus one at m=0. -/
theorem allowance_bounds (s : Nat → Bool) (m : Nat)
    (hag : AgreeFrom s ThueMorseBits.t m) :
    -1 ≤ best s m (cutoff m-1) ∧ best s m (cutoff m-1) ≤ 8*(m : Int)-1 := by
  refine ⟨best_at_cutoff_ge_neg_one s m hag, ?_⟩
  apply (_root_.FiniteEditOptimum.individual_additive_constant_iff s m hag _).mp
  exact ((FiniteEditExact.optimal_universal_additive_constant m (8*(m : Int)-1)).mpr
    (le_refl _)) s hag

 theorem maximum_iff_actual_height := FiniteEditExact.maximum_iff_height
end ResearchCommons.Claims.FiniteEditOptimum
