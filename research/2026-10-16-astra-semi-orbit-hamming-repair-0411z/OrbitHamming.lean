import Semi.Core.FiniteOrbit
import Semi.Diffraction.FourierIntensity

/-! Normalized orbit-Hamming loss on ALL source orbits of the declared cyclic
symmetry group. SOURCE CANDIDATE. Observation fibres and symmetry orbits are
different objects; the former are not used to restrict the action space. -/

namespace Semi.Diffraction

variable {N : ℕ} [NeZero N]

noncomputable def orbitGeometry (N : ℕ) [NeZero N] :
    Semi.Core.FiniteOrbitGeometry (symmetries N) (Configuration N) where
  action := (symmetries N).subtype
  distance := hammingDist
  self := hammingDist_self
  symmetric := hammingDist_comm
  triangle := hammingDist_triangle
  eq_zero := fun _ _ => hammingDist_eq_zero
  invariant := symmetry_preserves_hamming

abbrev SourceOrbit (N : ℕ) [NeZero N] := Quotient (orbitGeometry N).orbitSetoid

noncomputable instance sourceOrbitFintype : Fintype (SourceOrbit N) := Fintype.ofFinite _
instance sourceOrbitNonempty : Nonempty (SourceOrbit N) :=
  ⟨Quotient.mk _ (fun _ => false)⟩

noncomputable def sourceOrbit (x : Configuration N) : SourceOrbit N := Quotient.mk _ x

theorem orbitDistance_le_size (x y : Configuration N) :
    (orbitGeometry N).orbitDistance x y ≤ N := by
  exact ((orbitGeometry N).orbitDistance_le_distance x y).trans
    (by simpa [orbitGeometry, ZMod.card] using (hammingDist_le_card_fintype (x := x) (y := y)))

theorem quotientDistance_le_size (a b : SourceOrbit N) :
    (orbitGeometry N).quotientDistance a b ≤ N := by
  refine Quotient.inductionOn₂ a b (fun x y => ?_)
  exact orbitDistance_le_size x y

noncomputable def orbitMetric (a b : SourceOrbit N) : ℝ :=
  ((orbitGeometry N).quotientDistance a b : ℝ) / (N : ℝ)

theorem size_pos : 0 < (N : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne N))

theorem orbitMetric_nonneg (a b : SourceOrbit N) : 0 ≤ orbitMetric a b :=
  div_nonneg (Nat.cast_nonneg _) (le_of_lt size_pos)

theorem orbitMetric_le_one (a b : SourceOrbit N) : orbitMetric a b ≤ 1 := by
  apply (div_le_one size_pos).2
  exact Nat.cast_le.mpr (quotientDistance_le_size a b)

@[simp] theorem orbitMetric_self (a : SourceOrbit N) : orbitMetric a a = 0 := by
  simp [orbitMetric]

theorem orbitMetric_comm (a b : SourceOrbit N) : orbitMetric a b = orbitMetric b a := by
  rw [orbitMetric, orbitMetric, (orbitGeometry N).quotientDistance_comm]

theorem orbitMetric_triangle (a b c : SourceOrbit N) :
    orbitMetric a c ≤ orbitMetric a b + orbitMetric b c := by
  have h : ((orbitGeometry N).quotientDistance a c : ℝ) ≤
      (orbitGeometry N).quotientDistance a b + (orbitGeometry N).quotientDistance b c := by
    simpa only [Nat.cast_add] using
      (Nat.cast_le (α := ℝ)).mpr ((orbitGeometry N).quotientDistance_triangle a b c)
  simpa only [orbitMetric, add_div] using (div_le_div_of_nonneg_right h (le_of_lt size_pos))

@[simp] theorem orbitMetric_eq_zero (a b : SourceOrbit N) : orbitMetric a b = 0 ↔ a = b := by
  simp [orbitMetric, div_eq_zero_iff, ne_of_gt (size_pos (N := N)),
    (orbitGeometry N).quotientDistance_eq_zero]

noncomputable def orbitLoss (a : SourceOrbit N) (x : Configuration N) : ℝ :=
  orbitMetric a (sourceOrbit x)

theorem orbitLoss_pair_bound (a : SourceOrbit N) (x y : Configuration N) :
    orbitMetric (sourceOrbit x) (sourceOrbit y) ≤ orbitLoss a x + orbitLoss a y := by
  simpa only [orbitLoss, orbitMetric_comm (sourceOrbit x) a] using
    orbitMetric_triangle (sourceOrbit x) a (sourceOrbit y)

/-- Labelled intensity is invariant on the declared source orbits. It is not
asserted to distinguish those orbits. -/
noncomputable def orbitIntensity : SourceOrbit N → Grid N → ℝ :=
  Quotient.lift intensity (by
    intro x y hxy
    obtain ⟨g, hg⟩ := hxy
    change g.1 x = y at hg
    rw [← hg]
    exact (intensity_symmetry g x).symm)

end Semi.Diffraction
