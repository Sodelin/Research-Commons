import PairedGuardRouting
import G4TwoRootSourceStopping
import G1SharedRegisterStress

namespace DotG34.PairedCommonFace
open DotG34.PairedFairGuard DotG34.PairedGuardRouting G4TwoRootSourceStopping

/-- One once-drawn common bit routes every current root to the same arm. -/
noncomputable def commonNoMerger (n : ℕ) (B : PositiveBigon) : ℝ :=
  ∑ bit : Bool, GProgram.G1.registerWeight B.g bit *
    (if bit then arm B.y n else arm B.x n)

lemma common_two (B : PositiveBigon) :
    commonNoMerger 2 B = B.g*B.x+(1-B.g)*B.y := by
  simp [commonNoMerger,GProgram.G1.registerWeight,arm,Nat.choose]
  ring

lemma common_three (B : PositiveBigon) :
    commonNoMerger 3 B = B.g*B.x^3+(1-B.g)*B.y^3 := by
  simp [commonNoMerger,GProgram.G1.registerWeight,arm,Nat.choose]
  ring

lemma common_two_pos (B : PositiveBigon) : 0<commonNoMerger 2 B := by
  rw [common_two]
  have hx := B.x_positive
  have hy := B.y_positive
  have hg := B.g_positive
  have hgc : 0<1-B.g := by linarith [B.g_below_one]
  positivity

noncomputable def ratio (B : PositiveBigon) : ℝ :=
  commonNoMerger 3 B/(commonNoMerger 2 B)^3

lemma ratio_ge (B : PositiveBigon) : 1≤ratio B := by
  have hc : 0<(commonNoMerger 2 B)^3 := pow_pos (common_two_pos B) _
  unfold ratio
  apply (le_div_iff₀ hc).mpr
  rw [one_mul,common_two,common_three]
  have hx := B.x_positive
  have hy := B.y_positive
  have hg := B.g_positive
  have hgc : 0<1-B.g := by linarith [B.g_below_one]
  have hg2 : 0<2-B.g := by linarith [B.g_below_one]
  have hpos : 0≤B.g*(1-B.g)*(B.x-B.y)^2*((1+B.g)*B.x+(2-B.g)*B.y) := by positivity
  rw [← common_jensen_gap] at hpos
  linarith

lemma ratio_eq (B : PositiveBigon) : ratio B=1 ↔ B.x=B.y := by
  have hc : (commonNoMerger 2 B)^3 ≠ 0 := ne_of_gt (pow_pos (common_two_pos B) _)
  rw [ratio,div_eq_one_iff_eq hc,common_two,common_three]
  exact common_jensen_equality B.x_positive B.y_positive B.g_positive B.g_below_one

/-- Every finite positive parameter word is forced into the equal-arm face.
The remaining interface is the serial source diagonal product identity. -/
theorem common_face_forces_equal_arms (Bs : List PositiveBigon)
    (he : P (Bs.map ratio)=1) : ∀ B ∈ Bs, B.x=B.y := by
  have hall := product_one_forces_each (Bs.map ratio) (by
    intro a ha
    rcases List.mem_map.mp ha with ⟨B,hB,rfl⟩
    exact ratio_ge B) he
  intro B hB
  exact (ratio_eq B).mp (hall (ratio B) (List.mem_map.mpr ⟨B,hB,rfl⟩))

#print axioms common_face_forces_equal_arms
end DotG34.PairedCommonFace
