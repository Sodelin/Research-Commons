/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No compiler/runtime/certificate.

Explicit degree-five OUTPUT-LENGTH bound for the entire total bit-to-bit
constructor, including malformed and boundary cases. Output size is not
constructor running time; no polynomial machine is supplied here.
-/
import PolytomyTargetSizeBounds

namespace PolytomyReductionModel
noncomputable section

theorem binaryBits_length_le (n : ℕ) : n.bits.length ≤ n := by
  induction n using Nat.binaryRec' with
  | zero => simp
  | bit b n hn ih =>
      rw [Nat.bits_append_bit n b hn, List.length_cons]
      by_cases h0 : n = 0
      · have hb : b = true := hn h0
        subst n
        subst b
        simp [Nat.bit]
      · cases b <;> simp only [Nat.bit, cond] <;> omega

theorem binaryNatFrame_length_le (n : ℕ) : (binaryNatFrame n).length ≤ 2 * n + 1 := by
  have h := binaryBits_length_le n
  simp only [binaryNatFrame, unaryFrame, List.length_append, List.length_replicate,
    List.length_singleton]
  omega

theorem flatMap_length_le_const {A : Type*} (xs : List A) (f : A → List Bool)
    (bound : ℕ) (h : ∀ a ∈ xs, (f a).length ≤ bound) :
    (xs.flatMap f).length ≤ xs.length * bound := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
      have ha := h a (by simp)
      have hr := ih (fun b hb => h b (by simp [hb]))
      simp only [List.flatMap_cons, List.length_append, List.length_cons]
      nlinarith

theorem canonical_block_bit_bound {N m : ℕ} (D : MSSCInstance N m) (b : Block m) :
    (treeBits (canonicalBlockTree D b)).length ≤
      (N + m * N + 3) * (cellPayloadBound N m + 2) := by
  have hl := canonicalBlockTree_leaf_bound D b
  have hv := vertexCount_add_one (canonicalBlockTree D b)
  have hb := treeBits_length_le (canonicalBlockTree D b)
  have hm := Nat.mul_le_mul_right (cellPayloadBound N m + 2) hl
  nlinarith

def targetEncodingSizeBound (N m budget : ℕ) : ℕ :=
  2 * N + 3 * m + 2 * budget + 5 +
    (m + 1) * ((N + m * N + 3) * (cellPayloadBound N m + 2))

theorem canonical_target_encoding_bound {N m : ℕ} (D : MSSCInstance N m) (budget : ℕ) :
    (encodeAnyTarget ⟨N, m, ⟨canonicalBlockTree D, budget⟩⟩).length ≤
      targetEncodingSizeBound N m budget := by
  have hN := binaryNatFrame_length_le N
  have hm := binaryNatFrame_length_le m
  have hk := binaryNatFrame_length_le budget
  have hf := flatMap_length_le_const (blockIndexList m)
    (fun b => treeBits (canonicalBlockTree D b))
    ((N + m * N + 3) * (cellPayloadBound N m + 2))
    (fun b hb => canonical_block_bit_bound D b)
  have hi : (blockIndexList m).length = m + 1 := by simp [blockIndexList]
  rw [hi] at hf
  simp only [encodeAnyTarget, encodeRawTargetRows, targetToRows, encodeFramedList,
    unaryFrame, List.length_append, List.length_replicate, List.length_singleton,
    List.length_map, List.flatMap_map, hi, targetEncodingSizeBound]
  omega

theorem canonical_any_target_encoding_bound (G : AnyBlockTarget)
    (h : CanonicalTargetBlocks G) :
    (encodeAnyTarget G).length ≤ targetEncodingSizeBound G.1 G.2.1 G.2.2.budget := by
  rcases G with ⟨N, m, G⟩
  obtain ⟨D, hb⟩ := h
  have hG : G = (⟨canonicalBlockTree D, G.budget⟩ : BlockTargetData N m) :=
    blockTargetData_eq hb rfl
  rw [hG]
  exact canonical_target_encoding_bound D G.budget

def constructionBudgetBound (N m : ℕ) : ℕ :=
  (m + 1) * ((N + m * N + 3) * (N + m * N + 3)) + m * N

def TargetBudgetBound (G : AnyBlockTarget) : Prop :=
  G.2.2.budget ≤ constructionBudgetBound G.1 G.2.1

theorem constructionBudgetBound_mono {N m N' m' : ℕ} (hN : N ≤ N') (hm : m ≤ m') :
    constructionBudgetBound N m ≤ constructionBudgetBound N' m' := by
  have hprod := Nat.mul_le_mul hm hN
  have hs : N + m * N + 3 ≤ N' + m' * N' + 3 := by omega
  have hsq := Nat.mul_le_mul hs hs
  have hmain := Nat.mul_le_mul (by omega : m + 1 ≤ m' + 1) hsq
  unfold constructionBudgetBound
  omega

theorem targetEncodingSizeBound_mono {N m k N' m' k' : ℕ}
    (hN : N ≤ N') (hm : m ≤ m') (hk : k ≤ k') :
    targetEncodingSizeBound N m k ≤ targetEncodingSizeBound N' m' k' := by
  have hprod := Nat.mul_le_mul hm hN
  have hs : N + m * N + 3 ≤ N' + m' * N' + 3 := by omega
  have hp : cellPayloadBound N m + 2 ≤ cellPayloadBound N' m' + 2 := by
    unfold cellPayloadBound
    omega
  have hinner := Nat.mul_le_mul hs hp
  have hmain := Nat.mul_le_mul (by omega : m + 1 ≤ m' + 1) hinner
  unfold targetEncodingSizeBound
  omega

theorem canonical_target_budget_bound {N m : ℕ} (D : MSSCInstance N m) (K : ℕ)
    (hK : K ≤ m * N) : TargetBudgetBound ⟨N, m, canonicalBlockTarget D K⟩ := by
  have hc := canonical_fixedCost_bound D
  unfold TargetBudgetBound constructionBudgetBound canonicalBlockTarget
  omega

theorem fixedYesTarget_budgetBound : TargetBudgetBound fixedYesTarget := by
  exact canonical_target_budget_bound fixedBoundarySource 1 (by decide)

theorem fixedNoTarget_budgetBound : TargetBudgetBound fixedNoTarget := by
  exact Nat.zero_le _

theorem totalMSSCTarget_budgetBound {N m : ℕ} (D : MSSCInstance N m) (K : ℕ) :
    TargetBudgetBound (totalMSSCTarget D K) := by
  unfold totalMSSCTarget
  split_ifs <;> first
    | exact fixedYesTarget_budgetBound
    | exact fixedNoTarget_budgetBound
    | exact canonical_target_budget_bound D K (by omega)

theorem totalRawMSSCTarget_budgetBound (R : RawMSSCRecord) :
    TargetBudgetBound (totalRawMSSCTarget R) := by
  cases hp : decodeRawMSSC R with
  | none => simpa [totalRawMSSCTarget, hp] using fixedNoTarget_budgetBound
  | some D => simpa [totalRawMSSCTarget, hp] using totalMSSCTarget_budgetBound D R.K

theorem totalSourceBitTarget_budgetBound (bits : List Bool) :
    TargetBudgetBound (totalSourceBitTarget bits) := by
  cases hp : parseRawMSSC bits with
  | none => simpa [totalSourceBitTarget, hp] using fixedNoTarget_budgetBound
  | some R => simpa [totalSourceBitTarget, hp] using totalRawMSSCTarget_budgetBound R

theorem totalMSSCTarget_dimension_upper {N m : ℕ} (D : MSSCInstance N m) (K L : ℕ)
    (hN : N ≤ L) (hm : m ≤ L) :
    (totalMSSCTarget D K).1 ≤ L + 2 ∧ (totalMSSCTarget D K).2.1 ≤ L + 2 := by
  unfold totalMSSCTarget
  split_ifs <;> simp_all [fixedYesTarget, fixedNoTarget] <;> omega

theorem totalSourceBitTarget_dimension_upper (bits : List Bool) :
    (totalSourceBitTarget bits).1 ≤ bits.length + 2 ∧
      (totalSourceBitTarget bits).2.1 ≤ bits.length + 2 := by
  cases hp : parseRawMSSC bits with
  | none => simp [totalSourceBitTarget, hp, fixedNoTarget]
  | some R =>
      cases hd : decodeRawMSSC R with
      | none => simp [totalSourceBitTarget, hp, totalRawMSSCTarget, hd, fixedNoTarget]
      | some D =>
          have hv : RawMSSCValid R := (decodeRawMSSC_success_iff R).mp ⟨D, hd⟩
          have hb := parsed_valid_dimensions_bounded bits R hp hv
          simpa [totalSourceBitTarget, hp, totalRawMSSCTarget, hd] using
            totalMSSCTarget_dimension_upper D R.K bits.length hb.1 hb.2.2

def sourceOutputSizeBound (L : ℕ) : ℕ :=
  targetEncodingSizeBound (L + 2) (L + 2) (constructionBudgetBound (L + 2) (L + 2))

theorem sourceOutputSizeBound_polynomial (L : ℕ) :
    sourceOutputSizeBound L =
      3 * (L + 2)^5 + 10 * (L + 2)^4 + 32 * (L + 2)^3 +
        51 * (L + 2)^2 + 65 * (L + 2) + 41 := by
  unfold sourceOutputSizeBound targetEncodingSizeBound constructionBudgetBound cellPayloadBound
  ring

/-- Every source string, including malformed input with huge numeric
    declarations, has an output bounded by the SAME explicit polynomial. -/
theorem encodedSourceToTarget_length_bound (input : List Bool) :
    (encodedSourceToTarget input).length ≤ sourceOutputSizeBound input.length := by
  have he := canonical_any_target_encoding_bound (totalSourceBitTarget input)
    (totalSourceBitTarget_canonical input)
  obtain ⟨hN, hm⟩ := totalSourceBitTarget_dimension_upper input
  have hk0 : (totalSourceBitTarget input).2.2.budget ≤
      constructionBudgetBound (totalSourceBitTarget input).1 (totalSourceBitTarget input).2.1 :=
    totalSourceBitTarget_budgetBound input
  have hk := hk0.trans (constructionBudgetBound_mono hN hm)
  exact he.trans (targetEncodingSizeBound_mono hN hm hk)

/-- Complete finite correctness, explicit output size and independent
    bounded certificates together. No machine running-time claim is made. -/
theorem full_encoded_reduction_with_size (input : List Bool) (lambda : ℝ) :
    (encodedSourceToTarget input).length ≤ sourceOutputSizeBound input.length ∧
      (SourceBitMSSCDecision input ↔
        EncodedTargetCartaDecision (encodedSourceToTarget input) lambda) ∧
      (EncodedTargetCartaDecision (encodedSourceToTarget input) lambda ↔
        ∃ cert : List Bool,
          cert.length ≤ targetBitCertificateBound (encodedSourceToTarget input).length ∧
          checkEncodedTarget (encodedSourceToTarget input) cert = true) := by
  exact ⟨encodedSourceToTarget_length_bound input,
    full_encoded_source_actual_reduction input lambda,
    encoded_target_actual_iff_bounded (encodedSourceToTarget input) lambda⟩

/- Remaining: concrete total polynomial constructor/verifier MACHINE proofs,
compatible formal source hardness and composition, and all elaboration.
No output-size theorem alone proves polynomial computation time. -/

end
end PolytomyReductionModel
