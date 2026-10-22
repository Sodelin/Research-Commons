import RootBlobEdgeIndexedInterfaces

/-!
# Open-equivariant root-blob proof layer

Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY: every proof term below is UNELABORATED. No Lean or scientific
runtime was run. No declaration is being advertised as Lean-verified.

Read-only API reference: mathlib commit
0df444a360eaa60ab8c11dca51a86af692955474, Lean v4.33.1.
The prior interface modules are the immutable versions listed in
SOURCE-PROOF-PROGRESS.md. This file adds genuine proof terms, not axioms.

The final theorem is explicitly conditional on a graph-resolution formula
and source-law soundness. Those semantic obligations are NOT supplied by
this file and must not be erased from the theorem's acceptance statement.
The full graph class, original edges and fixed inheritance weights remain
the ones in RootBlobEdgeIndexed.
-/

open scoped BigOperators Topology
open RootBlobInterfaces
namespace RootBlobOpenProof

universe u v w x
variable {S : Type u} [Fintype S]

noncomputable def secondMarginal (P : Mat S) (j : S) : ℝ := ∑ i, P i j

noncomputable def conditional (P : Mat S) : Mat S :=
  fun j i => P i j / secondMarginal P j

noncomputable def rowAction (μ : S → ℝ) (M : Mat S) (i : S) : ℝ :=
  ∑ j, μ j * M j i

noncomputable def compensate (M : Mat S) (ν : S → ℝ) (c : ℝ) : Mat S :=
  fun j i => (M j i - (1 - c) * ν i) / c

noncomputable def equalInput (μ : S → ℝ) (t : ℝ) : Mat S := by
  classical
  exact fun i j => (if i = j then t else 0) + (1 - t) * μ j

/-- Entry formula for (E_μ(c) A)^T D_μ, without commuting A and E_μ. -/
noncomputable def blendPair (μ : S → ℝ) (c : ℝ) (A : Mat S) : Mat S :=
  fun i j => μ j * (c * A j i + (1 - c) * rowAction μ A i)

theorem sum_divide {I : Type v} [Fintype I] (f : I → ℝ) (c : ℝ) :
    (∑ i, f i / c) = (∑ i, f i) / c := by
  simp only [div_eq_mul_inv, Finset.sum_mul]

theorem marginal_positive [Nonempty S] {P : Mat S}
    (hP : ∀ i j, 0 < P i j) (j : S) : 0 < secondMarginal P j := by
  classical
  exact Finset.sum_pos (fun i _ => hP i j) Finset.univ_nonempty

theorem marginal_total {P : Mat S} (hP : (∑ i, ∑ j, P i j) = 1) :
    (∑ j, secondMarginal P j) = 1 := by
  unfold secondMarginal
  rw [Finset.sum_comm]
  exact hP

theorem marginal_invariant {P : Mat S} {H : Subgroup (Equiv.Perm S)}
    (hP : Equivariant H P) : Invariant H (secondMarginal P) := by
  classical
  intro h j
  unfold secondMarginal
  calc
    (∑ i, P i (h.val j)) = ∑ i, P (h.val i) (h.val j) :=
      (h.val.sum_comp (fun i => P i (h.val j))).symm
    _ = ∑ i, P i j := Finset.sum_congr rfl (fun i _ => hP h i j)

theorem conditional_open [Nonempty S] {P : Mat S}
    {H : Subgroup (Equiv.Perm S)} (hP : PositiveInvariantPair H P) :
    OpenTransition H (conditional P) := by
  classical
  have hμ := marginal_positive hP.1
  have hμinv := marginal_invariant hP.2.2
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro j i
    exact div_pos (hP.1 i j) (hμ j)
  · intro j
    change (∑ i, P i j / secondMarginal P j) = 1
    rw [sum_divide]
    exact div_self (ne_of_gt (hμ j))
  · intro h j i
    change P (h.val i) (h.val j) / secondMarginal P (h.val j) =
      P i j / secondMarginal P j
    rw [hP.2.2 h i j, hμinv h j]

theorem marginal_root [Nonempty S] {P : Mat S}
    {H : Subgroup (Equiv.Perm S)} (hP : PositiveInvariantPair H P) :
    RootAdmitted H (secondMarginal P) := by
  exact ⟨⟨fun j => le_of_lt (marginal_positive hP.1 j),
    marginal_total hP.2.1⟩, marginal_invariant hP.2.2⟩

theorem conditional_reconstruct [Nonempty S] {P : Mat S}
    (hP : ∀ i j, 0 < P i j) (i j : S) :
    secondMarginal P j * conditional P j i = P i j := by
  unfold conditional
  field_simp [ne_of_gt (marginal_positive hP j)] <;> ring

theorem rowAction_total {μ : S → ℝ} {M : Mat S}
    (hμ : (∑ i, μ i) = 1) (hM : ∀ i, (∑ j, M i j) = 1) :
    (∑ j, rowAction μ M j) = 1 := by
  unfold rowAction
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, hM, mul_one]
  exact hμ

theorem rowAction_invariant {μ : S → ℝ} {M : Mat S}
    {H : Subgroup (Equiv.Perm S)}
    (hμ : Invariant H μ) (hM : Equivariant H M) :
    Invariant H (rowAction μ M) := by
  classical
  intro h i
  unfold rowAction
  calc
    (∑ j, μ j * M j (h.val i)) =
        ∑ j, μ (h.val j) * M (h.val j) (h.val i) :=
      (h.val.sum_comp (fun j => μ j * M j (h.val i))).symm
    _ = ∑ j, μ j * M j i := by
      apply Finset.sum_congr rfl
      intro j _
      rw [hμ h j, hM h j i]

theorem compensate_rows {M : Mat S} {ν : S → ℝ} {c : ℝ}
    (hM : ∀ i, (∑ j, M i j) = 1) (hν : (∑ j, ν j) = 1)
    (hc : c ≠ 0) : ∀ i, (∑ j, compensate M ν c i j) = 1 := by
  intro i
  unfold compensate
  rw [sum_divide, Finset.sum_sub_distrib, ← Finset.mul_sum, hM i, hν]
  field_simp [hc] <;> ring

theorem compensate_invariant {M : Mat S} {ν : S → ℝ} {c : ℝ}
    {H : Subgroup (Equiv.Perm S)}
    (hM : Equivariant H M) (hν : Invariant H ν) :
    Equivariant H (compensate M ν c) := by
  intro h j i
  unfold compensate
  rw [hM h j i, hν h i]

theorem compensate_transport {μ : S → ℝ} {M : Mat S} {c : ℝ}
    (hμ : (∑ i, μ i) = 1) (hc : c ≠ 0) :
    rowAction μ (compensate M (rowAction μ M) c) = rowAction μ M := by
  funext j
  let ν := rowAction μ M
  change (∑ i, μ i * ((M i j - (1 - c) * ν j) / c)) = ν j
  have ht : ∀ i, μ i * ((M i j - (1 - c) * ν j) / c) =
      (μ i * M i j) / c - ((1 - c) * ν j / c) * μ i := by
    intro i
    field_simp [hc] <;> ring
  simp_rw [ht]
  rw [Finset.sum_sub_distrib, sum_divide, ← Finset.mul_sum, hμ]
  change ν j / c - ((1 - c) * ν j / c) * 1 = ν j
  field_simp [hc] <;> ring

theorem compensate_blend {μ : S → ℝ} {M : Mat S} {c : ℝ}
    (hμ : (∑ i, μ i) = 1) (hc : c ≠ 0) :
    blendPair μ c (compensate M (rowAction μ M) c) =
      fun i j => μ j * M j i := by
  funext i j
  unfold blendPair
  rw [compensate_transport hμ hc]
  unfold compensate
  field_simp [hc] <;> ring

theorem equalInput_open {μ : S → ℝ} {t : ℝ}
    {H : Subgroup (Equiv.Perm S)}
    (hμ : RootAdmitted H μ) (hμpos : ∀ i, 0 < μ i)
    (ht0 : 0 < t) (ht1 : t < 1) : OpenTransition H (equalInput μ t) := by
  classical
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i j
    unfold equalInput
    have hp : 0 < (1 - t) * μ j := mul_pos (sub_pos.mpr ht1) (hμpos j)
    split_ifs <;> linarith
  · intro i
    unfold equalInput
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hμ.1.2]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring
  · intro h i j
    have heq : (h.val i = h.val j) ↔ i = j := h.val.injective.eq_iff
    simp only [equalInput, heq, hμ.2 h j]


theorem equalInput_mul (μ : S → ℝ) (c : ℝ) (A : Mat S) (i j : S) :
    matMul (equalInput μ c) A i j =
      c * A i j + (1 - c) * rowAction μ A j := by
  classical
  change (∑ k, ((if i = k then c else 0) + (1 - c) * μ k) * A k j) = _
  have ht : ∀ k, ((if i = k then c else 0) + (1 - c) * μ k) * A k j =
      (if i = k then c * A k j else 0) + (1 - c) * (μ k * A k j) := by
    intro k
    split_ifs <;> ring
  simp_rw [ht]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq,
    if_pos (Finset.mem_univ i), ← Finset.mul_sum]
  rfl

theorem rowAction_equalInput {μ : S → ℝ} (hμ : (∑ i, μ i) = 1) (t : ℝ) :
    rowAction μ (equalInput μ t) = μ := by
  classical
  funext j
  change (∑ k, μ k * ((if k = j then t else 0) + (1 - t) * μ j)) = μ j
  have ht : ∀ k, μ k * ((if k = j then t else 0) + (1 - t) * μ j) =
      (if k = j then μ k * t else 0) + μ k * ((1 - t) * μ j) := by
    intro k
    split_ifs <;> ring
  simp_rw [ht]
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq',
    if_pos (Finset.mem_univ j), ← Finset.sum_mul, hμ]
  ring

theorem equalInput_semigroup {μ : S → ℝ} (hμ : (∑ i, μ i) = 1) (s t : ℝ) :
    matMul (equalInput μ s) (equalInput μ t) = equalInput μ (s * t) := by
  classical
  funext i j
  rw [equalInput_mul, rowAction_equalInput hμ]
  unfold equalInput
  split_ifs <;> ring

theorem equalInput_reversible (μ : S → ℝ) (t : ℝ) (i j : S) :
    μ i * equalInput μ t i j = μ j * equalInput μ t j i := by
  classical
  by_cases h : i = j
  · subst j
    rfl
  · simp only [equalInput, if_neg h, if_neg (Ne.symm h), zero_add]
    ring

theorem blendPair_matrix_formula (μ : S → ℝ) (c : ℝ) (A : Mat S) :
    blendPair μ c A = fun i j => matMul (equalInput μ c) A j i * μ j := by
  funext i j
  rw [equalInput_mul]
  unfold blendPair
  ring

/-- This neighborhood argument picks t strictly below one, not a limit point. -/
theorem exists_left_of_eventually {p : ℝ → Prop}
    (hp : ∀ᶠ t in 𝓝 (1 : ℝ), p t) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ p t := by
  rcases Metric.eventually_nhds_iff.mp hp with ⟨ε, hε, he⟩
  let δ : ℝ := min (ε / 2) (1 / 2)
  have hd0 : 0 < δ := lt_min (by linarith) (by norm_num)
  have hdε : δ < ε := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hd1 : δ ≤ (1 : ℝ) / 2 := min_le_right _ _
  refine ⟨1 - δ, by linarith, by linarith, ?_⟩
  apply he
  have hdist : dist (1 - δ) (1 : ℝ) = δ := by
    rw [Real.dist_eq]
    have heq : (1 - δ) - 1 = -δ := by ring
    rw [heq, abs_neg, abs_of_pos hd0]
  rw [hdist]
  exact hdε

noncomputable def coefficient {R : Type v} [Fintype R]
    (w : R → ℝ) (k : R → ℕ) (t : ℝ) : ℝ :=
  ∑ r, w r * t ^ k r

theorem coefficient_continuous {R : Type v} [Fintype R]
    (w : R → ℝ) (k : R → ℕ) : Continuous (coefficient w k) := by
  unfold coefficient
  fun_prop

theorem coefficient_one {R : Type v} [Fintype R]
    {w : R → ℝ} (k : R → ℕ) (hw : (∑ r, w r) = 1) :
    coefficient w k 1 = 1 := by
  simpa only [coefficient, one_pow, mul_one] using hw

/-- Finite openness supplies one common t for all matrix entries. -/
theorem exists_compensation_parameter {R : Type v} [Fintype R]
    {w : R → ℝ} (k : R → ℕ) (hw : (∑ r, w r) = 1)
    {M : Mat S} (hM : ∀ i j, 0 < M i j) (ν : S → ℝ) :
    ∃ t : ℝ, 0 < t ∧ t < 1 ∧ 0 < coefficient w k t ∧
      ∀ i j, 0 < M i j - (1 - coefficient w k t) * ν j := by
  have hc : Continuous (coefficient w k) := coefficient_continuous w k
  have hc1 := coefficient_one k hw
  have hec : ∀ᶠ t in 𝓝 (1 : ℝ), 0 < coefficient w k t := by
    apply hc.continuousAt.eventually
    exact isOpen_Ioi.mem_nhds (by rw [hc1]; norm_num)
  have he : ∀ i j, ∀ᶠ t in 𝓝 (1 : ℝ),
      0 < M i j - (1 - coefficient w k t) * ν j := by
    intro i j
    have hf : Continuous (fun t : ℝ =>
        M i j - (1 - coefficient w k t) * ν j) := by fun_prop
    apply hf.continuousAt.eventually
    apply isOpen_Ioi.mem_nhds
    simpa only [hc1, sub_self, zero_mul, sub_zero] using hM i j
  have hall : ∀ᶠ t in 𝓝 (1 : ℝ),
      ∀ i j, 0 < M i j - (1 - coefficient w k t) * ν j :=
    Filter.eventually_all.mpr (fun i => Filter.eventually_all.mpr (he i))
  exact exists_left_of_eventually (hec.and hall)

namespace Edge
open RootBlobEdgeIndexed
variable {V : Type v} {E : Type w}
variable [Fintype V] [DecidableEq V] [Fintype E]
variable (N : RootBlobEdgeIndexed.Network V E (Fin 2)) (W : E → ℝ)
variable (H : Subgroup (Equiv.Perm S))

/-- One assignment to original edges; parallel occurrences remain distinct. -/
noncomputable def terminalAssignment (A B : Mat S) : E → Mat S := by
  classical
  exact fun e => if N.target e = N.observed 0 then A else B

theorem terminalAssignment_open {A B : Mat S}
    (hA : OpenTransition H A) (hB : OpenTransition H B) :
    ∀ e, OpenTransition H (terminalAssignment N A B e) := by
  classical
  intro e
  unfold terminalAssignment
  split_ifs <;> assumption

/-- UNPROVED semantic input. Its construction must expand the actual finite
DAG and retain the original shared edge parameters and W. Formula is required
for ALL admitted roots and A, not only for a chosen target distribution. -/
structure ResolutionCertificate (R : Type x) [Fintype R] where
  weight : R → ℝ
  exponent : R → ℕ
  weight_pos : ∀ r, 0 < weight r
  weight_total : (∑ r, weight r) = 1
  exponent_pos : ∀ r, 0 < exponent r
  formula : ∀ (μ : S → ℝ) (A : Mat S) (t : ℝ),
    RootAdmitted H μ → (∀ i, 0 < μ i) → OpenTransition H A →
    0 < t → t < 1 →
    RootBlobEdgeIndexed.pairLaw N μ W
      (terminalAssignment N A (equalInput μ t)) =
      blendPair μ (coefficient weight exponent t) A

/-- Full constructive reverse direction, conditional only on the explicit
resolution formula above. This is a proof term, but remains unelaborated. -/
theorem realize_of_resolution [Nonempty S]
    {R : Type x} [Fintype R]
    (C : ResolutionCertificate N W H R)
    {P : Mat S} (hP : PositiveInvariantPair H P) :
    ∃ (π : S → ℝ) (M : E → Mat S),
      (∀ i, 0 < π i) ∧ RootAdmitted H π ∧
      (∀ e, OpenTransition H (M e)) ∧
      RootBlobEdgeIndexed.pairLaw N π W M = P := by
  classical
  let μ := secondMarginal P
  let M := conditional P
  let ν := rowAction μ M
  have hμpos : ∀ i, 0 < μ i := marginal_positive hP.1
  have hμ : RootAdmitted H μ := marginal_root hP
  have hM : OpenTransition H M := conditional_open hP
  have hνtotal : (∑ i, ν i) = 1 := rowAction_total hμ.1.2 hM.1.2
  have hνinv : Invariant H ν := rowAction_invariant hμ.2 hM.2
  obtain ⟨t, ht0, ht1, hc0, hnum⟩ :=
    exists_compensation_parameter C.exponent C.weight_total hM.1.1 ν
  let c := coefficient C.weight C.exponent t
  let A := compensate M ν c
  have hc : c ≠ 0 := ne_of_gt hc0
  have hA : OpenTransition H A := by
    refine ⟨⟨?_, compensate_rows hM.1.2 hνtotal hc⟩,
      compensate_invariant hM.2 hνinv⟩
    intro i j
    exact div_pos (hnum i j) hc0
  refine ⟨μ, terminalAssignment N A (equalInput μ t),
    hμpos, hμ, terminalAssignment_open N H hA
      (equalInput_open hμ hμpos ht0 ht1), ?_⟩
  rw [C.formula μ A t hμ hμpos hA ht0 ht1]
  change blendPair μ c (compensate M (rowAction μ M) c) = P
  rw [compensate_blend hμ.1.2 hc]
  funext i j
  exact conditional_reconstruct hP.1 i j


/-- Relabel every vertex state by the same state permutation. -/
def relabel (g : Equiv.Perm S) : (V → S) ≃ (V → S) where
  toFun := fun a v => g (a v)
  invFun := fun a v => g.symm (a v)
  left_inv := by intro a; funext v; exact g.symm_apply_apply (a v)
  right_inv := by intro a; funext v; exact g.apply_symm_apply (a v)

theorem assignmentMass_invariant (π : S → ℝ) (M : E → Mat S)
    (hπ : RootAdmitted H π) (hM : ∀ e, OpenTransition H (M e))
    (h : H) (a : V → S) :
    RootBlobEdgeIndexed.assignmentMass N π W M (relabel h.val a) =
      RootBlobEdgeIndexed.assignmentMass N π W M a := by
  classical
  unfold RootBlobEdgeIndexed.assignmentMass
  change π (h.val (a N.root)) *
      (Finset.univ.erase N.root).prod (fun v => ∑ e,
        if N.target e = v then
          W e * M e (h.val (a (N.source e))) (h.val (a v)) else 0) = _
  rw [hπ.2 h (a N.root)]
  congr 1
  apply Finset.prod_congr rfl
  intro v _
  apply Finset.sum_congr rfl
  intro e _
  split_ifs
  · rw [(hM e).2 h (a (N.source e)) (a v)]
  · rfl

theorem observedLaw_invariant (π : S → ℝ) (M : E → Mat S)
    (hπ : RootAdmitted H π) (hM : ∀ e, OpenTransition H (M e))
    (h : H) (z : Fin 2 → S) :
    RootBlobEdgeIndexed.observedLaw N π W M (fun o => h.val (z o)) =
      RootBlobEdgeIndexed.observedLaw N π W M z := by
  classical
  unfold RootBlobEdgeIndexed.observedLaw
  rw [← (relabel (V := V) h.val).sum_comp
    (fun a => if (∀ o, a (N.observed o) = h.val (z o))
      then RootBlobEdgeIndexed.assignmentMass N π W M a else 0)]
  apply Finset.sum_congr rfl
  intro a _
  have hc : (∀ o, (relabel h.val a) (N.observed o) = h.val (z o)) ↔
      (∀ o, a (N.observed o) = z o) := by
    apply forall_congr'
    intro o
    exact h.val.injective.eq_iff
  rw [hc]
  split_ifs
  · exact assignmentMass_invariant N W H π M hπ hM h a
  · rfl

theorem pairLaw_invariant (π : S → ℝ) (M : E → Mat S)
    (hπ : RootAdmitted H π) (hM : ∀ e, OpenTransition H (M e)) :
    Equivariant H (RootBlobEdgeIndexed.pairLaw N π W M) := by
  intro h i j
  unfold RootBlobEdgeIndexed.pairLaw
  have hz : (fun k : Fin 2 => if k = 0 then h.val i else h.val j) =
      (fun k : Fin 2 => h.val (if k = 0 then i else j)) := by
    funext k
    split_ifs <;> rfl
  rw [hz]
  exact observedLaw_invariant N W H π M hπ hM h
    (fun k => if k = 0 then i else j)

theorem assignmentMass_nonnegative (π : S → ℝ) (M : E → Mat S)
    (hW : RootBlobEdgeIndexed.WeightsAdmitted N W)
    (hπ : RootAdmitted H π) (hM : ∀ e, OpenTransition H (M e))
    (a : V → S) :
    0 ≤ RootBlobEdgeIndexed.assignmentMass N π W M a := by
  classical
  unfold RootBlobEdgeIndexed.assignmentMass
  apply mul_nonneg (hπ.1.1 _)
  apply Finset.prod_nonneg
  intro v _
  apply Finset.sum_nonneg
  intro e _
  split_ifs
  · exact le_of_lt (mul_pos (hW.1 e) ((hM e).1.1 _ _))
  · exact le_refl 0

theorem assignmentMass_positive (π : S → ℝ) (M : E → Mat S)
    (hG : RootBlobEdgeIndexed.GraphAdmitted N)
    (hW : RootBlobEdgeIndexed.WeightsAdmitted N W)
    (hM : ∀ e, OpenTransition H (M e))
    (a : V → S) (ha : 0 < π (a N.root)) :
    0 < RootBlobEdgeIndexed.assignmentMass N π W M a := by
  classical
  unfold RootBlobEdgeIndexed.assignmentMass
  apply mul_pos ha
  apply Finset.prod_pos
  intro v hv
  have hvroot : v ≠ N.root := (Finset.mem_erase.mp hv).1
  obtain ⟨e, he⟩ := hG.2.2.2.2.1 v hvroot
  apply Finset.sum_pos'
  · intro f _
    split_ifs
    · exact le_of_lt (mul_pos (hW.1 f) ((hM f).1.1 _ _))
    · exact le_refl 0
  · refine ⟨e, Finset.mem_univ e, ?_⟩
    simp only [he, if_true]
    exact mul_pos (hW.1 e) ((hM e).1.1 _ _)

/-- Positivity is proved directly for the actual assignment sum, rather than
included in an opaque source-image hypothesis. Root laws may have zeros. -/
theorem pairLaw_positive (π : S → ℝ) (M : E → Mat S)
    (hG : RootBlobEdgeIndexed.GraphAdmitted N)
    (hW : RootBlobEdgeIndexed.WeightsAdmitted N W)
    (hπ : RootAdmitted H π) (hM : ∀ e, OpenTransition H (M e)) :
    ∀ i j, 0 < RootBlobEdgeIndexed.pairLaw N π W M i j := by
  classical
  have hk : ∃ k, 0 < π k := by
    by_contra h
    push_neg at h
    have hz : ∀ k, π k = 0 := fun k => le_antisymm (h k) (hπ.1.1 k)
    have ht := hπ.1.2
    simp_rw [hz] at ht
    simpa using ht
  obtain ⟨k, hk⟩ := hk
  intro i j
  let a : V → S := fun v =>
    if v = N.observed 0 then i else if v = N.observed 1 then j else k
  have h01 : N.observed 0 ≠ N.observed 1 := by
    intro he
    have hfin := hG.1 he
    norm_num at hfin
  have hr0 : N.root ≠ N.observed 0 := Ne.symm (hG.2.1 0)
  have hr1 : N.root ≠ N.observed 1 := Ne.symm (hG.2.1 1)
  have haroot : a N.root = k := by simp [a, hr0, hr1]
  have haout : ∀ o : Fin 2,
      a (N.observed o) = if o = 0 then i else j := by
    intro o
    fin_cases o <;> simp [a, h01, Ne.symm h01]
  unfold RootBlobEdgeIndexed.pairLaw RootBlobEdgeIndexed.observedLaw
  apply Finset.sum_pos'
  · intro b _
    split_ifs
    · exact assignmentMass_nonnegative N W H π M hW hπ hM b
    · exact le_refl 0
  · refine ⟨a, Finset.mem_univ a, ?_⟩
    rw [if_pos haout]
    apply assignmentMass_positive N W H π M hG hW hM a
    rw [haroot]
    exact hk

/-- Still open: normalization of the finite-DAG sum by reverse-topological
elimination. Positivity and symmetry have separate proof terms above. -/
def SourceNormalization : Prop :=
  ∀ (π : S → ℝ) (M : E → Mat S),
    RootAdmitted H π → (∀ e, OpenTransition H (M e)) →
    (∑ i, ∑ j, RootBlobEdgeIndexed.pairLaw N π W M i j) = 1

/-- Soundness is an explicitly outstanding finite-DAG semantic obligation,
not an axiom supplied by this module. -/
def SourceSoundness : Prop :=
  ∀ (π : S → ℝ) (M : E → Mat S),
    RootAdmitted H π → (∀ e, OpenTransition H (M e)) →
    PositiveInvariantPair H (RootBlobEdgeIndexed.pairLaw N π W M)


/-- This conditional theorem leaves normalization, but not positivity or
equivariance, in the source-law soundness obligation. -/
theorem soundness_of_normalization
    (hG : RootBlobEdgeIndexed.GraphAdmitted N)
    (hW : RootBlobEdgeIndexed.WeightsAdmitted N W)
    (hnorm : SourceNormalization N W H) : SourceSoundness N W H := by
  intro π M hπ hM
  exact ⟨pairLaw_positive N W H π M hG hW hπ hM,
    hnorm π M hπ hM, pairLaw_invariant N W H π M hπ hM⟩

/-- Whole image theorem assembly. No part of SourceSoundness or the
ResolutionCertificate is automatically discharged by this theorem. -/
theorem openImage_eq_of_semantics [Nonempty S]
    {R : Type x} [Fintype R] (C : ResolutionCertificate N W H R)
    (hsound : SourceSoundness N W H) :
    RootBlobEdgeIndexed.openImage N W H =
      {P | PositiveInvariantPair H P} := by
  apply Set.ext
  intro P
  constructor
  · rintro ⟨π, M, hπ, hM, rfl⟩
    exact hsound π M hπ hM
  · intro hP
    rcases realize_of_resolution N W H C hP with
      ⟨π, M, _, hπ, hM, heq⟩
    exact ⟨π, M, hπ, hM, heq⟩

/-- Joint-context equality is a consequence of two complete pair-image
equalities; no independence of output ports is inserted. -/
theorem contextImages_eq_of_semantics [Nonempty S]
    {R : Type x} [Fintype R] (C : ResolutionCertificate N W H R)
    (hsound : SourceSoundness N W H)
    {RF : Type x} [Fintype RF]
    (CF : ResolutionCertificate RootBlobEdgeIndexed.rootedFork
      RootBlobEdgeIndexed.forkWeights H RF)
    (hfork : SourceSoundness RootBlobEdgeIndexed.rootedFork
      RootBlobEdgeIndexed.forkWeights H)
    {Z : Type*} (Q : S → S → Z → ℝ) :
    Set.image (fun P => context P Q) (RootBlobEdgeIndexed.openImage N W H) =
      Set.image (fun P => context P Q)
        (RootBlobEdgeIndexed.openImage RootBlobEdgeIndexed.rootedFork
          RootBlobEdgeIndexed.forkWeights H) := by
  rw [openImage_eq_of_semantics N W H C hsound,
    openImage_eq_of_semantics RootBlobEdgeIndexed.rootedFork
      RootBlobEdgeIndexed.forkWeights H CF hfork]


/-- Connects the proof-term layer to the exact original named interface.
The two premises are obligations, NOT automatically available instances. -/
theorem openImageClaim_of_obligations [Nonempty S]
    {R : Type x} [Fintype R]
    (hresolve : RootBlobEdgeIndexed.GraphAdmitted N →
      RootBlobEdgeIndexed.WeightsAdmitted N W → ResolutionCertificate N W H R)
    (hnorm : RootBlobEdgeIndexed.GraphAdmitted N →
      RootBlobEdgeIndexed.WeightsAdmitted N W → SourceNormalization N W H) :
    RootBlobEdgeIndexed.OpenImageClaim N W H := by
  intro _ hG hW
  exact openImage_eq_of_semantics N W H (hresolve hG hW)
    (soundness_of_normalization N W H hG hW (hnorm hG hW))

theorem openRealizationClaim_of_obligations [Nonempty S]
    {R : Type x} [Fintype R]
    (hresolve : RootBlobEdgeIndexed.GraphAdmitted N →
      RootBlobEdgeIndexed.WeightsAdmitted N W → ResolutionCertificate N W H R) :
    RootBlobEdgeIndexed.OpenRealizationClaim N W H := by
  intro _ hG hW P hP
  exact realize_of_resolution N W H (hresolve hG hW) hP

end Edge
end RootBlobOpenProof
