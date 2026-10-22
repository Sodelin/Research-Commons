import RootBlobTreeMarginals

/-!
# Joint-port context gluing, source only

Author: dot (OpenAI), 22 October 2026.
UNELABORATED. No compiler, kernel, runtime, or build claim.
The exterior is conditioned jointly on the two ports. It is never replaced
by two independent marginal kernels. Original exterior factors remain fixed.
-/

open scoped BigOperators
open RootBlobInterfaces RootBlobOpenProof RootBlobDAGNormalization
namespace RootBlobContextGlue
universe u v w x
variable {S : Type u} [Fintype S]
variable {A : Type v} [Fintype A]
variable {B : Type w} [Fintype B]
variable {Z : Type x} [Fintype Z]

noncomputable def portPair (m : (A → S) → ℝ) (p q : A) : Mat S := by
  classical
  exact fun i j => ∑ a : A → S, m a * (if a p = i ∧ a q = j then 1 else 0)

/-- Actual exterior state sum, with its original fixed factors and observation. -/
noncomputable def exteriorKernel (f : S → S → (B → S) → ℝ)
    (R : S → S → (B → S) → Z → ℝ) : S → S → Z → ℝ :=
  fun i j z => ∑ b : B → S, f i j b * R i j b z

noncomputable def fullLaw (m : (A → S) → ℝ) (p q : A)
    (f : S → S → (B → S) → ℝ) (R : S → S → (B → S) → Z → ℝ) : Z → ℝ :=
  fun z => ∑ a : A → S, ∑ b : B → S, m a * f (a p) (a q) b * R (a p) (a q) b z

theorem context_binning (m : (A → S) → ℝ) (p q : A)
    (Q : S → S → Z → ℝ) (z : Z) :
    context (portPair m p q) Q z =
      ∑ a : A → S, m a * Q (a p) (a q) z := by
  classical
  unfold context portPair
  simp_rw [Finset.sum_mul]
  calc
    (∑ i, ∑ j, ∑ a : A → S,
      (m a * (if a p = i ∧ a q = j then 1 else 0)) * Q i j z) =
      ∑ i, ∑ a : A → S, ∑ j,
        (m a * (if a p = i ∧ a q = j then 1 else 0)) * Q i j z := by
        apply Finset.sum_congr rfl
        intro i _
        rw [Finset.sum_comm]
    _ = ∑ a : A → S, ∑ i, ∑ j,
        (m a * (if a p = i ∧ a q = j then 1 else 0)) * Q i j z := by
        rw [Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro a _
      have ht : ∀ i j,
          (m a * (if a p = i ∧ a q = j then 1 else 0)) * Q i j z =
          if a p = i then (if a q = j then m a * Q i j z else 0) else 0 := by
        intro i j
        split_ifs <;> simp_all
      simp_rw [ht]
      have hi : ∀ i, (∑ j, if a p = i then
          (if a q = j then m a * Q i j z else 0) else 0) =
          if a p = i then m a * Q i (a q) z else 0 := by
        intro i
        by_cases hp : a p = i <;> simp [hp]
      simp_rw [hi]
      simp

theorem fullLaw_eq_context (m : (A → S) → ℝ) (p q : A)
    (f : S → S → (B → S) → ℝ) (R : S → S → (B → S) → Z → ℝ) :
    fullLaw m p q f R = context (portPair m p q) (exteriorKernel f R) := by
  funext z
  rw [context_binning]
  unfold fullLaw exteriorKernel
  simp_rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  ring

theorem exteriorKernel_admitted
    (f : S → S → (B → S) → ℝ) (R : S → S → (B → S) → Z → ℝ)
    (hf0 : ∀ i j b, 0 ≤ f i j b) (hf1 : ∀ i j, (∑ b, f i j b) = 1)
    (hR0 : ∀ i j b z, 0 ≤ R i j b z)
    (hR1 : ∀ i j b, (∑ z, R i j b z) = 1) :
    ContextAdmitted (exteriorKernel f R) := by
  intro i j
  constructor
  · intro z
    exact Finset.sum_nonneg (fun b _ => mul_nonneg (hf0 i j b) (hR0 i j b z))
  · unfold exteriorKernel
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hR1]
    simpa using hf1 i j

/-- A ranked exterior factorization with fixed port values. These are
local structural properties, not an assumed normalization or model image.
The edge-indexed specialization below supplies these properties. -/
structure ExteriorFactors (B : Type w) (S : Type u) [Fintype S] [DecidableEq B] where
  rank : B → ℕ
  factor : S → S → B → (B → S) → ℝ
  nonneg : ∀ i j v b, 0 ≤ factor i j v b
  normalize : ∀ i j v b, (∑ s, factor i j v (Function.update b v s)) = 1
  ignore_future : ∀ i j v w b s, v ≠ w → rank v ≤ rank w →
    factor i j v (Function.update b w s) = factor i j v b

namespace ExteriorFactors
variable [DecidableEq B] (F : ExteriorFactors B S)

noncomputable def mass (i j : S) (b : B → S) : ℝ := ∏ v, F.factor i j v b

theorem mass_nonneg (i j : S) (b : B → S) : 0 ≤ F.mass i j b :=
  Finset.prod_nonneg (fun v _ => F.nonneg i j v b)

theorem mass_total [Nonempty S] (i j : S) : (∑ b, F.mass i j b) = 1 :=
  ranked_normalization F.rank (F.factor i j) (F.normalize i j) (F.ignore_future i j)

theorem context_admitted [Nonempty S] (R : S → S → (B → S) → Z → ℝ)
    (hR0 : ∀ i j b z, 0 ≤ R i j b z)
    (hR1 : ∀ i j b, (∑ z, R i j b z) = 1) :
    ContextAdmitted (exteriorKernel F.mass R) :=
  exteriorKernel_admitted F.mass R F.mass_nonneg F.mass_total hR0 hR1

end ExteriorFactors


/-- Exterior edges retain their occurrences. Their source is either a
specified boundary port or an exterior vertex; their target is exterior. -/
structure ExteriorDAG (B : Type w) (E : Type v) where
  source : E → Sum (Fin 2) B
  target : E → B
  rank : B → ℕ
  internal_rank : ∀ e v, source e = Sum.inr v → rank v < rank (target e)

namespace ExteriorDAG
variable {E : Type v} [Fintype E] [DecidableEq B]
variable (D : ExteriorDAG B E)

noncomputable def sourceState (i j : S) (b : B → S) (e : E) : S := by
  classical
  exact match D.source e with
    | Sum.inl o => if o = 0 then i else j
    | Sum.inr v => b v

noncomputable def factor (W : E → ℝ) (M : E → Mat S)
    (i j : S) (v : B) (b : B → S) : ℝ := by
  classical
  exact ∑ e, if D.target e = v then W e * M e (D.sourceState i j b e) (b v) else 0

theorem sourceState_update (i j : S) (b : B → S) (e : E) (w : B) (s : S)
    (h : D.source e ≠ Sum.inr w) :
    D.sourceState i j (Function.update b w s) e = D.sourceState i j b e := by
  classical
  cases he : D.source e with
  | inl o => simp [sourceState, he]
  | inr v =>
    have hv : v ≠ w := by
      intro hvw
      subst w
      exact h he
    simp [sourceState, he, Function.update_of_ne hv]

theorem source_ne_target (e : E) :
    D.source e ≠ Sum.inr (D.target e) := by
  intro he
  exact (Nat.lt_irrefl _) (D.internal_rank e (D.target e) he)

theorem factor_normalize (W : E → ℝ) (M : E → Mat S)
    (hW : ∀ v, (∑ e, if D.target e = v then W e else 0) = 1)
    (hM : ∀ e i, (∑ j, M e i j) = 1)
    (i j : S) (v : B) (b : B → S) :
    (∑ s, D.factor W M i j v (Function.update b v s)) = 1 := by
  classical
  have hu : ∀ s,
      D.factor W M i j v (Function.update b v s) =
        ∑ e, if D.target e = v then W e * M e (D.sourceState i j b e) s else 0 := by
    intro s
    unfold factor
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : D.target e = v
    · have hn : D.source e ≠ Sum.inr v := by
        simpa [he] using D.source_ne_target e
      simp only [he, if_true, Function.update_self]
      rw [D.sourceState_update i j b e v s hn]
    · simp only [he, if_false]
  simp_rw [hu]
  rw [Finset.sum_comm]
  have ht : ∀ e, (∑ s, if D.target e = v then
      W e * M e (D.sourceState i j b e) s else 0) =
      if D.target e = v then W e else 0 := by
    intro e
    by_cases he : D.target e = v
    · simp only [he, if_true]
      rw [← Finset.mul_sum, hM, mul_one]
    · simp [he]
  simp_rw [ht]
  exact hW v

theorem factor_ignore_future (W : E → ℝ) (M : E → Mat S)
    (i j : S) (v w : B) (b : B → S) (s : S)
    (hvw : v ≠ w) (hr : D.rank v ≤ D.rank w) :
    D.factor W M i j v (Function.update b w s) = D.factor W M i j v b := by
  classical
  unfold factor
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : D.target e = v
  · have hn : D.source e ≠ Sum.inr w := by
      intro hs
      have hlt := D.internal_rank e w hs
      rw [he] at hlt
      exact (not_lt_of_ge hr) hlt
    simp only [he, if_true, Function.update_of_ne hvw]
    rw [D.sourceState_update i j b e w s hn]
  · simp only [he, if_false]

noncomputable def factors (W : E → ℝ) (M : E → Mat S)
    (hW0 : ∀ e, 0 ≤ W e)
    (hW1 : ∀ v, (∑ e, if D.target e = v then W e else 0) = 1)
    (hM0 : ∀ e i j, 0 ≤ M e i j)
    (hM1 : ∀ e i, (∑ j, M e i j) = 1) : ExteriorFactors B S where
  rank := D.rank
  factor := D.factor W M
  nonneg := by
    intro i j v b
    unfold factor
    apply Finset.sum_nonneg
    intro e _
    split_ifs
    · exact mul_nonneg (hW0 e) (hM0 e _ _)
    · exact le_refl 0
  normalize := D.factor_normalize W M hW1 hM1
  ignore_future := D.factor_ignore_future W M

end ExteriorDAG


noncomputable def deterministicReadout (observe : S → S → (B → S) → Z) :
    S → S → (B → S) → Z → ℝ := by
  classical
  exact fun i j b z => if observe i j b = z then 1 else 0

theorem deterministicReadout_nonneg (observe : S → S → (B → S) → Z)
    (i j : S) (b : B → S) (z : Z) :
    0 ≤ deterministicReadout observe i j b z := by
  classical
  unfold deterministicReadout
  split_ifs <;> norm_num

theorem deterministicReadout_total (observe : S → S → (B → S) → Z)
    (i j : S) (b : B → S) :
    (∑ z, deterministicReadout observe i j b z) = 1 := by
  classical
  simp [deterministicReadout]

/-- Assignment reindexing for a literal vertex partition, not an assumption
that hidden variables or the two port states are independent. -/
def sumAssignmentEquiv : (Sum A B → S) ≃ (A → S) × (B → S) where
  toFun := fun a => (fun v => a (Sum.inl v), fun w => a (Sum.inr w))
  invFun := fun p => Sum.elim p.1 p.2
  left_inv := by
    intro a
    funext v
    cases v <;> rfl
  right_inv := by intro p; cases p; rfl

/-- The original assignment sum after only the graph cut factorization:
internal mass times fixed exterior factors conditioned on both ports. -/
noncomputable def cutLaw (m : (A → S) → ℝ) (p q : A)
    (f : S → S → (B → S) → ℝ)
    (R : S → S → (B → S) → Z → ℝ) : Z → ℝ :=
  fun z => ∑ a : Sum A B → S,
    m (fun v => a (Sum.inl v)) *
    f (a (Sum.inl p)) (a (Sum.inl q)) (fun w => a (Sum.inr w)) *
    R (a (Sum.inl p)) (a (Sum.inl q)) (fun w => a (Sum.inr w)) z

theorem cutLaw_eq_fullLaw (m : (A → S) → ℝ) (p q : A)
    (f : S → S → (B → S) → ℝ)
    (R : S → S → (B → S) → Z → ℝ) :
    cutLaw m p q f R = fullLaw m p q f R := by
  funext z
  unfold cutLaw fullLaw
  calc
    (∑ a : Sum A B → S,
      m (fun v => a (Sum.inl v)) *
      f (a (Sum.inl p)) (a (Sum.inl q)) (fun w => a (Sum.inr w)) *
      R (a (Sum.inl p)) (a (Sum.inl q)) (fun w => a (Sum.inr w)) z) =
      ∑ ab : (A → S) × (B → S),
        m ab.1 * f (ab.1 p) (ab.1 q) ab.2 * R (ab.1 p) (ab.1 q) ab.2 z := by
        apply Fintype.sum_equiv sumAssignmentEquiv
        intro a
        rfl
    _ = _ := Fintype.sum_prod_type _

theorem cutLaw_eq_context (m : (A → S) → ℝ) (p q : A)
    (f : S → S → (B → S) → ℝ)
    (R : S → S → (B → S) → Z → ℝ) :
    cutLaw m p q f R = context (portPair m p q) (exteriorKernel f R) := by
  rw [cutLaw_eq_fullLaw, fullLaw_eq_context]

theorem portPair_assignmentMass {E : Type*} [Fintype E] [DecidableEq A]
    (N : RootBlobEdgeIndexed.Network A E (Fin 2))
    (π : S → ℝ) (W : E → ℝ) (M : E → Mat S) :
    portPair (RootBlobEdgeIndexed.assignmentMass N π W M)
      (N.observed 0) (N.observed 1) =
      RootBlobEdgeIndexed.pairLaw N π W M := by
  classical
  funext i j
  unfold portPair RootBlobEdgeIndexed.pairLaw RootBlobEdgeIndexed.observedLaw
  apply Finset.sum_congr rfl
  intro a _
  have hc : (∀ o : Fin 2, a (N.observed o) = if o = 0 then i else j) ↔
      a (N.observed 0) = i ∧ a (N.observed 1) = j := by
    constructor
    · intro h
      exact ⟨by simpa using h 0, by simpa using h 1⟩
    · rintro ⟨h0, h1⟩ o
      fin_cases o
      · simpa using h0
      · simpa using h1
  rw [hc]
  split_ifs <;> simp

theorem cutNetworkLaw_eq_context {E : Type*} [Fintype E] [DecidableEq A]
    (N : RootBlobEdgeIndexed.Network A E (Fin 2))
    (π : S → ℝ) (W : E → ℝ) (M : E → Mat S)
    (f : S → S → (B → S) → ℝ)
    (R : S → S → (B → S) → Z → ℝ) :
    cutLaw (RootBlobEdgeIndexed.assignmentMass N π W M)
      (N.observed 0) (N.observed 1) f R =
      context (RootBlobEdgeIndexed.pairLaw N π W M) (exteriorKernel f R) := by
  rw [cutLaw_eq_context, portPair_assignmentMass]

end RootBlobContextGlue
