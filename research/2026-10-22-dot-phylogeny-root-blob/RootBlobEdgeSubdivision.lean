import RootBlobFullModel

/-!
# Exact one-edge subdivision of the original displayed-tree state sum
Author: dot (OpenAI), 23 October 2026.
UNELABORATED SOURCE ONLY. No runtime, compiler, or kernel verification.
The identity below permits other parents at the subdivided edge's target.
All original inheritance weights are retained. Only the new indegree-one
edge has weight one. Full-image equality permits a free selected edge matrix.
-/

open scoped BigOperators
open RootBlobInterfaces RootBlobOpenProof RootBlobCutFactorization
namespace RootBlobEdgeSubdivision
universe u v w x
variable {S : Type u} [Fintype S]
variable {V : Type v} [Fintype V] [DecidableEq V]
variable {E : Type w} [Fintype E] [DecidableEq E]
variable {O : Type x} [Fintype O]

/-- Full positive equivariant matrices are closed under multiplication. -/
theorem matMul_open [Nonempty S] {H : Subgroup (Equiv.Perm S)}
    {K A : Mat S} (hK : OpenTransition H K) (hA : OpenTransition H A) :
    OpenTransition H (matMul K A) := by
  classical
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · intro i j
    exact Finset.sum_pos (fun k _ => mul_pos (hK.1.1 i k) (hA.1.1 k j))
      Finset.univ_nonempty
  · intro i
    unfold matMul
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, hA.1.2, mul_one]
    exact hK.1.2 i
  · intro h i j
    unfold matMul
    calc
      (∑ k, K (h.val i) k * A k (h.val j)) =
          ∑ k, K (h.val i) (h.val k) * A (h.val k) (h.val j) :=
        (Equiv.sum_comp h.val _).symm
      _ = ∑ k, K i k * A k j := by
        apply Finset.sum_congr rfl
        intro k _
        rw [hK.2 h i k, hA.2 h k j]

/-- Exact attained factorization, not an identity edge or a closure limit. -/
theorem exists_open_factorization [Nonempty S]
    {H : Subgroup (Equiv.Perm S)} {M : Mat S} (hM : OpenTransition H M) :
    ∃ K A : Mat S, OpenTransition H K ∧ OpenTransition H A ∧ matMul K A = M := by
  classical
  let μ : S → ℝ := fun _ => (Fintype.card S : ℝ)⁻¹
  have hn : (0 : ℝ) < Fintype.card S := by
    exact_mod_cast (Fintype.card_pos : 0 < Fintype.card S)
  have hμpos : ∀ i, 0 < μ i := fun _ => inv_pos.mpr hn
  have hμtotal : (∑ i, μ i) = 1 := by
    simp [μ, nsmul_eq_mul, ne_of_gt hn]
  have hμ : RootAdmitted H μ :=
    ⟨⟨fun i => le_of_lt (hμpos i), hμtotal⟩, fun _ _ => rfl⟩
  obtain ⟨t, ht0, ht1, _, hnum⟩ :=
    exists_compensation_parameter (w := fun _ : Unit => (1 : ℝ))
      (fun _ => 1) (by simp) hM.1.1 (rowAction μ M)
  have hc : coefficient (fun _ : Unit => (1 : ℝ)) (fun _ => 1) t = t := by
    simp [coefficient]
  rw [hc] at hnum
  let K := equalInput μ t
  let A := compensate M (rowAction μ M) t
  have hA : OpenTransition H A := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · intro i j
      exact div_pos (hnum i j) ht0
    · exact compensate_rows hM.1.2
        (rowAction_total hμtotal hM.1.2) (ne_of_gt ht0)
    · exact compensate_invariant hM.2 (rowAction_invariant hμ.2 hM.2)
  refine ⟨K, A, equalInput_open hμ hμpos ht0 ht1, hA, ?_⟩
  funext i j
  change matMul (equalInput μ t) (compensate M (rowAction μ M) t) i j = M i j
  rw [equalInput_mul, compensate_transport hμtotal (ne_of_gt ht0)]
  unfold compensate
  field_simp [ne_of_gt ht0] <;> ring

variable (G : RootBlobEdgeIndexed.Network V E O) (e₀ : E)

/-- The old edge occurrence becomes the second segment; the new occurrence
is the first segment. Its target has no other incoming edge. -/
def subdivide : RootBlobEdgeIndexed.Network (Sum V Unit) (Sum E Unit) O where
  root := Sum.inl G.root
  observed := fun o => Sum.inl (G.observed o)
  source := fun e => match e with
    | Sum.inl e => if e = e₀ then Sum.inr () else Sum.inl (G.source e)
    | Sum.inr _ => Sum.inl (G.source e₀)
  target := fun e => match e with
    | Sum.inl e => Sum.inl (G.target e)
    | Sum.inr _ => Sum.inr ()
  rank := fun v => match v with
    | Sum.inl v => 2 * G.rank v
    | Sum.inr _ => 2 * G.rank (G.source e₀) + 1

def weights (W : E → ℝ) : Sum E Unit → ℝ := Sum.elim W (fun _ => 1)
def matrices (M : E → Mat S) (K : Mat S) : Sum E Unit → Mat S :=
  Sum.elim M (fun _ => K)
def assignment (a : V → S) (y : S) : Sum V Unit → S :=
  Sum.elim a (fun _ => y)

noncomputable def collapsed (M : E → Mat S) (K : Mat S) : E → Mat S :=
  Function.update M e₀ (matMul K (M e₀))

theorem collapsed_off (M : E → Mat S) (K : Mat S) {e : E} (he : e ≠ e₀) :
    collapsed e₀ M K e = M e := by
  simp [collapsed, he]

theorem collapsed_at (M : E → Mat S) (K : Mat S) :
    collapsed e₀ M K e₀ = matMul K (M e₀) := by
  simp [collapsed]

/-- The inserted coordinate is genuinely a new hidden state. -/
def assignmentEquiv : (Sum V Unit → S) ≃ (V → S) × S where
  toFun := fun a => (fun v => a (Sum.inl v), a (Sum.inr ()))
  invFun := fun p => assignment p.1 p.2
  left_inv := by
    intro a
    funext v
    cases v with
    | inl v => rfl
    | inr v => cases v; rfl
  right_inv := by intro p; cases p; rfl

theorem new_vertexFactor (W : E → ℝ) (π : S → ℝ)
    (M : E → Mat S) (K : Mat S) (a : V → S) (y : S) :
    vertexFactor (subdivide G e₀) (weights W) π (matrices M K)
      (Sum.inr ()) (assignment a y) = K (a (G.source e₀)) y := by
  classical
  simp [vertexFactor, subdivide, weights, matrices, assignment,
    Fintype.sum_sum_type]

/-- All other original vertex factors ignore the new coordinate. -/
theorem old_vertexFactor_off (W : E → ℝ) (π : S → ℝ)
    (M : E → Mat S) (K : Mat S) (a : V → S) (y : S)
    (v : V) (hv : v ≠ G.target e₀) :
    vertexFactor (subdivide G e₀) (weights W) π (matrices M K)
      (Sum.inl v) (assignment a y) =
      vertexFactor G W π (collapsed e₀ M K) v a := by
  classical
  by_cases hr : v = G.root
  · subst v
    simp [vertexFactor, subdivide, assignment]
  · simp only [vertexFactor, subdivide, Sum.inl.injEq, hr, if_false,
      Fintype.sum_sum_type, weights, matrices, Sum.elim_inl, Sum.elim_inr,
      Sum.inr_ne_inl, Finset.sum_const_zero, add_zero, assignment]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : e = e₀
    · subst e
      simp [Ne.symm hv]
    · simp [he, collapsed_off e₀ M K he]

/-- The child factor is integrated linearly even when the child is a
reticulation with additional original parents. -/
theorem integrate_child (W : E → ℝ) (π : S → ℝ)
    (M : E → Mat S) (K : Mat S) (a : V → S)
    (hroot : G.target e₀ ≠ G.root)
    (hK : ∀ i, (∑ j, K i j) = 1) :
    (∑ y, K (a (G.source e₀)) y *
      vertexFactor (subdivide G e₀) (weights W) π (matrices M K)
        (Sum.inl (G.target e₀)) (assignment a y)) =
      vertexFactor G W π (collapsed e₀ M K) (G.target e₀) a := by
  classical
  simp only [vertexFactor, subdivide, Sum.inl.injEq, hroot, if_false,
    Fintype.sum_sum_type, weights, matrices, Sum.elim_inl, Sum.elim_inr,
    Sum.inr_ne_inl, Finset.sum_const_zero, add_zero, assignment]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro e _
  by_cases ht : G.target e = G.target e₀
  · simp only [ht, if_true]
    by_cases he : e = e₀
    · subst e
      simp only [if_pos rfl, Sum.elim_inr, collapsed_at]
      unfold matMul
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    · simp only [he, if_false, Sum.elim_inl, collapsed_off e₀ M K he]
      rw [← Finset.sum_mul, hK, one_mul]
  · simp [ht]

/-- Sum out precisely the inserted state, retaining every original state.
No equality of model images or probabilistic factorization is assumed. -/
theorem assignmentMass_subdivide (W : E → ℝ) (π : S → ℝ)
    (M : E → Mat S) (K : Mat S) (a : V → S)
    (hroot : G.target e₀ ≠ G.root)
    (hK : ∀ i, (∑ j, K i j) = 1) :
    (∑ y, RootBlobEdgeIndexed.assignmentMass (subdivide G e₀) π
      (weights W) (matrices M K) (assignment a y)) =
      RootBlobEdgeIndexed.assignmentMass G π W (collapsed e₀ M K) a := by
  classical
  let v₀ := G.target e₀
  let rest := (Finset.univ.erase v₀).prod
    (fun v => vertexFactor G W π (collapsed e₀ M K) v a)
  have hpoint : ∀ y,
      RootBlobEdgeIndexed.assignmentMass (subdivide G e₀) π
        (weights W) (matrices M K) (assignment a y) =
      (K (a (G.source e₀)) y *
        vertexFactor (subdivide G e₀) (weights W) π (matrices M K)
          (Sum.inl v₀) (assignment a y)) * rest := by
    intro y
    rw [← product_vertexFactor, Fintype.prod_sum_type]
    simp only [Fintype.prod_unique, new_vertexFactor]
    rw [← Finset.mul_prod_erase Finset.univ
      (fun v => vertexFactor (subdivide G e₀) (weights W) π (matrices M K)
        (Sum.inl v) (assignment a y)) (Finset.mem_univ v₀)]
    have hrest :
        (Finset.univ.erase v₀).prod
          (fun v => vertexFactor (subdivide G e₀) (weights W) π (matrices M K)
            (Sum.inl v) (assignment a y)) = rest := by
      apply Finset.prod_congr rfl
      intro v hv
      exact old_vertexFactor_off G e₀ W π M K a y v (Finset.mem_erase.mp hv).1
    rw [hrest]
    ring
  simp_rw [hpoint]
  rw [← Finset.sum_mul, integrate_child G e₀ W π M K a hroot hK]
  rw [← product_vertexFactor]
  exact Finset.mul_prod_erase Finset.univ
    (fun v => vertexFactor G W π (collapsed e₀ M K) v a) (Finset.mem_univ v₀)

/-- Exact original observed-law equality, with arbitrary original labels. -/
theorem observedLaw_subdivide (W : E → ℝ) (π : S → ℝ)
    (M : E → Mat S) (K : Mat S)
    (hroot : G.target e₀ ≠ G.root)
    (hK : ∀ i, (∑ j, K i j) = 1) :
    RootBlobEdgeIndexed.observedLaw (subdivide G e₀) π
      (weights W) (matrices M K) =
      RootBlobEdgeIndexed.observedLaw G π W (collapsed e₀ M K) := by
  classical
  funext z
  unfold RootBlobEdgeIndexed.observedLaw
  calc
    (∑ a : Sum V Unit → S,
      if ∀ o, a ((subdivide G e₀).observed o) = z o then
        RootBlobEdgeIndexed.assignmentMass (subdivide G e₀) π
          (weights W) (matrices M K) a else 0) =
      ∑ p : (V → S) × S,
        if ∀ o, p.1 (G.observed o) = z o then
          RootBlobEdgeIndexed.assignmentMass (subdivide G e₀) π
            (weights W) (matrices M K) (assignment p.1 p.2) else 0 := by
      apply Fintype.sum_equiv assignmentEquiv
      intro a
      have ha : assignment (fun v => a (Sum.inl v)) (a (Sum.inr ())) = a :=
        (assignmentEquiv (V := V) (S := S)).symm_apply_apply a
      change (if ∀ o, a (Sum.inl (G.observed o)) = z o then
          RootBlobEdgeIndexed.assignmentMass (subdivide G e₀) π
            (weights W) (matrices M K) a else 0) =
        (if ∀ o, a (Sum.inl (G.observed o)) = z o then
          RootBlobEdgeIndexed.assignmentMass (subdivide G e₀) π
            (weights W) (matrices M K)
              (assignment (fun v => a (Sum.inl v)) (a (Sum.inr ()))) else 0)
      rw [ha]
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro a _
      by_cases ho : ∀ o, a (G.observed o) = z o
      · simp only [ho, if_true]
        exact assignmentMass_subdivide G e₀ W π M K a hroot hK
      · simp [ho]

theorem matrices_open {H : Subgroup (Equiv.Perm S)} {M : E → Mat S} {K : Mat S}
    (hM : ∀ e, OpenTransition H (M e)) (hK : OpenTransition H K) :
    ∀ e, OpenTransition H (matrices M K e) := by
  intro e
  cases e with
  | inl e => exact hM e
  | inr e => exact hK

theorem collapsed_open [Nonempty S]
    {H : Subgroup (Equiv.Perm S)} {M : E → Mat S} {K : Mat S}
    (hM : ∀ e, OpenTransition H (M e)) (hK : OpenTransition H K) :
    ∀ e, OpenTransition H (collapsed e₀ M K e) := by
  intro e
  by_cases he : e = e₀
  · subst e
    rw [collapsed_at]
    exact matMul_open hK (hM e₀)
  · rw [collapsed_off e₀ M K he]
    exact hM e

/-- Full original class in both directions. The selected original matrix is
free; all other matrices can be retained. W is the SAME original function. -/
theorem modelImage_eq_subdivide [Nonempty S]
    (W : E → ℝ) (H : Subgroup (Equiv.Perm S))
    (hroot : G.target e₀ ≠ G.root) :
    RootBlobFullModel.modelImage G W H =
      RootBlobFullModel.modelImage (subdivide G e₀) (weights W) H := by
  classical
  apply Set.ext
  intro L
  constructor
  · rintro ⟨π, M, hπ, hM, hL⟩
    obtain ⟨K, A, hK, hA, hKA⟩ := exists_open_factorization (hM e₀)
    let T := Function.update M e₀ A
    have hT : ∀ e, OpenTransition H (T e) := by
      intro e
      by_cases he : e = e₀
      · subst e
        simpa [T] using hA
      · simpa [T, he] using hM e
    have hc : collapsed e₀ T K = M := by
      funext e
      by_cases he : e = e₀
      · subst e
        simpa [collapsed, T] using hKA
      · simp [collapsed, T, he]
    refine ⟨π, matrices T K, hπ, matrices_open hT hK, ?_⟩
    rw [observedLaw_subdivide G e₀ W π T K hroot hK.1.2, hc]
    exact hL
  · rintro ⟨π, X, hπ, hX, hL⟩
    let M : E → Mat S := fun e => X (Sum.inl e)
    let K : Mat S := X (Sum.inr ())
    have hx : matrices M K = X := by
      funext e
      cases e with
      | inl e => rfl
      | inr e => cases e; rfl
    have hM : ∀ e, OpenTransition H (M e) := fun e => hX (Sum.inl e)
    have hK : OpenTransition H K := hX (Sum.inr ())
    refine ⟨π, collapsed e₀ M K, hπ, collapsed_open e₀ hM hK, ?_⟩
    rw [← observedLaw_subdivide G e₀ W π M K hroot hK.1.2, hx]
    exact hL

theorem graph_admitted (hG : RootBlobEdgeIndexed.GraphAdmitted G) :
    RootBlobEdgeIndexed.GraphAdmitted (subdivide G e₀) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    exact hG.1 (Sum.inl.inj h)
  · intro o h
    exact hG.2.1 o (Sum.inl.inj h)
  · intro e
    cases e with
    | inl e =>
      have hr := hG.2.2.1 e
      by_cases he : e = e₀
      · subst e
        simp only [subdivide, if_pos rfl]
        omega
      · simp only [subdivide, if_neg he]
        omega
    | inr e =>
      cases e
      simp only [subdivide]
      omega
  · intro e h
    cases e with
    | inl e => exact hG.2.2.2.1 e (Sum.inl.inj h)
    | inr e => exact Sum.noConfusion h
  · intro v hv
    cases v with
    | inl v =>
      have hn : v ≠ G.root := fun h => hv (congrArg Sum.inl h)
      obtain ⟨e, he⟩ := hG.2.2.2.2.1 v hn
      exact ⟨Sum.inl e, congrArg Sum.inl he⟩
    | inr v => cases v; exact ⟨Sum.inr (), rfl⟩
  · intro v
    cases v with
    | inl v =>
      constructor
      · intro h
        have hs : ∀ e, G.source e ≠ v := by
          intro e he
          by_cases he₀ : e = e₀
          · subst e
            exact h (Sum.inr ()) (congrArg Sum.inl he)
          · apply h (Sum.inl e)
            simp [subdivide, he₀, he]
        obtain ⟨o, ho⟩ := (hG.2.2.2.2.2 v).mp hs
        exact ⟨o, congrArg Sum.inl ho⟩
      · rintro ⟨o, ho⟩ e he
        have hov : G.observed o = v := Sum.inl.inj ho
        have hs := (hG.2.2.2.2.2 v).mpr ⟨o, hov⟩
        cases e with
        | inl e =>
          by_cases he₀ : e = e₀
          · simp [subdivide, he₀] at he
          · exact hs e (Sum.inl.inj (by simpa [subdivide, he₀] using he))
        | inr e => exact hs e₀ (Sum.inl.inj he)
    | inr v =>
      cases v
      constructor
      · intro h
        exact False.elim (h (Sum.inl e₀) (by simp [subdivide]))
      · rintro ⟨o, ho⟩
        exact False.elim (Sum.noConfusion ho)

theorem weights_admitted (W : E → ℝ)
    (hW : RootBlobEdgeIndexed.WeightsAdmitted G W) :
    RootBlobEdgeIndexed.WeightsAdmitted (subdivide G e₀) (weights W) := by
  classical
  constructor
  · intro e
    cases e with
    | inl e => exact hW.1 e
    | inr e => norm_num [weights]
  · intro v hv
    cases v with
    | inl v =>
      have hn : v ≠ G.root := fun h => hv (congrArg Sum.inl h)
      simpa [subdivide, weights, Fintype.sum_sum_type] using hW.2 v hn
    | inr v => cases v; simp [subdivide, weights, Fintype.sum_sum_type]

def subdivideTwice (e₁ : E) := subdivide (subdivide G e₀) (Sum.inl e₁)

theorem modelImage_eq_subdivideTwice [Nonempty S]
    (e₁ : E) (W : E → ℝ) (H : Subgroup (Equiv.Perm S))
    (hG : RootBlobEdgeIndexed.GraphAdmitted G) :
    RootBlobFullModel.modelImage G W H =
      RootBlobFullModel.modelImage (subdivideTwice G e₀ e₁) (weights (weights W)) H := by
  calc
    _ = RootBlobFullModel.modelImage (subdivide G e₀) (weights W) H :=
      modelImage_eq_subdivide G e₀ W H (hG.2.2.2.1 e₀)
    _ = _ := modelImage_eq_subdivide (subdivide G e₀) (Sum.inl e₁)
      (weights W) H ((graph_admitted G e₀ hG).2.2.2.1 (Sum.inl e₁))

end RootBlobEdgeSubdivision

