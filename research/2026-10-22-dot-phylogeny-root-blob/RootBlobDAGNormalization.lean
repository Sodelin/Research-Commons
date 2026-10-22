import RootBlobOpenProof

/-!
# Ranked finite-DAG normalization

Author: dot (OpenAI), 22 October 2026.
SOURCE-ONLY, UNELABORATED proof terms. NO EXECUTION OR VERIFICATION.
Mathlib source reference: 0df444a360eaa60ab8c11dca51a86af692955474.

This module attempts the actual finite assignment-sum normalization rather
than assuming a probability oracle. The remaining ResolutionCertificate
construction is separate and is not proved or assumed as an axiom here.
-/

open scoped BigOperators
open RootBlobInterfaces RootBlobOpenProof
namespace RootBlobDAGNormalization
universe u v w
variable {S : Type u} [Fintype S]
variable {V : Type v} [Fintype V] [DecidableEq V]

def extendAt (v : V) (s : S) (b : {w : V // w ≠ v} → S) : V → S :=
  fun w => if h : w = v then s else b ⟨w, h⟩

def splitAt (v : V) : (V → S) ≃ S × ({w : V // w ≠ v} → S) where
  toFun := fun a => (a v, fun w => a w.val)
  invFun := fun p => extendAt v p.1 p.2
  left_inv := by
    intro a
    funext w
    by_cases h : w = v
    · subst w; simp [extendAt]
    · simp [extendAt, h]
  right_inv := by
    rintro ⟨s, b⟩
    apply Prod.ext
    · simp [extendAt]
    · funext w
      simp [extendAt, w.property]

theorem extendAt_update_inside (v : V) (s t : S)
    (b : {w : V // w ≠ v} → S) (u : {w : V // w ≠ v}) :
    extendAt v s (Function.update b u t) =
      Function.update (extendAt v s b) u.val t := by
  funext w
  by_cases hw : w = v
  · subst w
    simp [extendAt, Ne.symm u.property]
  · by_cases hu : w = u.val
    · subst w
      simp [extendAt, u.property]
    · have hsub : (⟨w, hw⟩ : {w : V // w ≠ v}) ≠ u := by
        intro he
        exact hu (congrArg Subtype.val he)
      simp [extendAt, hw, hu, hsub]

theorem extendAt_update_outer (v : V) (s t : S)
    (b : {w : V // w ≠ v} → S) :
    extendAt v t b = Function.update (extendAt v s b) v t := by
  funext w
  by_cases hw : w = v
  · subst w; simp [extendAt]
  · simp [extendAt, hw]

theorem prod_split (v : V) (f : V → ℝ) :
    (∏ w, f w) = f v * ∏ w : {w : V // w ≠ v}, f w.val := by
  classical
  calc
    (∏ w, f w) = f v * ∏ w ∈ Finset.univ.erase v, f w :=
      (Finset.mul_prod_erase Finset.univ f (Finset.mem_univ v)).symm
    _ = f v * ∏ w : {w : V // w ≠ v}, f w.val := by
      congr 1
      exact Finset.prod_subtype (Finset.univ.erase v) (by intro w; simp) f

/-- Generic finite elimination theorem. A factor is normalized in its own
coordinate and ignores every distinct coordinate of equal or larger rank. -/
theorem ranked_normalization [Nonempty S]
    (rank : V → ℕ) (f : V → (V → S) → ℝ)
    (hnorm : ∀ v a, (∑ s, f v (Function.update a v s)) = 1)
    (hignore : ∀ v w a s, v ≠ w → rank v ≤ rank w →
      f v (Function.update a w s) = f v a) :
    (∑ a : V → S, ∏ v, f v a) = 1 := by
  classical
  have aux : ∀ n : ℕ, ∀ (A : Type v) [Fintype A] [DecidableEq A],
      Fintype.card A = n →
      ∀ (ρ : A → ℕ) (g : A → (A → S) → ℝ),
      (∀ v a, (∑ s, g v (Function.update a v s)) = 1) →
      (∀ v w a s, v ≠ w → ρ v ≤ ρ w →
        g v (Function.update a w s) = g v a) →
      (∑ a : A → S, ∏ v, g v a) = 1 := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro A _ _ hcard ρ g hgNorm hgIgnore
      rcases isEmpty_or_nonempty A with hA | hA
      · letI : IsEmpty A := hA
        simp
      · letI : Nonempty A := hA
        obtain ⟨v, _, hv⟩ :=
          Finset.exists_max_image Finset.univ ρ Finset.univ_nonempty
        let U := {w : A // w ≠ v}
        let k : S := Classical.choice inferInstance
        let g' : U → (U → S) → ℝ := fun u b => g u.val (extendAt v k b)
        have hnorm' : ∀ u b, (∑ s, g' u (Function.update b u s)) = 1 := by
          intro u b
          change (∑ s, g u.val (extendAt v k (Function.update b u s))) = 1
          simp_rw [extendAt_update_inside]
          exact hgNorm u.val (extendAt v k b)
        have hignore' : ∀ u w b s, u ≠ w → ρ u.val ≤ ρ w.val →
            g' u (Function.update b w s) = g' u b := by
          intro u w b s huw hr
          change g u.val (extendAt v k (Function.update b w s)) =
            g u.val (extendAt v k b)
          rw [extendAt_update_inside]
          apply hgIgnore u.val w.val (extendAt v k b) s
          · intro he
            exact huw (Subtype.ext he)
          · exact hr
        have hlt : Fintype.card U < n := by
          rw [← hcard]
          exact Fintype.card_subtype_lt (x := v) (by intro h; exact h rfl)
        have hi := ih (Fintype.card U) hlt U rfl
          (fun u => ρ u.val) g' hnorm' hignore'
        have hsum : (∑ a : A → S, ∏ w, g w a) =
            ∑ b : U → S, ∑ s : S, ∏ w, g w (extendAt v s b) := by
          calc
            (∑ a : A → S, ∏ w, g w a) =
                ∑ p : S × (U → S), ∏ w, g w ((splitAt v).symm p) := by
              apply Fintype.sum_equiv (splitAt v)
              intro a
              rw [Equiv.symm_apply_apply]
            _ = ∑ b : U → S, ∑ s : S, ∏ w, g w (extendAt v s b) := by
              rw [Fintype.sum_prod_type, Finset.sum_comm]
              rfl
        rw [hsum]
        calc
          (∑ b : U → S, ∑ s : S, ∏ w, g w (extendAt v s b)) =
              ∑ b : U → S, ∏ u, g' u b := by
            apply Finset.sum_congr rfl
            intro b _
            have hrest : ∀ s, (∏ u : U, g u.val (extendAt v s b)) =
                ∏ u : U, g' u b := by
              intro s
              apply Finset.prod_congr rfl
              intro u _
              change g u.val (extendAt v s b) = g u.val (extendAt v k b)
              rw [extendAt_update_outer v k s b]
              exact hgIgnore u.val v (extendAt v k b) s u.property
                (hv u.val (Finset.mem_univ _))
            have hvNorm : (∑ s, g v (extendAt v s b)) = 1 := by
              calc
                (∑ s, g v (extendAt v s b)) =
                    ∑ s, g v (Function.update (extendAt v k b) v s) := by
                  apply Finset.sum_congr rfl
                  intro s _
                  rw [extendAt_update_outer v k s b]
                _ = 1 := hgNorm v (extendAt v k b)
            simp_rw [prod_split v, hrest]
            rw [← Finset.sum_mul, hvNorm, one_mul]
          _ = 1 := hi
  exact aux (Fintype.card V) V rfl rank f hnorm hignore

namespace Edge
open RootBlobEdgeIndexed
variable {E : Type w} [Fintype E]
variable (N : RootBlobEdgeIndexed.Network V E (Fin 2)) (W : E → ℝ)
variable (H : Subgroup (Equiv.Perm S))

noncomputable def localFactor (π : S → ℝ) (M : E → Mat S)
    (v : V) (a : V → S) : ℝ := by
  classical
  exact if v = N.root then π (a N.root) else
    ∑ e, if N.target e = v then W e * M e (a (N.source e)) (a v) else 0

theorem product_localFactor (π : S → ℝ) (M : E → Mat S) (a : V → S) :
    (∏ v, localFactor N W π M v a) =
      RootBlobEdgeIndexed.assignmentMass N π W M a := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ
    (fun v => localFactor N W π M v a) (Finset.mem_univ N.root)]
  unfold RootBlobEdgeIndexed.assignmentMass
  simp only [localFactor, if_pos rfl]
  congr 1
  apply Finset.prod_congr rfl
  intro v hv
  exact if_neg (Finset.mem_erase.mp hv).1

theorem localFactor_normalized (π : S → ℝ) (M : E → Mat S)
    (hG : RootBlobEdgeIndexed.GraphAdmitted N)
    (hW : RootBlobEdgeIndexed.WeightsAdmitted N W)
    (hπ : RootAdmitted H π) (hM : ∀ e, OpenTransition H (M e)) :
    ∀ v a, (∑ s, localFactor N W π M v (Function.update a v s)) = 1 := by
  classical
  intro v a
  by_cases hv : v = N.root
  · subst v
    simpa only [localFactor, if_pos rfl, Function.update_self] using hπ.1.2
  · simp only [localFactor, if_neg hv]
    rw [Finset.sum_comm]
    calc
      (∑ e, ∑ s, if N.target e = v then
        W e * M e (Function.update a v s (N.source e))
          (Function.update a v s v) else 0) =
          ∑ e, if N.target e = v then W e else 0 := by
        apply Finset.sum_congr rfl
        intro e _
        by_cases he : N.target e = v
        · have hs : N.source e ≠ v := by
            intro h
            have hr := hG.2.2.1 e
            rw [h, he] at hr
            exact (Nat.lt_irrefl (N.rank v)) hr
          simp only [if_pos he, Function.update_of_ne hs, Function.update_self]
          rw [← Finset.mul_sum, (hM e).1.2, mul_one]
        · simp only [if_neg he, Finset.sum_const_zero]
      _ = 1 := hW.2 v hv

theorem localFactor_ignores_future (π : S → ℝ) (M : E → Mat S)
    (hG : RootBlobEdgeIndexed.GraphAdmitted N) :
    ∀ v w a s, v ≠ w → N.rank v ≤ N.rank w →
      localFactor N W π M v (Function.update a w s) =
        localFactor N W π M v a := by
  classical
  intro v w a s hvw hrank
  by_cases hv : v = N.root
  · subst v
    simp only [localFactor, if_pos rfl, Function.update_of_ne hvw]
  · simp only [localFactor, if_neg hv]
    apply Finset.sum_congr rfl
    intro e _
    by_cases he : N.target e = v
    · have hs : N.source e ≠ w := by
        intro h
        have hlt := hG.2.2.1 e
        rw [h, he] at hlt
        exact (not_lt_of_ge hrank) hlt
      simp only [if_pos he, Function.update_of_ne hs, Function.update_of_ne hvw]
    · simp only [if_neg he]

theorem assignmentMass_total [Nonempty S]
    (π : S → ℝ) (M : E → Mat S)
    (hG : RootBlobEdgeIndexed.GraphAdmitted N)
    (hW : RootBlobEdgeIndexed.WeightsAdmitted N W)
    (hπ : RootAdmitted H π) (hM : ∀ e, OpenTransition H (M e)) :
    (∑ a : V → S, RootBlobEdgeIndexed.assignmentMass N π W M a) = 1 := by
  simp_rw [← product_localFactor N W π M]
  exact ranked_normalization N.rank (localFactor N W π M)
    (localFactor_normalized N W H π M hG hW hπ hM)
    (localFactor_ignores_future N W π M hG)

theorem pairLaw_total_eq_assignmentMass (π : S → ℝ) (M : E → Mat S) :
    (∑ i, ∑ j, RootBlobEdgeIndexed.pairLaw N π W M i j) =
      ∑ a : V → S, RootBlobEdgeIndexed.assignmentMass N π W M a := by
  classical
  unfold RootBlobEdgeIndexed.pairLaw RootBlobEdgeIndexed.observedLaw
  rw [Finset.sum_comm]
  conv_lhs =>
    arg 2
    ext j
    rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  have hc : ∀ i j, (∀ o : Fin 2,
      a (N.observed o) = if o = 0 then i else j) ↔
      a (N.observed 0) = i ∧ a (N.observed 1) = j := by
    intro i j
    constructor
    · intro h
      exact ⟨by simpa using h 0, by simpa using h 1⟩
    · rintro ⟨h0, h1⟩ o
      fin_cases o
      · simpa using h0
      · simpa using h1
  simp_rw [hc]
  have hinner : ∀ j,
      (∑ i, if a (N.observed 0) = i ∧ a (N.observed 1) = j
        then RootBlobEdgeIndexed.assignmentMass N π W M a else 0) =
      if a (N.observed 1) = j then RootBlobEdgeIndexed.assignmentMass N π W M a
      else 0 := by
    intro j
    by_cases hj : a (N.observed 1) = j
    · simp [hj]
    · simp [hj]
  simp_rw [hinner]
  simp

theorem sourceNormalization [Nonempty S]
    (hG : RootBlobEdgeIndexed.GraphAdmitted N)
    (hW : RootBlobEdgeIndexed.WeightsAdmitted N W) :
    RootBlobOpenProof.Edge.SourceNormalization N W H := by
  intro π M hπ hM
  rw [pairLaw_total_eq_assignmentMass N W π M]
  exact assignmentMass_total N W H π M hG hW hπ hM

/-- Both directions now need only the source-faithful resolution certificate,
not a separate unproved normalization or positive-invariance assertion. -/
theorem openImageClaim_of_resolution [Nonempty S]
    {R : Type*} [Fintype R]
    (hresolve : RootBlobEdgeIndexed.GraphAdmitted N →
      RootBlobEdgeIndexed.WeightsAdmitted N W →
      RootBlobOpenProof.Edge.ResolutionCertificate N W H R) :
    RootBlobEdgeIndexed.OpenImageClaim N W H :=
  RootBlobOpenProof.Edge.openImageClaim_of_obligations N W H hresolve
    (sourceNormalization N W H)

end Edge
end RootBlobDAGNormalization
