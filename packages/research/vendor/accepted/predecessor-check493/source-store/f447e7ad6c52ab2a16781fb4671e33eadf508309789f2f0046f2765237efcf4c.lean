import G7FullEpochPolynomial
import ActualBigonSurvival
import UnifiedLean.Source.SourceCalendarCompiler

/-! Polynomial rows of actual original-node operations with a single original
hybrid gamma bank. CURRENT live-owner coins and stored COMMON registers are used.
The real coin product identity is reused from the accepted G34 source provider. -/
namespace GProgram.G7.OriginalBoundaryPolynomial
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourceCalendarCompiler
open DotG34.ActualBigonSurvival
open scoped Classical BigOperators NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def coinPolynomial {Site : Type*} [Fintype Site] (coin : Site → Bool) : Polynomial ℚ :=
  ∏ i : Site, if coin i then Polynomial.X else 1-Polynomial.X

lemma coinPolynomial_eval {Site : Type*} [Fintype Site] (coin : Site → Bool) (g : ℝ) :
    Polynomial.eval₂ (Rat.castHom ℝ) g (coinPolynomial coin) =
      ∏ i : Site, if coin i then g else 1-g := by
  simp only [coinPolynomial,Polynomial.eval₂_finsetProd]
  apply Finset.prod_congr rfl
  intro i _
  cases coin i <;> simp

noncomputable def pulsePolynomial {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample)
    {O : Type*} (f : Code N sample → O) (o : O) : Polynomial ℚ :=
  ∑ coin : AtNode (state s) H.hybrid → Bool,
    if f (pulseCode H s coin) = o then coinPolynomial coin else 0

theorem actual_pulse_polynomial {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample)
    {O : Type*} (f : Code N sample → O) (o : O) (gamma : unitInterval) :
    Polynomial.eval₂ (Rat.castHom ℝ) (gamma:ℝ) (pulsePolynomial H s f o) =
      ((independentPulseKernel H gamma s).map f o).toReal := by
  rw [independentPulseKernel,PMF.map_comp,map_probability_real]
  simp only [pulsePolynomial,Polynomial.eval₂_finsetSum,Function.comp_def]
  apply Finset.sum_congr rfl
  intro coin _
  rw [actual_coin_mass]
  by_cases h : f (pulseCode H s coin) = o
  · simp only [if_pos h,mul_one]
    exact coinPolynomial_eval coin gamma
  · simp [h]

noncomputable def embedAt {I : Type*} (i : I) (p : Polynomial ℚ) : MvPolynomial I ℚ :=
  p.sum (fun n a => MvPolynomial.C a * MvPolynomial.X i ^ n)

lemma embedAt_eval {I : Type*} (x : I → ℝ) (i : I) (p : Polynomial ℚ) :
    MvPolynomial.eval₂ (Rat.castHom ℝ) x (embedAt i p) =
      Polynomial.eval₂ (Rat.castHom ℝ) (x i) p := by
  simp [embedAt,Polynomial.eval₂_eq_sum,Polynomial.sum_def,MvPolynomial.eval₂_mul]

noncomputable def constantPolynomial {I A O : Type*} (f : A → O) (a : A) (o : O) :
    MvPolynomial I ℚ := MvPolynomial.C (if f a = o then 1 else 0)

lemma constantPolynomial_eval {I A O : Type*} (x : I → ℝ) (f : A → O) (a : A) (o : O) :
    MvPolynomial.eval₂ (Rat.castHom ℝ) x (constantPolynomial f a o) =
      ((PMF.pure a).map f o).toReal := by
  rw [PMF.pure_map]
  by_cases h : f a = o
  · simp [constantPolynomial,PMF.pure_apply,h]
  · simp [constantPolynomial,PMF.pure_apply,h,Ne.symm h]

noncomputable def nodePolynomial (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool) (v : V)
    (s : Code N sample) (o : SelectedIndex N sample Finset.univ) : MvPolynomial (Hybrid N) ℚ :=
  if hr : v = N.root then constantPolynomial (projection N Finset.univ) (rootCode N s) o
  else if hh : N.graph.IsHybrid v then
    if common ⟨v,hh⟩ then constantPolynomial (projection N Finset.univ)
      (pulseCode (H.parents ⟨v,hh⟩) s (fun _ => (state s).register (H.parents ⟨v,hh⟩).hybrid)) o
    else embedAt ⟨v,hh⟩ (pulsePolynomial (H.parents ⟨v,hh⟩) s (projection N Finset.univ) o)
  else constantPolynomial (projection N Finset.univ)
    (ordinaryCode N s ((defaultSelector N).edge ⟨v,hr⟩)) o

theorem actual_original_node_polynomial (N : RootedBinary V E X) {sample : Copy → X}
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool) (v : V)
    (s : Code N sample) (o : SelectedIndex N sample Finset.univ)
    (gamma : Hybrid N → unitInterval) :
    MvPolynomial.eval₂ (Rat.castHom ℝ) (fun h => (gamma h:ℝ)) (nodePolynomial N H common v s o) =
      ((boundaryKernel N (originalNodeOperation N H gamma common v) s).map
        (projection N Finset.univ) o).toReal := by
  by_cases hr : v = N.root
  · simp only [nodePolynomial,dif_pos hr,originalNodeOperation,boundaryKernel]
    exact constantPolynomial_eval _ _ _ _
  · by_cases hh : N.graph.IsHybrid v
    · by_cases hc : common ⟨v,hh⟩ = true
      · simp only [nodePolynomial,dif_neg hr,dif_pos hh,if_pos hc,originalNodeOperation,boundaryKernel]
        exact constantPolynomial_eval _ _ _ _
      · simp only [nodePolynomial,dif_neg hr,dif_pos hh,if_neg hc,originalNodeOperation,boundaryKernel]
        rw [embedAt_eval]
        exact actual_pulse_polynomial _ _ _ _ _
    · simp only [nodePolynomial,dif_neg hr,dif_neg hh,originalNodeOperation,boundaryKernel]
      exact constantPolynomial_eval _ _ _ _

end GProgram.G7.OriginalBoundaryPolynomial
