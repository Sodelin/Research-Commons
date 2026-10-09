import ActualBigonSurvival
import G4AllRootBinomialCompression

/-! Reuses the accepted all-root binomial compiler after binding the actual
source pulse/epoch law. No new count-compression proof. dot, 9 October 2026. -/
namespace DotG34.ActualBigonBinomial
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceActualHoldingClocks
open DotG34.ActualBigonRate DotG34.ActualBigonSurvival
open GProgram.G4.IndependentRouting GProgram.G4.BinomialCompression
open scoped Classical BigOperators NNReal

noncomputable def reindexCoin {Site : Type*} {n : ℕ} (e : Fin n ≃ Site) :
    (Site → Bool) ≃ (Fin n → Bool) where
  toFun c := fun i => c (e i)
  invFun c := fun i => c (e.symm i)
  left_inv c := by funext i; simp
  right_inv c := by funext i; simp

lemma reindex_count {Site : Type*} [Fintype Site] {n : ℕ}
    (e : Fin n ≃ Site) (c : Fin n → Bool) (b : Bool) :
    coinCount ((reindexCoin e).symm c) b = coinCount c b := by
  unfold coinCount
  symm
  apply Finset.card_equiv e
  intro i
  simp [reindexCoin]

lemma count_false {n : ℕ} (c : Fin n → Bool) : coinCount c false = count0 c := by
  have h := (Finset.sum_boole (R := ℕ) (fun i : Fin n => c i = false) Finset.univ).symm
  have hc : coinCount c false = ∑ i : Fin n, if c i = false then (1 : ℕ) else 0 := by
    simpa [coinCount] using h
  rw [hc]
  unfold count0
  apply Finset.sum_congr rfl
  intro i _
  cases c i <;> simp [count0]

lemma count_true {n : ℕ} (c : Fin n → Bool) : coinCount c true = count1 c := by
  have h := (Finset.sum_boole (R := ℕ) (fun i : Fin n => c i = true) Finset.univ).symm
  have hc : coinCount c true = ∑ i : Fin n, if c i = true then (1 : ℕ) else 0 := by
    simpa [coinCount] using h
  rw [hc]
  unfold count1
  apply Finset.sum_congr rfl
  intro i _
  cases c i <;> simp [count1]

lemma reindex_weight {Site : Type*} [Fintype Site] {n : ℕ}
    (e : Fin n ≃ Site) (c : Fin n → Bool) (g : ℝ) :
    (∏ i : Site, if ((reindexCoin e).symm c) i then g else 1-g) =
      routingWeight (1-g) c := by
  rw [← e.prod_comp]
  unfold routingWeight
  apply Finset.prod_congr rfl
  intro i _
  cases hc : c i <;> simp [reindexCoin, GProgram.G4.IndependentRouting.bitWeight, hc]

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Strict source rates and a positive physical interval give precisely the
strict arm-survival domain required by the earlier paired guard. -/
theorem actual_arm_survival_strict (r : PositivePairRates E) (e : E)
    (t : ℝ≥0) (ht : 0 < t) :
    0 < Real.exp (-(pairRate r (some e)*(t:ℝ))) ∧
      Real.exp (-(pairRate r (some e)*(t:ℝ))) < 1 := by
  constructor
  · exact Real.exp_pos _
  · apply Real.exp_lt_one_iff.mpr
    exact neg_neg_of_pos (mul_pos (pairRate_pos r (some e)) ht)

theorem actual_bigon_private_sum (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (H : GProgram.G2.OriginalHybridParents N)
    (gamma : unitInterval) (t : ℝ≥0) (s : Code N sample)
    (hall : ∀ l ∈ (state s).live, (state s).location l = .node H.hybrid)
    (n : ℕ) (e : Fin n ≃ AtNode (state s) H.hybrid) :
    (((sourceProgram N r [.boundary (.independent H gamma), .interval t] s).map
      liveCard) (liveCard s)).toReal =
    privateNoMerger n (1-(gamma:ℝ))
      (fun k => (Real.exp (-(pairRate r (some H.parent0)*(t:ℝ))))^(k.choose 2))
      (fun k => (Real.exp (-(pairRate r (some H.parent1)*(t:ℝ))))^(k.choose 2)) := by
  rw [actual_bigon_survival N r H gamma t s hall]
  rw [← (reindexCoin e).symm.sum_comp]
  unfold privateNoMerger
  apply Finset.sum_congr rfl
  intro c _
  rw [reindex_weight, reindex_count, reindex_count, count_false, count_true]

/-- The previously accepted binomial compiler now evaluates the literal
original source event. No enumeration or root-count bound is supplied. -/
theorem actual_bigon_binomial (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (H : GProgram.G2.OriginalHybridParents N)
    (gamma : unitInterval) (t : ℝ≥0) (s : Code N sample)
    (hall : ∀ l ∈ (state s).live, (state s).location l = .node H.hybrid) :
    let n := Fintype.card (AtNode (state s) H.hybrid)
    (((sourceProgram N r [.boundary (.independent H gamma), .interval t] s).map
      liveCard) (liveCard s)).toReal =
      ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ)*(1-(gamma:ℝ))^k*(gamma:ℝ)^(n-k)*
        (Real.exp (-(pairRate r (some H.parent0)*(t:ℝ))))^(k.choose 2)*
        (Real.exp (-(pairRate r (some H.parent1)*(t:ℝ))))^((n-k).choose 2) := by
  dsimp only
  rw [actual_bigon_private_sum N r H gamma t s hall _ (Fintype.equivFin _).symm,
    all_root_binomial_sum]
  simp only [sub_sub_cancel]

#print axioms actual_bigon_private_sum
#print axioms actual_bigon_binomial
end DotG34.ActualBigonBinomial
