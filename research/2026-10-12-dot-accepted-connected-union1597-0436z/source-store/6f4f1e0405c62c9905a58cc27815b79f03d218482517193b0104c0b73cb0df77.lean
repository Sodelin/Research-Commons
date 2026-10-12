import G4IndependentRoutingBridge
import Mathlib.Data.Fintype.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Exact all-finite-root count compression of the no-merger marginal

Dedicated Sol6.1 source-model contribution. The actual independent live-root
assignment sum is grouped by original parent0 root count using mathlib's
powerset-card/binomial sum identities. This reduces the marginal to n+1
count classes. It does not assert that counts determine full labelled forests.
-/

namespace GProgram.G4.BinomialCompression

open scoped BigOperators
open GProgram.G4.IndependentRouting

noncomputable def rootSet {n : Nat} (coin : Fin n → Bool) : Finset (Fin n) :=
  Finset.univ.filter (fun i => coin i = false)

noncomputable def coinOfSet {n : Nat} (s : Finset (Fin n)) : Fin n → Bool :=
  fun i => if i ∈ s then false else true

noncomputable def rootSetEquiv (n : Nat) : (Fin n → Bool) ≃ Finset (Fin n) where
  toFun := rootSet
  invFun := coinOfSet
  left_inv coin := by
    funext i
    cases hc : coin i <;> simp [coinOfSet,rootSet,hc]
  right_inv s := by
    ext i
    by_cases hi : i ∈ s <;> simp [rootSet,coinOfSet,hi]

theorem count0_of_set {n : Nat} (s : Finset (Fin n)) : count0 (coinOfSet s) = s.card := by
  have ht : ∀ i : Fin n, (if coinOfSet s i then 0 else 1) =
      if i ∈ s then (1 : Nat) else 0 := by
    intro i
    by_cases hi : i ∈ s <;> simp [coinOfSet,hi]
  unfold count0
  simp_rw [ht]
  simp

theorem count1_of_set {n : Nat} (s : Finset (Fin n)) : count1 (coinOfSet s) = n-s.card := by
  have h := count_partition (coinOfSet s)
  rw [count0_of_set] at h
  omega

theorem weight_of_set {n : Nat} (u : ℝ) (s : Finset (Fin n)) :
    routingWeight u (coinOfSet s) = u^s.card*(1-u)^(n-s.card) := by
  have ht : ∀ i : Fin n, bitWeight u (coinOfSet s i) = if i ∈ s then u else 1-u := by
    intro i
    by_cases hi : i ∈ s <;> simp [coinOfSet,bitWeight,hi]
  unfold routingWeight
  simp_rw [ht]
  rw [Finset.prod_ite]
  have h0 : Finset.univ.filter (fun i : Fin n => i ∈ s) = s := by ext; simp
  have h1 : Finset.univ.filter (fun i : Fin n => i ∉ s) = Finset.univ \ s := by ext; simp
  rw [h0,h1]
  simp [Finset.card_sdiff_of_subset (Finset.subset_univ s)]

theorem all_root_binomial_sum (n : Nat) (u : ℝ) (a b : Nat → ℝ) :
    privateNoMerger n u a b =
      ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ)*u^k*(1-u)^(n-k)*a k*b (n-k) := by
  unfold privateNoMerger
  rw [← (rootSetEquiv n).symm.sum_comp
    (fun coin => routingWeight u coin*a (count0 coin)*b (count1 coin))]
  change (∑ s : Finset (Fin n), routingWeight u (coinOfSet s)*
    a (count0 (coinOfSet s))*b (count1 (coinOfSet s))) = _
  simp only [weight_of_set,count0_of_set,count1_of_set]
  rw [← Finset.powerset_univ,Finset.sum_powerset]
  simp only [Finset.card_univ,Fintype.card_fin]
  apply Finset.sum_congr rfl
  intro k _
  have h := Finset.sum_powersetCard k (Finset.univ : Finset (Fin n))
    (fun j => u^j*(1-u)^(n-j)*a j*b (n-j))
  simpa only [Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_assoc] using h

section OriginalSource

open Nanuq.Source
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
  [DecidableEq V] [DecidableEq E]
variable {N : RootedBinary V E X}

theorem original_all_root_binomial_sum (H : GProgram.G2.OriginalHybridParents N)
    (n : Nat) (u : ℝ) (a b : Nat → ℝ) :
    actualPrivateNoMerger H n u a b =
      ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ)*u^k*(1-u)^(n-k)*a k*b (n-k) := by
  rw [actualPrivateNoMerger_eq,all_root_binomial_sum]

theorem original_all_root_exponential_coefficients
    (H : GProgram.G2.OriginalHybridParents N) (n : Nat) (u t0 t1 : ℝ)
    (ht0 : 0 ≤ t0) (ht1 : 0 ≤ t1) :
    actualPrivateNoMerger H n u (fun k => firstHoldingKernel k t0)
      (fun k => firstHoldingKernel k t1) =
    ∑ k ∈ Finset.range (n+1), (n.choose k : ℝ)*u^k*(1-u)^(n-k)*
      (Real.exp (-t0))^(k.choose 2)*(Real.exp (-t1))^((n-k).choose 2) := by
  rw [original_all_root_binomial_sum]
  simp_rw [firstHoldingKernel_eq_power ht0,firstHoldingKernel_eq_power ht1]

end OriginalSource

#print axioms original_all_root_binomial_sum
#print axioms original_all_root_exponential_coefficients
#print axioms rootSetEquiv
#print axioms all_root_binomial_sum

end GProgram.G4.BinomialCompression
