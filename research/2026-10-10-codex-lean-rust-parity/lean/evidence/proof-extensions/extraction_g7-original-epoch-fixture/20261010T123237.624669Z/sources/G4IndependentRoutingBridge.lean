import G2LiveLineageRouting
import G1SharedRegisterStress
import Mathlib.Data.Nat.Choose.Basic
import Lean.Elab.Tactic.Omega
import G4FourRootPositivity
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.NormNum

/-!
# Source-mode independent live-token routing to no-merger coordinates

Dedicated Sol6.1 Lean contribution. Fixed original hybrid parent IDs and one
coin per LIVE input forest root are retained. The explicit finite sum below
uses independent product routing weights; each live root goes to exactly one
parent. Earlier coalesced copy labels remain attached through LiveAncestry.
Generic arm no-merger kernels are supplied separately. Their continuous-time
Kingman/source interpretation is not assumed as the desired bigon polynomial.
-/

namespace GProgram.G4.IndependentRouting

open scoped BigOperators

noncomputable def bitWeight (u : ℝ) (bit : Bool) : ℝ := if bit then 1-u else u

noncomputable def routingWeight {n : Nat} (u : ℝ) (coin : Fin n → Bool) : ℝ :=
  ∏ i, bitWeight u (coin i)

def count0 {n : Nat} (coin : Fin n → Bool) : Nat := ∑ i, if coin i then 0 else 1
def count1 {n : Nat} (coin : Fin n → Bool) : Nat := ∑ i, if coin i then 1 else 0

/-- Private independent parent populations: each arm receives its routed live
root count, preserving the same fixed kernel at all input sizes. -/
noncomputable def privateNoMerger (n : Nat) (u : ℝ) (arm0 arm1 : Nat → ℝ) : ℝ :=
  ∑ coin : Fin n → Bool,
    routingWeight u coin * arm0 (count0 coin) * arm1 (count1 coin)

theorem sum_vectors_succ {n : Nat} (f : (Fin (n+1) → Bool) → ℝ) :
    (∑ coin, f coin) = ∑ b : Bool, ∑ coin : Fin n → Bool, f (Fin.cons b coin) := by
  classical
  calc
    (∑ coin, f coin) = ∑ p : Bool × (Fin n → Bool), f (Fin.cons p.1 p.2) :=
      ((Fin.consEquiv (fun _ : Fin (n+1) => Bool)).sum_comp f).symm
    _ = _ := Fintype.sum_prod_type _

theorem sum_vectors_zero (f : (Fin 0 → Bool) → ℝ) :
    (∑ coin, f coin) = f default := by
  rw [Fintype.sum_unique]
  congr 1
  exact Subsingleton.elim _ _

theorem count0_cons {n : Nat} (b : Bool) (coin : Fin n → Bool) :
    count0 (Fin.cons b coin) = (if b then 0 else 1) + count0 coin := by
  simp only [count0,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

theorem count1_cons {n : Nat} (b : Bool) (coin : Fin n → Bool) :
    count1 (Fin.cons b coin) = (if b then 1 else 0) + count1 coin := by
  simp only [count1,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]

theorem count_partition {n : Nat} (coin : Fin n → Bool) :
    count0 coin + count1 coin = n := by
  unfold count0 count1
  rw [← Finset.sum_add_distrib]
  have ht : ∀ i : Fin n, (if coin i then 0 else 1) + (if coin i then 1 else 0) = 1 := by
    intro i
    cases coin i <;> rfl
  simp [ht]

theorem routingWeight_cons {n : Nat} (u : ℝ) (b : Bool) (coin : Fin n → Bool) :
    routingWeight u (Fin.cons b coin) = bitWeight u b * routingWeight u coin := by
  simp [routingWeight,Fin.prod_univ_succ]

theorem routingWeight_normalized (n : Nat) (u : ℝ) :
    (∑ coin : Fin n → Bool, routingWeight u coin) = 1 := by
  induction n with
  | zero => simp [routingWeight]
  | succ n ih =>
    rw [sum_vectors_succ]
    simp [routingWeight_cons,← Finset.mul_sum,ih,Fintype.sum_bool,bitWeight]

theorem routingWeight_nonnegative {n : Nat} {u : ℝ} (hu : 0 ≤ u) (hu1 : u ≤ 1)
    (coin : Fin n → Bool) : 0 ≤ routingWeight u coin := by
  unfold routingWeight
  apply Finset.prod_nonneg
  intro i _
  cases coin i <;> simp [bitWeight] <;> linarith

theorem generic_two (u : ℝ) (a b : Nat → ℝ) :
    privateNoMerger 2 u a b =
      u^2*a 2*b 0+2*u*(1-u)*a 1*b 1+(1-u)^2*a 0*b 2 := by
  simp only [privateNoMerger,sum_vectors_succ,sum_vectors_zero,Fintype.sum_bool,
    routingWeight_cons,count0_cons,count1_cons]
  norm_num [bitWeight,routingWeight,count0,count1,Fin.prod_univ_zero,Fin.sum_univ_zero]
  ring

theorem generic_three (u : ℝ) (a b : Nat → ℝ) :
    privateNoMerger 3 u a b =
      u^3*a 3*b 0+3*u^2*(1-u)*a 2*b 1+
      3*u*(1-u)^2*a 1*b 2+(1-u)^3*a 0*b 3 := by
  simp only [privateNoMerger,sum_vectors_succ,sum_vectors_zero,Fintype.sum_bool,
    routingWeight_cons,count0_cons,count1_cons]
  norm_num [bitWeight,routingWeight,count0,count1,Fin.prod_univ_zero,Fin.sum_univ_zero]
  ring

theorem generic_four (u : ℝ) (a b : Nat → ℝ) :
    privateNoMerger 4 u a b =
      u^4*a 4*b 0+4*u^3*(1-u)*a 3*b 1+6*u^2*(1-u)^2*a 2*b 2+
      4*u*(1-u)^3*a 1*b 3+(1-u)^4*a 0*b 4 := by
  simp only [privateNoMerger,sum_vectors_succ,sum_vectors_zero,Fintype.sum_bool,
    routingWeight_cons,count0_cons,count1_cons]
  norm_num [bitWeight,routingWeight,count0,count1,Fin.prod_univ_zero,Fin.sum_univ_zero]
  ring

/-- Finite arm-power contract, independent of the desired bigon formula. -/
def FourRootArmLaw (arm : Nat → ℝ) (x : ℝ) : Prop :=
  arm 0 = 1 ∧ arm 1 = 1 ∧ arm 2 = x ∧ arm 3 = x^3 ∧ arm 4 = x^6

/-- The explicit exponential first-holding-clock model, with one unit-rate
unordered-pair merger hazard per live pair. Equality with the full biological
source's first-merge event remains a separate source-generator obligation. -/
noncomputable def firstHoldingKernel (k : Nat) (duration : ℝ) : ℝ :=
  if k ≤ 1 then 1 else GProgram.G1.pairSurvival (k.choose 2 : ℝ) duration

theorem firstHoldingKernel_eq_power {duration : ℝ} (ht : 0 ≤ duration) (k : Nat) :
    firstHoldingKernel k duration = (Real.exp (-duration))^(k.choose 2) := by
  by_cases hk : k ≤ 1
  · have hc : k.choose 2 = 0 := Nat.choose_eq_zero_of_lt (by omega)
    simp [firstHoldingKernel,hk,hc]
  · have hc : 0 < (k.choose 2 : ℝ) := by
      exact_mod_cast Nat.choose_pos (show 2 ≤ k by omega)
    rw [firstHoldingKernel,if_neg hk,GProgram.G1.pairSurvival_eq_exp hc ht,
      ← Real.exp_nat_mul]
    congr 1
    ring

theorem exponential_four_root_arm_law {duration : ℝ} (ht : 0 ≤ duration) :
    FourRootArmLaw (fun k => firstHoldingKernel k duration) (Real.exp (-duration)) := by
  norm_num [FourRootArmLaw,firstHoldingKernel_eq_power ht,Nat.choose]

section OriginalSource

open Nanuq.Source

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]
variable {N : RootedBinary V E X}

theorem actual_parent0_count {n : Nat} (H : GProgram.G2.OriginalHybridParents N)
    (coin : Fin n → Bool) :
    (Finset.univ.filter (fun i => H.parent (coin i) = H.parent0)).card = count0 coin := by
  classical
  have hcard : (Finset.univ.filter (fun i => H.parent (coin i) = H.parent0)).card =
      ∑ i, if H.parent (coin i) = H.parent0 then (1 : Nat) else 0 := by
    simpa using (Finset.sum_boole (R := Nat)
      (fun i : Fin n => H.parent (coin i) = H.parent0) Finset.univ).symm
  rw [hcard]
  unfold count0
  apply Finset.sum_congr rfl
  intro i _
  cases hc : coin i <;> simp [GProgram.G2.OriginalHybridParents.parent,hc,
    H.different,H.different.symm]

theorem actual_parent1_count {n : Nat} (H : GProgram.G2.OriginalHybridParents N)
    (coin : Fin n → Bool) :
    (Finset.univ.filter (fun i => H.parent (coin i) = H.parent1)).card = count1 coin := by
  classical
  have hcard : (Finset.univ.filter (fun i => H.parent (coin i) = H.parent1)).card =
      ∑ i, if H.parent (coin i) = H.parent1 then (1 : Nat) else 0 := by
    simpa using (Finset.sum_boole (R := Nat)
      (fun i : Fin n => H.parent (coin i) = H.parent1) Finset.univ).symm
  rw [hcard]
  unfold count1
  apply Finset.sum_congr rfl
  intro i _
  cases hc : coin i <;> simp [GProgram.G2.OriginalHybridParents.parent,hc,
    H.different,H.different.symm]

/-- Same original hybrid and parent IDs, same u, same two arm kernels for every
input size. Product arm kernel explicitly specifies private independent arms. -/
noncomputable def actualPrivateNoMerger (H : GProgram.G2.OriginalHybridParents N)
    (n : Nat) (u : ℝ) (a b : Nat → ℝ) : ℝ := by
  classical
  exact ∑ coin : Fin n → Bool, routingWeight u coin *
    a ((Finset.univ.filter (fun i => H.parent (coin i) = H.parent0)).card) *
    b ((Finset.univ.filter (fun i => H.parent (coin i) = H.parent1)).card)

theorem actualPrivateNoMerger_eq (H : GProgram.G2.OriginalHybridParents N)
    (n : Nat) (u : ℝ) (a b : Nat → ℝ) :
    actualPrivateNoMerger H n u a b = privateNoMerger n u a b := by
  classical
  unfold actualPrivateNoMerger privateNoMerger
  apply Finset.sum_congr rfl
  intro coin _
  rw [actual_parent0_count,actual_parent1_count]

/-- The desired three bigon polynomials are CONCLUSIONS of independent live-root
routing enumeration. Arm power laws and private arm independence stay explicit. -/
theorem original_source_coordinates (H : GProgram.G2.OriginalHybridParents N)
    (u x y : ℝ) (a b : Nat → ℝ) (ha : FourRootArmLaw a x) (hb : FourRootArmLaw b y) :
    actualPrivateNoMerger H 2 u a b = GProgram.G4.FourRoot.s2 u x y ∧
    actualPrivateNoMerger H 3 u a b = GProgram.G4.FourRoot.s3 u x y ∧
    actualPrivateNoMerger H 4 u a b = GProgram.G4.FourRoot.s4 u x y := by
  rcases ha with ⟨ha0,ha1,ha2,ha3,ha4⟩
  rcases hb with ⟨hb0,hb1,hb2,hb3,hb4⟩
  simp only [actualPrivateNoMerger_eq,generic_two,generic_three,generic_four,
    ha0,ha1,ha2,ha3,ha4,hb0,hb1,hb2,hb3,hb4,
    GProgram.G4.FourRoot.s2,GProgram.G4.FourRoot.s3,GProgram.G4.FourRoot.s4]
  constructor
  · ring
  constructor <;> ring

/-- Fully explicit exponential first-holding MODEL. The remaining source step
is identifying actual Kingman arm first-merge laws with this modeled clock. -/
theorem exponential_model_original_coordinates (H : GProgram.G2.OriginalHybridParents N)
    (u t0 t1 : ℝ) (ht0 : 0 ≤ t0) (ht1 : 0 ≤ t1) :
    let a := fun k => firstHoldingKernel k t0
    let b := fun k => firstHoldingKernel k t1
    actualPrivateNoMerger H 2 u a b = GProgram.G4.FourRoot.s2 u (Real.exp (-t0)) (Real.exp (-t1)) ∧
    actualPrivateNoMerger H 3 u a b = GProgram.G4.FourRoot.s3 u (Real.exp (-t0)) (Real.exp (-t1)) ∧
    actualPrivateNoMerger H 4 u a b = GProgram.G4.FourRoot.s4 u (Real.exp (-t0)) (Real.exp (-t1)) := by
  exact original_source_coordinates H u _ _ _ _
    (exponential_four_root_arm_law ht0) (exponential_four_root_arm_law ht1)

end OriginalSource

#print axioms exponential_model_original_coordinates
#print axioms original_source_coordinates
#print axioms exponential_four_root_arm_law
#print axioms actual_parent0_count
#print axioms generic_two
#print axioms generic_three
#print axioms generic_four
#print axioms routingWeight_normalized

end GProgram.G4.IndependentRouting
