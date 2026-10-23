import G4IndependentRoutingBridge
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
UNCOMPILED candidate, 21 October 2026. Paired cap-three per-cell gain bound.
Uses the existing actual-original-parent routing coordinate supplier, GIVEN
its explicit arm-law contract. commonPair is the same-tuple weighted arm
mean, not a newly proved common source-program/kernel identification.
The scalar product lemma is not source-word reflection or a G3 endpoint.
No local Git, worker, compile claim, axiom or sorry is introduced here.
-/
namespace GProgram.G3.PairedCap3Gain

open scoped BigOperators

noncomputable def commonPair (p x y : ℝ) : ℝ := p*x + (1-p)*y

theorem gain_identity (p x y : ℝ) :
    3 * commonPair p x y * GProgram.G4.FourRoot.s2 p x y -
      2 * GProgram.G4.FourRoot.s3 p x y =
    p^3*x^2*(3-2*x) + (1-p)^3*y^2*(3-2*y) + 3*p*(1-p)*x*y := by
  unfold commonPair GProgram.G4.FourRoot.s2 GProgram.G4.FourRoot.s3
  ring

theorem gain_strict (p x y : ℝ) (hp : 0 < p) (hp1 : p < 1)
    (hx : 0 < x) (hx1 : x < 1) (hy : 0 < y) (hy1 : y < 1) :
    GProgram.G4.FourRoot.s3 p x y <
      (3/2 : ℝ) * commonPair p x y * GProgram.G4.FourRoot.s2 p x y := by
  have hh : 0 < 1-p := by linarith
  have hxx : 0 < 3-2*x := by linarith
  have hyy : 0 < 3-2*y := by linarith
  have hpos : 0 < p^3*x^2*(3-2*x) + (1-p)^3*y^2*(3-2*y) +
      3*p*(1-p)*x*y := by positivity
  have h : 0 < 3 * commonPair p x y * GProgram.G4.FourRoot.s2 p x y -
      2 * GProgram.G4.FourRoot.s3 p x y := by
    rw [gain_identity]
    exact hpos
  linarith

theorem word_gain_product_bound {L : Nat} (g : Fin L → ℝ) (A : ℝ)
    (hA : A < 1) (hpos : ∀ i, 0 < g i) (hgain : ∀ i, g i ≤ (3/2 : ℝ)) :
    A * (∏ i, g i) < (3/2 : ℝ)^L := by
  have hp : 0 < ∏ i, g i := Finset.prod_pos (fun i _ => hpos i)
  have hb : (∏ i, g i) ≤ (3/2 : ℝ)^L := by
    calc
      (∏ i, g i) ≤ ∏ _i : Fin L, (3/2 : ℝ) :=
        Finset.prod_le_prod (fun i _ => (hpos i).le) (fun i _ => hgain i)
      _ = (3/2 : ℝ)^L := by simp
  have hs : A * (∏ i, g i) < ∏ i, g i := by
    simpa using mul_lt_mul_of_pos_right hA hp
  exact hs.trans_le hb

section ActualOriginalCoordinates

open Nanuq.Source
open GProgram.G4.IndependentRouting

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
  [DecidableEq V] [DecidableEq E] {N : RootedBinary V E X}

/-- Exact original hybrid/parent IDs in both I coordinates. The arm law and
the weighted same-tuple common mean stay explicit; no full forest law or
clock-generator refinement is assumed as a conclusion. -/
theorem actual_original_private_gain_strict
    (H : GProgram.G2.OriginalHybridParents N) (p x y : ℝ)
    (a b : Nat → ℝ) (ha : FourRootArmLaw a x) (hb : FourRootArmLaw b y)
    (hp : 0 < p) (hp1 : p < 1) (hx : 0 < x) (hx1 : x < 1)
    (hy : 0 < y) (hy1 : y < 1) :
    actualPrivateNoMerger H 3 p a b <
      (3/2 : ℝ) * commonPair p x y * actualPrivateNoMerger H 2 p a b := by
  obtain ⟨h2,h3,_h4⟩ := original_source_coordinates H p x y a b ha hb
  rw [h2,h3]
  exact gain_strict p x y hp hp1 hx hx1 hy hy1

end ActualOriginalCoordinates

#print axioms gain_identity
#print axioms gain_strict
#print axioms word_gain_product_bound
#print axioms actual_original_private_gain_strict

end GProgram.G3.PairedCap3Gain
