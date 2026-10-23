import G3PairedCap3Gain

/-!
UNCOMPILED additive routing-layer candidate, 21 October 2026.
One common bit routes every current input root to the SAME original parent
edge. Explicit private arm kernels are supplied just as in the existing
G4IndependentRoutingBridge. This is not a proved identification with the
native sourceProgram, original register prior, or Kingman transition law.
The common/independent statements use ONE H,p,a,b tuple.
-/
namespace GProgram.G3.OriginalCommonCap3Routing

open scoped BigOperators
open Nanuq.Source GProgram.G4.IndependentRouting
open GProgram.G3.PairedCap3Gain

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
  [DecidableEq V] [DecidableEq E] {N : RootedBinary V E X}

/-- A fresh common Bernoulli bit, used for the complete current forest.
Counts refer to the physical original parent IDs. Arm-law and full source
bank/program refinement obligations are deliberately not hidden as fields. -/
noncomputable def actualPrivateCommonNoMerger
    (H : GProgram.G2.OriginalHybridParents N) (n : Nat) (p : ℝ)
    (a b : Nat → ℝ) : ℝ := by
  classical
  exact ∑ bit : Bool, bitWeight p bit *
    a ((Finset.univ.filter (fun _i : Fin n => H.parent bit = H.parent0)).card) *
    b ((Finset.univ.filter (fun _i : Fin n => H.parent bit = H.parent1)).card)

theorem original_common_enumeration
    (H : GProgram.G2.OriginalHybridParents N) (n : Nat) (p : ℝ)
    (a b : Nat → ℝ) :
    actualPrivateCommonNoMerger H n p a b =
      p * a n * b 0 + (1-p) * a 0 * b n := by
  classical
  simp [actualPrivateCommonNoMerger,Fintype.sum_bool,bitWeight,
    GProgram.G2.OriginalHybridParents.parent,H.different,H.different.symm] <;> ring

theorem original_common_cap3_coordinates
    (H : GProgram.G2.OriginalHybridParents N) (p x y : ℝ)
    (a b : Nat → ℝ) (ha : FourRootArmLaw a x) (hb : FourRootArmLaw b y) :
    actualPrivateCommonNoMerger H 2 p a b = commonPair p x y ∧
    actualPrivateCommonNoMerger H 3 p a b = p*x^3+(1-p)*y^3 := by
  rcases ha with ⟨ha0,_ha1,ha2,ha3,_ha4⟩
  rcases hb with ⟨hb0,_hb1,hb2,hb3,_hb4⟩
  simp [original_common_enumeration,ha0,ha2,ha3,hb0,hb2,hb3,commonPair]

/-- The common finite-bit program and the inherited independent live-root
program are evaluated on exactly the same physical parent/arm tuple. -/
theorem same_original_tuple_gain_strict
    (H : GProgram.G2.OriginalHybridParents N) (p x y : ℝ)
    (a b : Nat → ℝ) (ha : FourRootArmLaw a x) (hb : FourRootArmLaw b y)
    (hp : 0 < p) (hp1 : p < 1) (hx : 0 < x) (hx1 : x < 1)
    (hy : 0 < y) (hy1 : y < 1) :
    actualPrivateNoMerger H 3 p a b <
      (3/2 : ℝ) * actualPrivateCommonNoMerger H 2 p a b *
        actualPrivateNoMerger H 2 p a b := by
  rw [(original_common_cap3_coordinates H p x y a b ha hb).1]
  exact actual_original_private_gain_strict H p x y a b ha hb hp hp1 hx hx1 hy hy1

#print axioms original_common_enumeration
#print axioms original_common_cap3_coordinates
#print axioms same_original_tuple_gain_strict

end GProgram.G3.OriginalCommonCap3Routing
