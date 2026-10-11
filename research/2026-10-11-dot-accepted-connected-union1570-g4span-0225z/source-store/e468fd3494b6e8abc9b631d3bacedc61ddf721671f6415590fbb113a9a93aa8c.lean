import G4TwoRootSourceStopping
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Actual finite ordinary triplet compiler for the G4 A-clade readout.

The three equally weighted unordered first pairs are enumerated as Fin 3.
The resulting rooted genealogy is constructed, and the A-only cherry event is
evaluated on that constructed tree. Thus the coefficient 1/3 is calculated by
the finite compiler rather than introduced as an independent readout field.
Ordinary pair survivals in (0,1) also receive a positive exponential-duration
witness, and concatenated durations yield multiplied survivals.

Remaining source-to-observation obligation: this finite triplet compiler has
not yet been connected to a formally admitted four-taxon network and the
C,D-deletion/projectivity theorem. It does not prove the full Kingman waiting
time distribution from a continuous probability-measure definition.
-/

namespace G4OrdinaryTripletReadout

inductive Leaf where
  | a1
  | a2
  | b
  deriving DecidableEq

inductive RootedGeneTree where
  | leaf (label : Leaf)
  | node (left right : RootedGeneTree)
  deriving DecidableEq

open Leaf RootedGeneTree

def aaTree : RootedGeneTree := node (node (leaf a1) (leaf a2)) (leaf b)

def topologyFromFirstPair (pair : Fin 3) : RootedGeneTree :=
  if pair.val = 0 then aaTree
  else if pair.val = 1 then node (node (leaf a1) (leaf b)) (leaf a2)
  else node (node (leaf a2) (leaf b)) (leaf a1)

def isAACherry (left right : RootedGeneTree) : Bool :=
  decide ((left = leaf a1 ∧ right = leaf a2) ∨
    (left = leaf a2 ∧ right = leaf a1))

def hasAAClade : RootedGeneTree → Bool
  | leaf _ => false
  | node left right =>
      isAACherry left right || hasAAClade left || hasAAClade right

def cladeIndicator (tree : RootedGeneTree) : ℚ :=
  if hasAAClade tree then 1 else 0

def firstPairWeight (_ : Fin 3) : ℚ := 1 / 3

def ordinaryTripletCladeProbability : ℚ :=
  ∑ pair : Fin 3, firstPairWeight pair * cladeIndicator (topologyFromFirstPair pair)

theorem first_pair_weights_positive (pair : Fin 3) : 0 < firstPairWeight pair := by
  norm_num [firstPairWeight]

theorem first_pair_weights_normalized : (∑ pair : Fin 3, firstPairWeight pair) = 1 := by
  norm_num [firstPairWeight]

theorem premerged_A_clade : cladeIndicator aaTree = 1 := by
  decide

theorem first_pair_event_table :
    (cladeIndicator (topologyFromFirstPair (0 : Fin 3)) = 1) ∧
      (cladeIndicator (topologyFromFirstPair (1 : Fin 3)) = 0) ∧
      (cladeIndicator (topologyFromFirstPair (2 : Fin 3)) = 0) := by
  decide

theorem ordinaryTripletCladeProbability_eq :
    ordinaryTripletCladeProbability = (1 / 3 : ℚ) := by
  unfold ordinaryTripletCladeProbability
  rw [Fin.sum_univ_three]
  rw [first_pair_event_table.1, first_pair_event_table.2.1, first_pair_event_table.2.2]
  norm_num [firstPairWeight]

noncomputable def compiledCladeProbability (r : ℝ) : ℝ :=
  (1 - r) * (cladeIndicator aaTree : ℝ) +
    r * (ordinaryTripletCladeProbability : ℝ)

theorem compiledCladeProbability_eq (r : ℝ) :
    compiledCladeProbability r = 1 - (2 / 3 : ℝ) * r := by
  rw [compiledCladeProbability, premerged_A_clade, ordinaryTripletCladeProbability_eq]
  norm_num
  <;> ring

theorem actual_triplet_compiler_is_core_readout
    (before after : G4TwoRootSourceStopping.PositiveEdge) (p : ℝ) :
    compiledCladeProbability (before.survival * after.survival * p) =
      G4TwoRootSourceStopping.rootedACladeResponse before after p := by
  rw [compiledCladeProbability_eq, G4TwoRootSourceStopping.rootedACladeResponse_eq]
  ring

theorem actual_triplet_readout_injective
    (before after : G4TwoRootSourceStopping.PositiveEdge) :
    Function.Injective (fun p : ℝ =>
      compiledCladeProbability (before.survival * after.survival * p)) := by
  intro p q h
  dsimp only at h
  rw [actual_triplet_compiler_is_core_readout,
    actual_triplet_compiler_is_core_readout] at h
  exact G4TwoRootSourceStopping.rootedACladeResponse_injective before after h

noncomputable def canonicalDuration (q : ℝ) : ℝ := -Real.log q

theorem canonicalDuration_positive {q : ℝ} (hq : 0 < q) (hq1 : q < 1) :
    0 < canonicalDuration q := by
  exact neg_pos.mpr (Real.log_neg hq hq1)

theorem canonicalDuration_survival {q : ℝ} (hq : 0 < q) :
    Real.exp (-canonicalDuration q) = q := by
  simp [canonicalDuration, Real.exp_log hq]

theorem positive_survival_iff_positive_exponential_duration (q : ℝ) :
    (0 < q ∧ q < 1) ↔ ∃ t : ℝ, 0 < t ∧ q = Real.exp (-t) := by
  constructor
  · rintro ⟨hq, hq1⟩
    exact ⟨canonicalDuration q, canonicalDuration_positive hq hq1,
      (canonicalDuration_survival hq).symm⟩
  · rintro ⟨t, ht, rfl⟩
    refine ⟨Real.exp_pos _, ?_⟩
    have hneg : -t < 0 := neg_neg_of_pos ht
    simpa using Real.exp_lt_exp.mpr hneg

theorem positive_edge_has_clock (E : G4TwoRootSourceStopping.PositiveEdge) :
    ∃ t : ℝ, 0 < t ∧ E.survival = Real.exp (-t) :=
  (positive_survival_iff_positive_exponential_duration E.survival).mp
    ⟨E.positive, E.below_one⟩

theorem concatenated_duration_survival {q r : ℝ} (hq : 0 < q) (hr : 0 < r) :
    Real.exp (-(canonicalDuration q + canonicalDuration r)) = q * r := by
  rw [neg_add, Real.exp_add, canonicalDuration_survival hq, canonicalDuration_survival hr]

end G4OrdinaryTripletReadout

#print axioms G4OrdinaryTripletReadout.ordinaryTripletCladeProbability_eq
#print axioms G4OrdinaryTripletReadout.actual_triplet_readout_injective
#print axioms G4OrdinaryTripletReadout.positive_edge_has_clock
