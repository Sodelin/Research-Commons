import G7OriginalAdmission
import G7OriginalSurvivalCoverage
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# The literal nine-vertex pendant-bigon fixture

Author: dot / OpenAI, 2026-10-14.
SOURCE-ONLY TRANSCRIPTION DRAFT. No elaboration, kernel, or axiom audit has run.

The incidence data, original occurrence order, dates and equal-arm survival
coordinates are those of the reviewed 2026-10-13 physical singleton fixture.
The finite admission proof avoids evaluating the universe of all codes and
does not evaluate finite reachability by saturation. Finite `decide` calls
below concern only local degrees, arrays, registry and single-edge facts.

This file does not construct an outer-plane embedding, prove fixed-bank
selector compatibility of the displayed paths, or prove an observation row.
Those receiver obligations retain their separate status.
-/

namespace DotG3.PhysicalFixture

noncomputable section

open Nanuq.Source GProgram.G5
open GProgram.G7.OriginalFiniteEncoding GProgram.G7.OriginalAdmission
open GProgram.G7.OriginalSurvivalCoverage
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture

def fixtureCode : Code (Fin 4) (Fin 1) :=
  ⟨![0, 0, 1, 3, 3, 4, 1, 2, 2],
   ![1, 2, 3, 4, 4, 5, 6, 7, 8],
   0, ![5, 6, 7, 8], (fun _ => 4), (fun _ b => if b then 4 else 3)⟩

abbrev fixtureGraph : EdgeGraph (Fin 9) (Fin 9) := codeGraph fixtureCode

def fixtureRank : Fin 9 → ℕ := ![4, 3, 1, 2, 1, 0, 0, 0, 0]

lemma fixture_edge_rank (e : Fin 9) :
    fixtureRank (fixtureGraph.target e) < fixtureRank (fixtureGraph.source e) := by
  revert e
  decide

private lemma step_rank {a b : Fin 9} (h : fixtureGraph.DStep a b) :
    fixtureRank b < fixtureRank a := by
  obtain ⟨e, rfl, rfl⟩ := h
  exact fixture_edge_rank e

private lemma path_rank {a b : Fin 9}
    (h : Relation.TransGen fixtureGraph.DStep a b) :
    fixtureRank b < fixtureRank a := by
  induction h with
  | single h => exact step_rank h
  | tail _ h ih => exact lt_trans (step_rank h) ih

lemma fixture_acyclic : fixtureGraph.Acyclic := by
  intro a h
  exact Nat.lt_irrefl (fixtureRank a) (path_rank h)

private lemma edge_reach (e : Fin 9) :
    fixtureGraph.DReach (fixtureGraph.source e) (fixtureGraph.target e) :=
  Relation.ReflTransGen.single ⟨e, rfl, rfl⟩

lemma fixture_rooted (v : Fin 9) : fixtureGraph.DReach 0 v := by
  fin_cases v
  · exact .refl
  · exact edge_reach 0
  · exact edge_reach 1
  · exact (edge_reach 0).trans (edge_reach 2)
  · exact ((edge_reach 0).trans (edge_reach 2)).trans (edge_reach 3)
  · exact (((edge_reach 0).trans (edge_reach 2)).trans (edge_reach 3)).trans
      (edge_reach 5)
  · exact (edge_reach 0).trans (edge_reach 6)
  · exact (edge_reach 1).trans (edge_reach 7)
  · exact (edge_reach 1).trans (edge_reach 8)

private lemma avoid_B (z : Fin 9) (h0 : (0 : Fin 9) ≠ z)
    (h1 : (1 : Fin 9) ≠ z) (h6 : (6 : Fin 9) ≠ z) :
    fixtureGraph.AvoidReach z 0 6 := by
  refine ⟨h0, h6, ?_⟩
  exact (Relation.ReflTransGen.single ⟨⟨0, rfl, rfl⟩, h0, h1⟩).trans
    (Relation.ReflTransGen.single ⟨⟨6, rfl, rfl⟩, h1, h6⟩)

private lemma avoid_C (z : Fin 9) (h0 : (0 : Fin 9) ≠ z)
    (h2 : (2 : Fin 9) ≠ z) (h7 : (7 : Fin 9) ≠ z) :
    fixtureGraph.AvoidReach z 0 7 := by
  refine ⟨h0, h7, ?_⟩
  exact (Relation.ReflTransGen.single ⟨⟨1, rfl, rfl⟩, h0, h2⟩).trans
    (Relation.ReflTransGen.single ⟨⟨7, rfl, rfl⟩, h2, h7⟩)

lemma fixture_least_stable (v : Fin 9)
    (h : ∀ x : Fin 4, fixtureGraph.Dominates 0 v (codeLeaf fixtureCode x)) : v = 0 := by
  fin_cases v
  · rfl
  · exact False.elim (h 2 (avoid_C 1 (by decide) (by decide) (by decide)))
  · exact False.elim (h 1 (avoid_B 2 (by decide) (by decide) (by decide)))
  · exact False.elim (h 1 (avoid_B 3 (by decide) (by decide) (by decide)))
  · exact False.elim (h 1 (avoid_B 4 (by decide) (by decide) (by decide)))
  · exact False.elim (h 1 (avoid_B 5 (by decide) (by decide) (by decide)))
  · exact False.elim (h 2 (avoid_C 6 (by decide) (by decide) (by decide)))
  · exact False.elim (h 1 (avoid_B 7 (by decide) (by decide) (by decide)))
  · exact False.elim (h 1 (avoid_B 8 (by decide) (by decide) (by decide)))

lemma fixture_binary_valid : BinaryValid fixtureCode := by
  refine ⟨?_, ?_, ?_, ?_, ?_, fixture_acyclic, fixture_rooted, fixture_least_stable⟩
  · decide
  · decide
  · decide
  · decide
  · decide

lemma fixture_registry_valid : RegistryValid fixtureCode := by decide

private lemma retained_edge_isolates_five (e : Fin 9) (he : e ≠ 5) :
    fixtureGraph.source e = 5 ↔ fixtureGraph.target e = 5 := by
  revert he e
  decide

private lemma retained_step_isolates_five {a b : Fin 9}
    (h : fixtureGraph.UStep (fun e => e ≠ 5) a b) : a = 5 ↔ b = 5 := by
  obtain ⟨e, he, hinc⟩ := h
  rcases hinc with ⟨hs, ht⟩ | ⟨hs, ht⟩
  · rw [← hs, ← ht]
    exact retained_edge_isolates_five e he
  · rw [← ht, ← hs]
    exact (retained_edge_isolates_five e he).symm

private lemma retained_path_isolates_five {a b : Fin 9}
    (h : fixtureGraph.UReach (fun e => e ≠ 5) a b) : a = 5 ↔ b = 5 := by
  induction h with
  | refl => exact Iff.rfl
  | tail _ h ih => exact ih.trans (retained_step_isolates_five h)

lemma fixture_child_bridge : fixtureGraph.IsBridge 5 := by
  intro h
  have h45 : (4 : Fin 9) = 5 := (retained_path_isolates_five h).mpr rfl
  exact (by decide : (4 : Fin 9) ≠ 5) h45

lemma fixture_cut_child : CutChild fixtureCode := by
  intro e he
  have h : ∀ f : Fin 9, fixtureGraph.IsHybrid (fixtureGraph.source f) → f = 5 := by
    decide
  obtain rfl := h e he
  exact fixture_child_bridge

def fixtureN : RootedBinary (Fin 9) (Fin 9) (Fin 4) :=
  sourceOfValid fixtureCode fixture_binary_valid

noncomputable def fixtureIDs : Fin 1 ≃ Hybrid fixtureN :=
  decodedIDs fixtureCode fixture_binary_valid fixture_registry_valid

noncomputable def fixtureH : OriginalParentRegistry fixtureN :=
  decodedRegistry fixtureCode fixture_binary_valid fixture_registry_valid

lemma fixture_hybrid_unique (h : Hybrid fixtureN) : h = fixtureIDs 0 := by
  calc
    h = fixtureIDs (fixtureIDs.symm h) := (fixtureIDs.apply_symm_apply h).symm
    _ = fixtureIDs 0 := congrArg fixtureIDs (Subsingleton.elim _ _)

lemma fixture_parent_exact (b : Bool) :
    (fixtureH.parents (fixtureIDs 0)).parent b = (if b then 4 else 3) :=
  decoded_parent_exact fixtureCode fixture_binary_valid fixture_registry_valid 0 b

def fixtureC : Calendar fixtureN.graph where
  age v := fixtureRank v
  edge_older e := by exact_mod_cast fixture_edge_rank e

def fixtureEdgeSurvival : Fin 9 → ℝ :=
  ![1/2, 1/2, 3/4, 8/9, 8/9, 3/4, 1/2, 1/2, 1/2]

lemma fixture_edge_survival_open : OpenCube fixtureEdgeSurvival := by
  intro e
  fin_cases e <;> norm_num [fixtureEdgeSurvival]

noncomputable def fixtureR : PositivePairRates (Fin 9) :=
  ratesFromSurvival fixtureN fixtureC fixtureEdgeSurvival fixture_edge_survival_open

lemma fixture_whole_edge_exposure (e : Fin 9) :
    exposure fixtureN fixtureC fixtureR e = -Real.log (fixtureEdgeSurvival e) :=
  ratesFromSurvival_exposure fixtureN fixtureC fixtureEdgeSurvival
    fixture_edge_survival_open e

lemma fixture_whole_edge_survival :
    survival fixtureN fixtureC fixtureR = fixtureEdgeSurvival :=
  ratesFromSurvival_survival fixtureN fixtureC fixtureEdgeSurvival
    fixture_edge_survival_open

def fixtureP : HybridProbabilities fixtureN where
  gamma _ := 1/3
  positive _ := by norm_num
  below_one _ := by norm_num

/-- Candidate forward paths, still to be tied to each actual once-drawn bank. -/
lemma fixture_A_path_false : EdgePath fixtureN.graph fixtureN.root (fixtureN.leaf 0)
    [0, 2, 3, 5] :=
  .cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil _))))

lemma fixture_A_path_true : EdgePath fixtureN.graph fixtureN.root (fixtureN.leaf 0)
    [0, 2, 4, 5] :=
  .cons rfl (.cons rfl (.cons rfl (.cons rfl (.nil _))))

lemma fixture_B_path : EdgePath fixtureN.graph fixtureN.root (fixtureN.leaf 1)
    [0, 6] := .cons rfl (.cons rfl (.nil _))

lemma fixture_C_path : EdgePath fixtureN.graph fixtureN.root (fixtureN.leaf 2)
    [1, 7] := .cons rfl (.cons rfl (.nil _))

lemma fixture_D_path : EdgePath fixtureN.graph fixtureN.root (fixtureN.leaf 3)
    [1, 8] := .cons rfl (.cons rfl (.nil _))

#print axioms fixture_binary_valid
#print axioms fixture_registry_valid
#print axioms fixture_cut_child
#print axioms fixture_whole_edge_survival

end

end DotG3.PhysicalFixture
