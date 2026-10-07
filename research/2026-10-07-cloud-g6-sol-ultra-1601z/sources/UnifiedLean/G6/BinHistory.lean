import G2SourceGraftDecoration
import G2ActualPairCoalescence

/-!
UNCHECKED root draft, 7 October 2026. No compiler receipt is implied.
Coarsening of the actual pair-age update and same-bin endpoint collapse.
The full calendar/read-cut/bin observation law is a separate source theorem.
-/
namespace UnifiedLean.G6.BinHistory
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open GProgram.G2.SourceGraftDecoration GProgram.G2.ActualPairCoalescence
open scoped Classical

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Finite tags use the SAME actual old/destination ancestry condition. -/
noncomputable def tagUpdate {Tag : Type*} (N : RootedBinary V E X) {sample : Copy → X}
    (s d : Code N sample) (tag : Tag) (M : Copy → Copy → Tag) (x y : Copy) : Tag :=
  if (state s).ancestor x ≠ (state s).ancestor y ∧
      (state d).ancestor x = (state d).ancestor y then tag else M x y

/-- Pointwise coarsening of the inherited actual age update, with no new law premise. -/
theorem map_coded_age_update {Tag : Type*} (N : RootedBinary V E X) {sample : Copy → X}
    (s d : Code N sample) (age : ℝ) (M : Copy → Copy → ℝ) (bin : ℝ → Tag) :
    (fun x y => bin (codedAgeUpdate N s d age M x y)) =
      tagUpdate N s d (bin age) (fun x y => bin (M x y)) := by
  funext x y
  by_cases h : (state s).ancestor x ≠ (state s).ancestor y ∧
      (state d).ancestor x = (state d).ancestor y
  · simp only [codedAgeUpdate, tagUpdate, if_pos h]
  · simp only [codedAgeUpdate, tagUpdate, if_neg h]

def RelationMonotone (N : RootedBinary V E X) {sample : Copy → X}
    (s d : Code N sample) : Prop :=
  ∀ x y, (state s).ancestor x = (state s).ancestor y →
    (state d).ancestor x = (state d).ancestor y

/-- Same-bin updates collapse to the initial/final endpoints if old pair relations persist. -/
theorem same_bin_update_comp {Tag : Type*} (N : RootedBinary V E X) {sample : Copy → X}
    (s d e : Code N sample) (tag : Tag) (M : Copy → Copy → Tag)
    (hsd : RelationMonotone N s d) (hde : RelationMonotone N d e) :
    tagUpdate N d e tag (tagUpdate N s d tag M) = tagUpdate N s e tag M := by
  funext x y
  have h01 := hsd x y
  have h12 := hde x y
  by_cases h0 : (state s).ancestor x = (state s).ancestor y <;>
    by_cases h1 : (state d).ancestor x = (state d).ancestor y <;>
    by_cases h2 : (state e).ancestor x = (state e).ancestor y <;>
    simp_all [tagUpdate]

theorem tag_update_self {Tag : Type*} (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (tag : Tag) (M : Copy → Copy → Tag) :
    tagUpdate N s s tag M = M := by
  funext x y
  simp [tagUpdate]

/-- Discharge monotonicity for the unchanged ACTUAL legal merger destination. -/
theorem actual_destination_relation_monotone (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) :
    RelationMonotone N s (stepDestination N s (some p)) := by
  intro x y hxy
  have hbefore : sameBlock (selectedView (state s) Finset.univ) x y :=
    (selected_same_block (state s) s.property.forest Finset.univ
      (Finset.mem_univ x) (Finset.mem_univ y)).mpr hxy
  have hafter : sameBlock
      (selectedView (state (stepDestination N s (some p))) Finset.univ) x y :=
    (actual_destination_pair_birth N s Finset.univ p
      (Finset.mem_univ x) (Finset.mem_univ y)).mpr (Or.inl hbefore)
  exact (selected_same_block (state (stepDestination N s (some p)))
    (stepDestination N s (some p)).property.forest Finset.univ
      (Finset.mem_univ x) (Finset.mem_univ y)).mp hafter

/-- Two actual mergers within the same bin retain old tags and assign that bin once. -/
theorem two_actual_mergers_same_bin {Tag : Type*} (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (p : Choice N s)
    (q : Choice N (stepDestination N s (some p)))
    (tag : Tag) (M : Copy → Copy → Tag) :
    tagUpdate N (stepDestination N s (some p))
        (stepDestination N (stepDestination N s (some p)) (some q)) tag
        (tagUpdate N s (stepDestination N s (some p)) tag M) =
      tagUpdate N s (stepDestination N (stepDestination N s (some p)) (some q)) tag M :=
  same_bin_update_comp N _ _ _ tag M
    (actual_destination_relation_monotone N s p)
    (actual_destination_relation_monotone N _ q)

#print axioms map_coded_age_update
#print axioms same_bin_update_comp
#print axioms tag_update_self
#print axioms actual_destination_relation_monotone
#print axioms two_actual_mergers_same_bin
end UnifiedLean.G6.BinHistory
