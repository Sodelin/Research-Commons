import G5SelectedDiscreteSurvival
import G5FrozenTriplePolynomialKernel

/-!
# Five genealogy partitions read from the actual source ancestry

Contributor: dot, 2026-10-09. Verification is recorded by the packet's exact-byte build and owned-declaration audit receipt.
The finite partition code reads the existing actual ancestor map. Pair and
triple discreteness are genealogy-only selected-view events, with explicit
identities connecting them to this code. No population is observed.
-/
namespace GProgram.G5.TriplePartitionReadout
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceForestIntrinsicGenerator
open GProgram.G5.SelectedDiscreteSurvival
open scoped Classical NNReal ENNReal BigOperators
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma actual_genealogy_leaf_member (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (keep : Finset Copy)
    (x y : Copy) (hx : x ∈ keep) (hy : y ∈ keep) :
    y ∈ Genealogy.optionLeaves ((selectedView (state s) keep).genealogy x) ↔
      (state s).ancestor y = (state s).ancestor x := by
  have hv : Valid (state s) := s.property.forest
  rw [selected_view_block_leaves (state s) keep hx,
    selectedBlock_eq_fiber (state s) hv keep
      (hv.ancestor_live x) y]
  simp only [hy, true_and]

theorem actual_discrete_view_iff_injOn (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (keep : Finset Copy) :
    DiscreteView keep (selectedView (state s) keep) ↔
      Set.InjOn (state s).ancestor (keep : Set Copy) := by
  constructor
  · intro h x hx y hy he
    exact h x hx y hy ((actual_genealogy_leaf_member N s keep x y hx hy).mpr he.symm)
  · intro h x hx y hy hm
    exact (h hy hx ((actual_genealogy_leaf_member N s keep x y hx hy).mp hm)).symm

theorem actual_pair_discrete_view (N : RootedBinary V E X)
    {sample : Copy → X} (s : Code N sample) (i j : Copy) (hij : i ≠ j) :
    DiscreteView {i,j} (selectedView (state s) {i,j}) ↔
      (state s).ancestor i ≠ (state s).ancestor j := by
  rw [actual_discrete_view_iff_injOn]
  constructor
  · intro h he
    exact hij (h (by simp) (by simp) he)
  · intro h x hx y hy he
    have hx' : x = i ∨ x = j := by simpa using hx
    have hy' : y = i ∨ y = j := by simpa using hy
    rcases hx' with rfl | rfl <;> rcases hy' with rfl | rfl
    · rfl
    · exact False.elim (h he)
    · exact False.elim (h he.symm)
    · rfl

/-- 0=0|1|2, 1=01|2, 2=02|1, 3=12|0, 4=012. -/
noncomputable def ancestorPartition {A : Type*} [DecidableEq A] (a : Fin 3 → A) : Fin 5 :=
  if a 0 = a 1 then (if a 0 = a 2 then 4 else 1)
  else if a 0 = a 2 then 2 else if a 1 = a 2 then 3 else 0

noncomputable def actualTriplePartition (N : RootedBinary V E X)
    {sample : Fin 3 → X} (s : Code N sample) : Fin 5 :=
  ancestorPartition (state s).ancestor

theorem ancestor_partition_zero (a : Fin 3 → Fin 3) :
    ancestorPartition a = 0 ↔ Function.Injective a := by
  have hi : Function.Injective a ↔ a 0 ≠ a 1 ∧ a 0 ≠ a 2 ∧ a 1 ≠ a 2 := by
    constructor
    · intro h
      exact ⟨fun he => (by decide : (0 : Fin 3) ≠ 1) (h he),
        fun he => (by decide : (0 : Fin 3) ≠ 2) (h he),
        fun he => (by decide : (1 : Fin 3) ≠ 2) (h he)⟩
    · rintro ⟨h01,h02,h12⟩ x y he
      fin_cases x <;> fin_cases y <;> simp_all
  rw [hi]
  unfold ancestorPartition
  split_ifs <;> simp_all [eq_comm]

/-- Every actual triple ancestry, regardless of hidden populations, obeys
the exact event table. The impossible nontransitive equality cases vanish. -/
theorem ancestor_partition_pair01 (a : Fin 3 → Fin 3) :
    a 0 ≠ a 1 ↔ ancestorPartition a = 0 ∨
      ancestorPartition a = 2 ∨ ancestorPartition a = 3 := by
  unfold ancestorPartition
  split_ifs <;> simp_all [eq_comm]

theorem ancestor_partition_pair02 (a : Fin 3 → Fin 3) :
    a 0 ≠ a 2 ↔ ancestorPartition a = 0 ∨
      ancestorPartition a = 1 ∨ ancestorPartition a = 3 := by
  unfold ancestorPartition
  split_ifs <;> simp_all [eq_comm]

theorem ancestor_partition_pair12 (a : Fin 3 → Fin 3) :
    a 1 ≠ a 2 ↔ ancestorPartition a = 0 ∨
      ancestorPartition a = 1 ∨ ancestorPartition a = 2 := by
  unfold ancestorPartition
  split_ifs <;> simp_all [eq_comm]

#print axioms actual_genealogy_leaf_member
#print axioms actual_discrete_view_iff_injOn
#print axioms actual_pair_discrete_view
#print axioms ancestor_partition_zero
#print axioms ancestor_partition_pair01
#print axioms ancestor_partition_pair02
#print axioms ancestor_partition_pair12
end GProgram.G5.TriplePartitionReadout

