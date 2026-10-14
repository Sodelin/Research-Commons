import Astra.PhysicalSpliceRegistry
import G1ActualSelectedClusterTransport
import G4WeightedOrdinaryTreeLaw

/-!
# Actual taxon fibres through the original two-port splice

Source-only candidate, unselected and uncompiled. These finite structural
equalities use the original whole COMMON bank and its literal retained
registry. No equal-exposure condition, rate assignment, weighted-law equation
or bank-marginal identity is an assumption or conclusion of this module.
-/

namespace Astra.PhysicalSpliceClades

set_option backward.isDefEq.respectTransparency false

open Nanuq.Source GProgram.G5 GProgram.G5.Normalization
open G1ActualTwoPortBlob G1BigonFootprint G1BigonSpliceGraph
open G1SplicedSourceAdmission G1SplicedOriginalSwitching
open G1SwitchingDescendantTransport G1ActualSelectedClusterTransport
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativeCommonPairGerm
open GProgram.G5.AttainedChronology DotG4.WeightedOrdinaryTreeLaw
open Astra.PhysicalSpliceRegistry
open scoped Classical

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E] [DecidableEq X]

/-- An unselected original edge carries no original taxon route. -/
theorem edgeTaxa_empty_of_not_kept (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (coin : CommonSeed N) (e : E)
    (hk : ¬(commonSwitching N H coin).keep e) :
    edgeTaxa N C H coin e = ∅ := by
  ext x
  constructor
  · intro hx
    exact False.elim (hk (common_route_kept N C H coin x
      ((mem_edgeTaxa N C H coin e x).mp hx)))
  · intro hx
    exact False.elim (Finset.not_mem_empty x hx)

/-- Every retained edge occurrence has the same full original-taxon fibre,
including the case where its original bank does not select it. -/
theorem retained_edgeTaxa (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (hc : CutChild N) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (coin : CommonSeed N) (e : RetainedEdge N b A) :
    edgeTaxa (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
      (splicedRegistry N hc b hb A H) (restrictBank N hc b hb A coin) (.inl e) =
        edgeTaxa N C H coin e.val := by
  let N' := splicedNetwork N hc b hb A
  let C' := splicedCalendar N hc b hb A C
  let H' := splicedRegistry N hc b hb A H
  let coin' := restrictBank N hc b hb A coin
  change edgeTaxa N' C' H' coin' (.inl e) = edgeTaxa N C H coin e.val
  have hs : commonSwitching N' H' coin' =
      restrictSwitching N hc b hb A (commonSwitching N H coin) :=
    commonSwitching_restrict N hc b hb A H coin
  by_cases hk : (commonSwitching N H coin).keep e.val
  · have hk' : (commonSwitching N' H' coin').keep (.inl e) := by
      rw [hs]
      exact hk
    calc
      edgeTaxa N' C' H' coin' (.inl e) =
          sampledDescendants N' (commonSwitching N' H' coin') Finset.univ
            (retainedTarget N hc b A e) :=
        edgeTaxa_eq_sampledDescendants N' C' H' coin' ⟨.inl e, hk'⟩
      _ = sampledDescendants N (commonSwitching N H coin) Finset.univ
          (N.graph.target e.val) := by
        rw [hs]
        exact actual_retained_selected_cluster N hc b hb A
          (commonSwitching N H coin) Finset.univ (retainedTarget N hc b A e)
      _ = edgeTaxa N C H coin e.val :=
        (edgeTaxa_eq_sampledDescendants N C H coin ⟨e.val, hk⟩).symm
  · have hk' : ¬(commonSwitching N' H' coin').keep (.inl e) := by
      rw [hs]
      exact hk
    rw [edgeTaxa_empty_of_not_kept N' C' H' coin' (.inl e) hk',
      edgeTaxa_empty_of_not_kept N C H coin e.val hk]

/-- The actual new ordinary edge carries precisely the old child-edge fibre. -/
theorem new_edgeTaxa (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (hc : CutChild N) (b : N.graph.Blob)
    (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (coin : CommonSeed N) :
    edgeTaxa (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
      (splicedRegistry N hc b hb A H) (restrictBank N hc b hb A coin) (.inr ()) =
        edgeTaxa N C H coin A.child := by
  let N' := splicedNetwork N hc b hb A
  let C' := splicedCalendar N hc b hb A C
  let H' := splicedRegistry N hc b hb A H
  let coin' := restrictBank N hc b hb A coin
  change edgeTaxa N' C' H' coin' (.inr ()) = edgeTaxa N C H coin A.child
  have hs : commonSwitching N' H' coin' =
      restrictSwitching N hc b hb A (commonSwitching N H coin) :=
    commonSwitching_restrict N hc b hb A H coin
  have hk' : (commonSwitching N' H' coin').keep (.inr ()) := by
    rw [hs]
    trivial
  have hk : (commonSwitching N H coin).keep A.child :=
    child_kept N b A (commonSwitching N H coin)
  calc
    edgeTaxa N' C' H' coin' (.inr ()) =
        sampledDescendants N' (commonSwitching N' H' coin') Finset.univ
          (descendantInterface N b A) :=
      edgeTaxa_eq_sampledDescendants N' C' H' coin' ⟨.inr (), hk'⟩
    _ = sampledDescendants N (commonSwitching N H coin) Finset.univ
        (N.graph.target A.child) := by
      rw [hs]
      exact actual_retained_selected_cluster N hc b hb A
        (commonSwitching N H coin) Finset.univ (descendantInterface N b A)
    _ = edgeTaxa N C H coin A.child :=
      (edgeTaxa_eq_sampledDescendants N C H coin ⟨A.child, hk⟩).symm

/-- The entry's selected upper descendants are exactly the child descendants. -/
theorem entry_edgeTaxa_eq_child (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (hc : CutChild N) (b : N.graph.Blob)
    (A : ActualBlobBigon N b) (coin : CommonSeed N) :
    edgeTaxa N C H coin A.entry = edgeTaxa N C H coin A.child := by
  have he : (commonSwitching N H coin).keep A.entry :=
    entry_kept N hc b A (commonSwitching N H coin)
  have hd : (commonSwitching N H coin).keep A.child :=
    child_kept N b A (commonSwitching N H coin)
  rw [edgeTaxa_eq_sampledDescendants N C H coin ⟨A.entry, he⟩,
    edgeTaxa_eq_sampledDescendants N C H coin ⟨A.child, hd⟩, A.entry_target]
  ext x
  simp only [sampledDescendants, Finset.mem_filter, Finset.mem_univ, true_and]
  exact actual_selected_upper_descendants N hc b A (commonSwitching N H coin) x

/-- Either actual arm, when selected by the whole original bank, has exactly
the child fibre. The arm order here is A's literal fragment order. -/
theorem kept_parent_edgeTaxa_eq_child (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (b : N.graph.Blob) (A : ActualBlobBigon N b)
    (coin : CommonSeed N) (bit : Bool)
    (hk : (commonSwitching N H coin).keep (A.fragment.parents.parent bit)) :
    edgeTaxa N C H coin (A.fragment.parents.parent bit) =
      edgeTaxa N C H coin A.child := by
  have hd : (commonSwitching N H coin).keep A.child :=
    child_kept N b A (commonSwitching N H coin)
  have ht : N.graph.target (A.fragment.parents.parent bit) =
      A.fragment.parents.hybrid := by
    cases bit
    · exact A.fragment.parents.target0
    · exact A.fragment.parents.target1
  rw [edgeTaxa_eq_sampledDescendants N C H coin ⟨A.fragment.parents.parent bit, hk⟩,
    edgeTaxa_eq_sampledDescendants N C H coin ⟨A.child, hd⟩, ht]
  ext x
  simp only [sampledDescendants, Finset.mem_filter, Finset.mem_univ, true_and]
  exact actual_selected_hybrid_descendants N b A (commonSwitching N H coin) x

#check edgeTaxa_empty_of_not_kept
#check retained_edgeTaxa
#check new_edgeTaxa
#check entry_edgeTaxa_eq_child
#check kept_parent_edgeTaxa_eq_child
#print axioms edgeTaxa_empty_of_not_kept
#print axioms retained_edgeTaxa
#print axioms new_edgeTaxa
#print axioms entry_edgeTaxa_eq_child
#print axioms kept_parent_edgeTaxa_eq_child

end Astra.PhysicalSpliceClades
