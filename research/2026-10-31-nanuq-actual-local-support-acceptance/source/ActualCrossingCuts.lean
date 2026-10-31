import SortedCrossingExclusion
import ActualCutClusters

/-! UNCOMPILED original-ID crossing-cut bridge. No reshaped syntax edge
is used as an original physical edge. The all-query equality is discharged
by the SAME qualified source receiver in the eventual actual wrapper. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualCutClusters
open Nanuq.Source Nanuq.Quartet Nanuq.GraphSyntax Nanuq.ActualFinite
open Nanuq.AdjacentCertificate
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- A resolution witnessed in one ACTUAL original switching belongs to the
original DISTINCT set, regardless of how many other choices repeat it. -/
theorem actual_resolution_mem (N : RootedBinary V E X) (S : N.Switching)
    (q : Fin 4 ↪ X) (r : Resolution)
    (hr : S.graph.Resolves (fun i => N.leaf (q i)) r) :
    r ∈ N.rawDisplayedQuartets q := by
  have he := (S.resolves_iff_eq_resolve q r).mp hr
  exact Finset.mem_image.mpr ⟨S,Finset.mem_univ _,he.symm⟩

/-- Conversely every member of the distinct set retains a literal original
switching and its physical cut-resolution witness. -/
theorem actual_resolution_mem_iff (N : RootedBinary V E X)
    (q : Fin 4 ↪ X) (r : Resolution) :
    r ∈ N.rawDisplayedQuartets q ↔
      ∃ S : N.Switching, S.graph.Resolves (fun i => N.leaf (q i)) r := by
  constructor
  · intro hr
    obtain ⟨S, _, he⟩ := Finset.mem_image.mp hr
    exact ⟨S,(S.resolves_iff_eq_resolve q r).mpr he.symm⟩
  · rintro ⟨S,hr⟩
    exact actual_resolution_mem N S q r hr

/-- Complete actual descendant-side tests supply the original edge witness.
Both orientations of the physical edge are accepted. -/
theorem actual_crossing_of_descendants (N : RootedBinary V E X)
    (S : N.Switching) (e : S.Edge) (q : Fin 4 ↪ X)
    (hc :
      (¬S.graph.DReach (S.graph.target e) (N.leaf (q 0)) ∧
       ¬S.graph.DReach (S.graph.target e) (N.leaf (q 2)) ∧
       S.graph.DReach (S.graph.target e) (N.leaf (q 1)) ∧
       S.graph.DReach (S.graph.target e) (N.leaf (q 3))) ∨
      (S.graph.DReach (S.graph.target e) (N.leaf (q 0)) ∧
       S.graph.DReach (S.graph.target e) (N.leaf (q 2)) ∧
       ¬S.graph.DReach (S.graph.target e) (N.leaf (q 1)) ∧
       ¬S.graph.DReach (S.graph.target e) (N.leaf (q 3)))) :
    Resolution.xz_yw ∈ N.rawDisplayedQuartets q := by
  apply actual_resolution_mem N S q Resolution.xz_yw
  have hsrc (i : Fin 4) := source_cut_iff S.graph S.selected_acyclic
    S.selected_uniqueIncoming N.root S.selected_rooted e (N.leaf (q i))
  have htgt (i : Fin 4) := target_cut_iff S.graph S.selected_acyclic
    S.selected_uniqueIncoming e (N.leaf (q i))
  refine ⟨e,S.graph.uniqueIncoming_all_bridges S.selected_uniqueIncoming S.selected_acyclic e,?_⟩
  rcases hc with hc | hc
  · exact Or.inl ⟨(hsrc 0).mpr hc.1,(hsrc 2).mpr hc.2.1,
      (htgt 1).mpr hc.2.2.1,(htgt 3).mpr hc.2.2.2⟩
  · exact Or.inr ⟨(hsrc 1).mpr hc.2.2.1,(hsrc 3).mpr hc.2.2.2,
      (htgt 0).mpr hc.1,(htgt 2).mpr hc.2.1⟩

end Nanuq.ActualCutClusters
