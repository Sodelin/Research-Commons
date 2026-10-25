import G6BridgeCannotEnterHybrid
import G5CalendarRoutes

/-!
# Actual bridge components have unique rootward entries

New proof contribution: dot's Lean source-bridge lane, 2026-10-02.
The original edge-indexed rooted acyclic graph itself implies that every
non-root bridge-deleted component has exactly one incoming bridge occurrence.
No finite size, binary degree, LSA, level, embedding or canonical component
representation is needed by the generic uniqueness proof. Together with the
cut-child nonbridge route bound this supplies genuine graph premises for the
current-component G5 argument; clocks, source probabilities and chronology are
still separate formal obligations.
-/

namespace GProgram.G5.ComponentEntries

open Nanuq.Source

variable {V E : Type*}

/-- A nonbridge-component path avoids EVERY specified bridge occurrence. -/
theorem sameBlob_avoids_bridge (G : EdgeGraph V E) {e : E}
    (he : G.IsBridge e) {a b : V} (hab : G.SameBlob a b) : G.ReachWithout e a b := by
  apply G.ureach_mono (keep := fun f => ¬ G.IsBridge f) _ hab
  intro f hf hfe
  subst f
  exact hf he

/-- Two different incoming bridges cannot enter the same actual component. -/
theorem bridge_targets_sameBlob_iff_eq (G : EdgeGraph V E) (root : V)
    (ha : G.Acyclic) (hr : ∀ v, G.DReach root v) {e f : E}
    (he : G.IsBridge e) (hf : G.IsBridge f) :
    G.SameBlob (G.target e) (G.target f) ↔ e = f := by
  constructor
  · intro hblob
    have hef := (GProgram.G5.Minimal.bridge_component_iff_descendant G root ha hr he
      (G.target f)).mp (sameBlob_avoids_bridge G he hblob)
    have hfe := (GProgram.G5.Minimal.bridge_component_iff_descendant G root ha hr hf
      (G.target e)).mp (sameBlob_avoids_bridge G hf (G.sameBlob_symm hblob))
    have ht := G.dreach_antisymm ha hef hfe
    exact (GProgram.G6.BridgeEntry.bridge_incoming_unique G root ha hr he ht.symm).symm
  · intro h
    subst f
    exact G.sameBlob_refl _

/-- The component of the original root has no incoming bridge. -/
theorem bridge_target_not_root_component (G : EdgeGraph V E) (root : V)
    (ha : G.Acyclic) (hr : ∀ v, G.DReach root v) {e : E}
    (he : G.IsBridge e) : ¬ G.SameBlob (G.target e) root := by
  intro hb
  exact G.bridge_sides_disjoint he
    (GProgram.G5.Minimal.root_source_side_of_rooted_acyclic G root ha hr e)
    (sameBlob_avoids_bridge G he hb)

/-- Any original directed route either stays in one component or has a final
incoming bridge followed only by original nonbridge component connectivity. -/
theorem EdgePath.sameBlob_or_incoming_bridge {G : EdgeGraph V E}
    {a b : V} {es : List E} (p : GProgram.G5.EdgePath G a b es) :
    G.SameBlob a b ∨ ∃ e ∈ es, G.IsBridge e ∧ G.SameBlob (G.target e) b := by
  induction p with
  | nil a => exact Or.inl (G.sameBlob_refl a)
  | @cons a b e es hs rest ih =>
    rcases ih with hsame | ⟨f, hmem, hf, hfb⟩
    · by_cases he : G.IsBridge e
      · exact Or.inr ⟨e, List.mem_cons_self, he, hsame⟩
      · apply Or.inl
        have het := G.nonbridge_sameBlob he
        rw [hs] at het
        exact het.trans hsame
    · exact Or.inr ⟨f, List.mem_cons_of_mem e hmem, hf, hfb⟩

/-- Rootedness supplies an actual incoming original bridge for every component
other than the root component, without assuming a bridge-tree decomposition. -/
theorem nonroot_component_has_incoming_bridge (G : EdgeGraph V E) (root : V)
    (hr : ∀ v, G.DReach root v) (v : V) (hv : ¬ G.SameBlob root v) :
    ∃ e, G.IsBridge e ∧ G.SameBlob (G.target e) v := by
  obtain ⟨es, hp⟩ := GProgram.G5.exists_edgePath_of_directed (hr v)
  rcases EdgePath.sameBlob_or_incoming_bridge hp with hs | ⟨e, _, he, hb⟩
  · exact False.elim (hv hs)
  · exact ⟨e, he, hb⟩

/-- Exact original bridge occurrence uniqueness for every non-root component. -/
theorem nonroot_component_unique_entry (G : EdgeGraph V E) (root : V)
    (ha : G.Acyclic) (hr : ∀ v, G.DReach root v) (v : V)
    (hv : ¬ G.SameBlob root v) :
    ∃! e, G.IsBridge e ∧ G.SameBlob (G.target e) v := by
  obtain ⟨e, he, hb⟩ := nonroot_component_has_incoming_bridge G root hr v hv
  refine ⟨e, ⟨he, hb⟩, ?_⟩
  intro f hf
  exact (bridge_targets_sameBlob_iff_eq G root ha hr hf.1 he).mp
    (hf.2.trans (G.sameBlob_symm hb))

#print axioms bridge_targets_sameBlob_iff_eq
#print axioms bridge_target_not_root_component
#print axioms nonroot_component_has_incoming_bridge
#print axioms nonroot_component_unique_entry

end GProgram.G5.ComponentEntries
