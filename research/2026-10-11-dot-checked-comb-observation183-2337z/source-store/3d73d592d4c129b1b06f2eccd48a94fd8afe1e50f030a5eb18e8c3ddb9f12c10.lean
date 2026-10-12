import G5BridgeComponentEntries
import G5NonbridgeRouteBound
import Mathlib.Tactic

/-!
# Actual original root routes cover component calendar intervals

Contributor: dot, 2026-10-02. The route suffix inside an actual bridge-deleted
component is derived from original rooted acyclic graph paths. It is not a
provided nonbridge-route oracle. Strict original edge clocks then supply the
unique active population on every entry/port interval. Source coin laws and
observation-driven safe chronology remain separate.
-/
namespace GProgram.G5.ComponentCalendar
open Nanuq.Source
open GProgram.G5
open GProgram.G5.NonbridgeRoutes
variable {V E : Type*}

theorem EdgePath.source_reachable_of_mem {G : EdgeGraph V E}
    {a b : V} {es : List E} (p : GProgram.G5.EdgePath G a b es)
    {e : E} (he : e ∈ es) : G.DReach a (G.source e) := by
  induction p with
  | nil => simp at he
  | @cons a b f fs hs rest ih =>
    rcases List.mem_cons.mp he with h | h
    · subst e
      rw [hs]
      exact .refl
    · exact (Relation.ReflTransGen.single ⟨f,hs,rfl⟩).trans (ih h)

theorem EdgePath.all_nonbridge_of_sameBlob {G : EdgeGraph V E} (root : V)
    (ha : G.Acyclic) (hr : ∀ v, G.DReach root v)
    {a b : V} {es : List E} (p : GProgram.G5.EdgePath G a b es)
    (hab : G.SameBlob a b) : ∀ e ∈ es, ¬G.IsBridge e := by
  intro e he heb
  have htb := p.target_reaches_end_of_mem he
  have havoid := GProgram.G5.ComponentEntries.sameBlob_avoids_bridge G heb hab
  have hbt : G.ReachWithout e (G.target e) b :=
    (GProgram.G5.Minimal.bridge_component_iff_descendant G root ha hr heb b).mpr htb
  have hta : G.DReach (G.target e) a :=
    (GProgram.G5.Minimal.bridge_component_iff_descendant G root ha hr heb a).mp
      (hbt.trans (G.ureach_symm havoid))
  have hts := hta.trans (EdgePath.source_reachable_of_mem p he)
  exact ha (G.target e) (Relation.TransGen.tail' hts ⟨e,rfl,rfl⟩)

theorem EdgePath.split_at_original_edge {G : EdgeGraph V E}
    {a b : V} {es : List E} (p : GProgram.G5.EdgePath G a b es)
    {e : E} (he : e ∈ es) :
    ∃ pre post, es = pre ++ e :: post ∧
      GProgram.G5.EdgePath G a (G.source e) pre ∧
      GProgram.G5.EdgePath G (G.target e) b post := by
  induction p with
  | nil => simp at he
  | @cons a b f fs hs rest ih =>
    rcases List.mem_cons.mp he with h | h
    · subst e
      refine ⟨[],fs,rfl,?_,rest⟩
      rw [hs]
      exact .nil a
    · rcases ih h with ⟨pre,post,heq,hpre,hpost⟩
      exact ⟨f::pre,post,by simp [heq],.cons hs hpre,hpost⟩

theorem root_route_component_decomposition (G : EdgeGraph V E) (root : V)
    (ha : G.Acyclic) (hr : ∀ v, G.DReach root v)
    {port : V} {es : List E} (p : GProgram.G5.EdgePath G root port es) :
    (G.SameBlob root port ∧ ∀ e ∈ es, ¬G.IsBridge e) ∨
    ∃ entry pre post, es = pre ++ entry :: post ∧ G.IsBridge entry ∧
      G.SameBlob (G.target entry) port ∧
      GProgram.G5.EdgePath G root (G.source entry) pre ∧
      GProgram.G5.EdgePath G (G.target entry) port post ∧
      (∀ e ∈ post, ¬G.IsBridge e) := by
  rcases GProgram.G5.ComponentEntries.EdgePath.sameBlob_or_incoming_bridge p with
    hs | ⟨entry,hemem,hbridge,hblob⟩
  · exact Or.inl ⟨hs,EdgePath.all_nonbridge_of_sameBlob root ha hr p hs⟩
  · rcases EdgePath.split_at_original_edge p hemem with ⟨pre,post,heq,hpre,hpost⟩
    exact Or.inr ⟨entry,pre,post,heq,hbridge,hblob,hpre,hpost,
      EdgePath.all_nonbridge_of_sameBlob root ha hr hpost hblob⟩

theorem EdgePath.active_exists {G : EdgeGraph V E} (C : Calendar G)
    {a b : V} {es : List E} (p : GProgram.G5.EdgePath G a b es)
    {t : ℝ} (hl : C.age b ≤ t) (hu : t < C.age a) :
    ∃ e ∈ es, C.Active t e := by
  induction p with
  | nil a => exact False.elim (not_lt_of_ge hl hu)
  | @cons a b e es hs rest ih =>
    by_cases he : C.age (G.target e) ≤ t
    · exact ⟨e,List.mem_cons_self,he,by simpa [hs] using hu⟩
    · rcases ih hl (lt_of_not_ge he) with ⟨f,hmem,hactive⟩
      exact ⟨f,List.mem_cons_of_mem e hmem,hactive⟩

theorem EdgePath.unique_active_exists {G : EdgeGraph V E} (C : Calendar G)
    {a b : V} {es : List E} (p : GProgram.G5.EdgePath G a b es)
    {t : ℝ} (hl : C.age b ≤ t) (hu : t < C.age a) :
    ∃! e, e ∈ es ∧ C.Active t e := by
  obtain ⟨e,he,ha⟩ := EdgePath.active_exists C p hl hu
  exact ⟨e,⟨he,ha⟩,fun f hf => p.active_unique C hf.1 he hf.2 ha⟩

#print axioms EdgePath.all_nonbridge_of_sameBlob
#print axioms root_route_component_decomposition
#print axioms EdgePath.unique_active_exists
end GProgram.G5.ComponentCalendar
