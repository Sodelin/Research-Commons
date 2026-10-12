import G2CompleteTimedSupport
import G2TimedDecorationPruning

/-!
Chronological validity under literal leaf deletion and unary suppression.
Contributor: dot (OpenAI), 6 October 2026.
-/
namespace GProgram.G2.ChronologicalPruning
set_option backward.isDefEq.respectTransparency false
open GProgram.SourceForest
open GProgram.G2.FaithfulPairAgeDecoration GProgram.G2.TimedDecorationPruning
open GProgram.G2.ChronologicalDecoration
open scoped Classical
variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]

theorem prune_chronological (leafAge : Copy → ℝ) (keep : Finset Copy)
    (t : Genealogy Copy) (d : Decoration t) (hc : Chronological leafAge t d)
    (u : Decorated (Copy := Copy)) (hu : prune keep t d = some u) :
    Chronological leafAge u.1 u.2 ∧ rootAge leafAge u.1 u.2 ≤ rootAge leafAge t d := by
  induction t generalizing u with
  | leaf x =>
      by_cases hx : x ∈ keep
      · simp only [prune,if_pos hx,Option.some.injEq] at hu
        subst u
        exact ⟨True.intro,le_rfl⟩
      · simp [prune,hx] at hu
  | graft a b iha ihb =>
      cases ha : prune keep a d.2.1 with
      | none =>
          cases hb : prune keep b d.2.2 with
          | none => simp [prune,ha,hb,join] at hu
          | some ub =>
              simp only [prune,ha,hb,join,Option.some.injEq] at hu
              subst u
              obtain ⟨hcb,hrb⟩ := ihb d.2.2 hc.2.1 ub hb
              exact ⟨hcb,hrb.trans hc.2.2.2.le⟩
      | some ua =>
          obtain ⟨hca,hra⟩ := iha d.2.1 hc.1 ua ha
          cases hb : prune keep b d.2.2 with
          | none =>
              simp only [prune,ha,hb,join,Option.some.injEq] at hu
              subst u
              exact ⟨hca,hra.trans hc.2.2.1.le⟩
          | some ub =>
              simp only [prune,ha,hb,join,Option.some.injEq] at hu
              subst u
              obtain ⟨hcb,hrb⟩ := ihb d.2.2 hc.2.1 ub hb
              exact ⟨⟨hca,hcb,hra.trans_lt hc.2.2.1,hrb.trans_lt hc.2.2.2⟩,le_rfl⟩

lemma pair_age_self (leafAge : Copy → ℝ) (t : Genealogy Copy) (d : Decoration t)
    (x : Copy) (hx : x ∈ t.leaves) : pairAge leafAge t d x x = leafAge x := by
  induction t with
  | leaf y =>
      have hxy := Finset.mem_singleton.mp hx
      subst x
      rfl
  | graft a b iha ihb =>
      by_cases ha : x ∈ a.leaves
      · rw [pairAge,if_pos ⟨ha,ha⟩]
        exact iha d.2.1 ha
      · have hb : x ∈ b.leaves := (Finset.mem_union.mp hx).resolve_left ha
        rw [pairAge,if_neg (fun h => ha h.1),if_pos ⟨hb,hb⟩]
        exact ihb d.2.2 hb

#print axioms prune_chronological
#print axioms pair_age_self
end GProgram.G2.ChronologicalPruning
