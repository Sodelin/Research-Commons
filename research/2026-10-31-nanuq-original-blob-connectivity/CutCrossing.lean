import SourceNetwork
import Mathlib.Tactic
set_option debug.skipKernelTC false
namespace Nanuq.RawBlock
open Nanuq.Source
variable {V E : Type*} (G : EdgeGraph V E)

def Crosses (S : V → Prop) (e : E) : Prop := ¬ (S (G.source e) ↔ S (G.target e))

theorem reach_side_iff {S : V → Prop} {keep : E → Prop} {a b : V}
    (h : G.UReach keep a b)
    (hedge : ∀ e, keep e → (S (G.source e) ↔ S (G.target e))) : S a ↔ S b := by
  induction h with
  | refl => rfl
  | tail _ hs ih =>
    obtain ⟨e,he,hinc⟩ := hs
    rcases hinc with ⟨h₁,h₂⟩ | ⟨h₁,h₂⟩
    · exact ih.trans (h₁ ▸ h₂ ▸ hedge e he)
    · exact ih.trans (h₁ ▸ h₂ ▸ (hedge e he).symm)

theorem exists_crossing {S : V → Prop} {keep : E → Prop} {a b : V}
    (h : G.UReach keep a b) (ha : S a) (hb : ¬ S b) :
    ∃ e, keep e ∧ Crosses G S e := by
  classical
  by_contra hn
  push_neg at hn
  have hh : S a ↔ S b := reach_side_iff G h (fun e he => by
    have hh := hn e he
    simpa only [Crosses, not_not] using hh)
  exact hb (hh.mp ha)

/-- Any cut crossed by an edge has a second ORIGINAL crossing edge if none is a bridge. -/
theorem second_crossing (hnb : ∀ e, ¬ G.IsBridge e) {S : V → Prop} {e : E}
    (he : Crosses G S e) : ∃ f, f ≠ e ∧ Crosses G S f := by
  classical
  have hd : G.ReachWithout e (G.source e) (G.target e) := by
    simpa only [EdgeGraph.IsBridge, not_not] using hnb e
  by_cases hs : S (G.source e)
  · have ht : ¬ S (G.target e) := fun ht => he ⟨fun _ => ht,fun _ => hs⟩
    exact exists_crossing G hd hs ht
  · have ht : S (G.target e) := by
      by_contra ht
      exact he ⟨fun h => False.elim (hs h),fun h => False.elim (ht h)⟩
    exact exists_crossing G (G.ureach_symm hd) ht hs

#print axioms reach_side_iff
#print axioms second_crossing
end Nanuq.RawBlock
