import G1SemidirectedMergedRootCutPaths

/-! The selected edge subtype and the literal original keep/delete predicate
have identical physical paths. This binds actual graph deletion to the
original switching tree already used by normalized topology readouts. -/
namespace G1SelectedOriginalDeletionPathEquivalence
open Nanuq.Source GProgram.G5 G1SemidirectedSelectedRetainedCutPaths
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

theorem actual_selected_without_iff_original (N : RootedBinary V E X) (S : N.Switching)
    (e : S.Edge) (v w : V) :
    S.graph.ReachWithout e v w ↔ N.graph.UReach (OriginalWithout N S e.val) v w := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hstep ih =>
      obtain ⟨f,hf,hinc⟩ := hstep
      exact ih.tail ⟨f.val,⟨f.property,fun he => hf (Subtype.ext he)⟩,hinc⟩
  · intro h
    induction h with
    | refl => exact .refl
    | tail _ hstep ih =>
      obtain ⟨f,hf,hinc⟩ := hstep
      exact ih.tail ⟨⟨f,hf.1⟩,fun he => hf.2 (congrArg Subtype.val he),hinc⟩

lemma actual_dreach_without_of_source_unreachable {W F : Type*} (G : EdgeGraph W F) (e : F)
    {a b : W} (h : G.DReach a b) (hn : ¬ G.DReach a (G.source e)) : G.ReachWithout e a b := by
  induction h with
  | refl => exact .refl
  | @tail b c hp hstep ih =>
    obtain ⟨f,hs,ht⟩ := hstep
    have hf : f ≠ e := by
      intro he
      subst f
      exact hn (hs ▸ hp)
    exact ih.tail ⟨f,hf,Or.inl ⟨hs,ht⟩⟩

#print axioms actual_selected_without_iff_original
end G1SelectedOriginalDeletionPathEquivalence
