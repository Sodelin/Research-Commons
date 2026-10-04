import G1SharpCoreCombAdmission

/-! Literal cut-child admission: every actual hybrid child edge is a bridge.
The right child cut is derived by an explicit ORIGINAL vertex-side partition. -/
namespace G1SharpCoreCombCutChild
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source G1SharpCoreCombDefinition G1SharpCoreCombDegrees G1SharpCoreCombAdmission
open scoped Classical

lemma actual_bridge_from_cut {V E : Type*} (G : EdgeGraph V E) (e : E) (side : V → Prop)
    (hs : ¬side (G.source e)) (ht : side (G.target e))
    (hother : ∀ f, f ≠ e → (side (G.source f) ↔ side (G.target f))) : G.IsBridge e := by
  intro hwalk
  have hinv : ∀ a b, G.ReachWithout e a b → (side a ↔ side b) := by
    intro a b h
    induction h with
    | refl => rfl
    | tail _ hstep ih =>
      obtain ⟨f,hfe,hinc⟩ := hstep
      rcases hinc with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
      · exact ih.trans (hother f hfe)
      · exact ih.trans (hother f hfe).symm
  exact hs ((hinv _ _ hwalk).mpr ht)

def suffixSide (n : Nat) (i : Module n) : Vertex n → Prop
  | .inl (j,_) => i.val < j.val
  | .inr x => i.val < x.val

theorem original_right_port_bridge (n : Nat) (hn : 4 ≤ n) (i : Module n) :
    (network n hn).graph.IsBridge (i,7) := by
  apply actual_bridge_from_cut (graph n) (i,7) (suffixSide n i)
  · simp [graph,source,localSource,suffixSide]
  · dsimp only [graph,target]
    split_ifs <;> dsimp only [suffixSide]
    all_goals simp only [Fin.val_mk]
    all_goals have hi := i.isLt
    all_goals omega
  · intro f hne
    rcases f with ⟨j,l⟩
    have hi := i.isLt
    have hj := j.isLt
    fin_cases l
    all_goals dsimp only [graph,source,target,localSource,suffixSide]
    all_goals try rfl
    split_ifs <;> try dsimp only [suffixSide]
    all_goals
      have hjne : j.val ≠ i.val := by
        intro he
        apply hne
        simp only [Prod.mk.injEq,Fin.ext_iff]
        exact ⟨he,rfl⟩
      simp only [Fin.val_mk]
      omega

theorem original_left_port_bridge (n : Nat) (hn : 4 ≤ n) (i : Module n) :
    (network n hn).graph.IsBridge (i,6) :=
  (network n hn).leaf_incoming_bridge ⟨i.val,by have hi := i.isLt; omega⟩ rfl

theorem actual_cut_child (n : Nat) (hn : 4 ≤ n) : G1CutChildPorts.CutChild (network n hn) := by
  intro e hh
  rcases e with ⟨i,k⟩
  change (graph n).IsHybrid (.inl (i,localSource k)) at hh
  have hd := (original_module_hybrid n hn i (localSource k)).mp hh
  fin_cases k <;> simp only [localSource,Fin.ext_iff] at hd
  all_goals first | exact original_left_port_bridge n hn i | exact original_right_port_bridge n hn i | norm_num at hd

#print axioms actual_cut_child
end G1SharpCoreCombCutChild
