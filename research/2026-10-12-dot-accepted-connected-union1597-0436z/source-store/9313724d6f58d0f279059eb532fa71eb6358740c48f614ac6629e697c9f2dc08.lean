import G1SharpCoreCombRootedness

/-! Actual original LSA admission for the all-n source family. Every nonroot
vertex is bypassed by an explicit original path to a labelled original tip. -/
namespace G1SharpCoreCombLSA
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source G1SharpCoreCombDefinition G1SharpCoreCombDegrees G1SharpCoreCombRootedness
open scoped Classical

lemma avoid_step {n : Nat} (blocked start old next : Vertex n) (e : Edge n)
    (h : (graph n).AvoidReach blocked start old) (hs : (graph n).source e = old)
    (ht : (graph n).target e = next) (hne : next ≠ blocked) :
    (graph n).AvoidReach blocked start next :=
  ⟨h.1,hne,h.2.2.tail ⟨⟨e,hs,ht⟩,h.2.1,hne⟩⟩

lemma avoids_left_tip (n : Nat) (hn : 4 ≤ n) (blocked : Vertex n)
    (hr : root n hn ≠ blocked)
    (hh : (Sum.inl ((⟨0,by omega⟩ : Module n),(3:LocalVertex)) : Vertex n) ≠ blocked)
    (hl : (Sum.inr (⟨0,by omega⟩ : Fin n) : Vertex n) ≠ blocked) :
    (graph n).AvoidReach blocked (root n hn) (.inr ⟨0,by omega⟩) := by
  let i : Module n := ⟨0,by omega⟩
  have base : (graph n).AvoidReach blocked (root n hn) (root n hn) := ⟨hr,hr,.refl⟩
  have middle := avoid_step blocked _ _ (.inl (i,3)) (i,0) base rfl rfl hh
  exact avoid_step blocked _ _ (.inr ⟨0,by omega⟩) (i,6) middle rfl rfl hl

lemma avoids_right_lane (n : Nat) (hn : 4 ≤ n) (blocked : Vertex n)
    (hsafe : ∀ i : Module n, (.inl (i,0) : Vertex n) ≠ blocked ∧
      (.inl (i,1) : Vertex n) ≠ blocked ∧ (.inl (i,4) : Vertex n) ≠ blocked)
    (hlast : (Sum.inr (⟨n-1,by omega⟩ : Fin n) : Vertex n) ≠ blocked) :
    (graph n).AvoidReach blocked (root n hn) (.inr ⟨n-1,by omega⟩) := by
  have localPath (i : Module n) (h : (graph n).AvoidReach blocked (root n hn) (.inl (i,0))) :
      (graph n).AvoidReach blocked (root n hn) (.inl (i,4)) := by
    have hU := avoid_step blocked _ _ (.inl (i,1)) (i,1) h rfl rfl (hsafe i).2.1
    exact avoid_step blocked _ _ (.inl (i,4)) (i,2) hU rfl rfl (hsafe i).2.2
  have aux : ∀ m : Nat, ∀ h : m < n-1, (graph n).AvoidReach blocked (root n hn) (.inl (⟨m,h⟩,0)) := by
    intro m
    induction m with
    | zero => intro h; exact ⟨(hsafe ⟨0,h⟩).1,(hsafe ⟨0,h⟩).1,.refl⟩
    | succ m ih =>
      intro h
      have hprev : m < n-1 := by omega
      let prev : Module n := ⟨m,hprev⟩
      have hr := localPath prev (ih hprev)
      have hnext : prev.val+1 < n-1 := h
      have ht : (graph n).target (prev,7) = .inl (⟨m+1,h⟩,0) := by
        simp only [graph,target]
        rw [dif_pos hnext]
      exact avoid_step blocked _ _ (.inl (⟨m+1,h⟩,0)) (prev,7) hr rfl ht (hsafe ⟨m+1,h⟩).1
  let last : Module n := ⟨n-2,by omega⟩
  have hr := localPath last (aux last.val last.isLt)
  have hnext : ¬last.val+1 < n-1 := by dsimp [last]; omega
  have ht : (graph n).target (last,7) = .inr ⟨n-1,by omega⟩ := by
    simp only [graph,target]
    rw [dif_neg hnext]
  exact avoid_step blocked _ _ (.inr ⟨n-1,by omega⟩) (last,7) hr rfl ht hlast

theorem original_least_stable (n : Nat) (hn : 4 ≤ n) (blocked : Vertex n)
    (hdom : ∀ x : Fin n, (graph n).Dominates (root n hn) blocked (taxon n x)) : blocked = root n hn := by
  by_contra hroot
  have hr : root n hn ≠ blocked := Ne.symm hroot
  cases blocked with
  | inl pair =>
    rcases pair with ⟨i,k⟩
    by_cases hk : k = 3
    · subst k
      have ha := avoids_right_lane n hn (.inl (i,3)) (by intro j; simp) (by simp)
      exact hdom ⟨n-1,by omega⟩ ha
    · have hh : (Sum.inl ((⟨0,by omega⟩ : Module n),(3:LocalVertex)) : Vertex n) ≠ .inl (i,k) := by
        intro he
        exact hk (congrArg Prod.snd (Sum.inl.inj he)).symm
      have ha := avoids_left_tip n hn (.inl (i,k)) hr hh (by simp)
      exact hdom ⟨0,by omega⟩ ha
  | inr x =>
    by_cases hx : x.val = 0
    · have hlast : (Sum.inr (⟨n-1,by omega⟩ : Fin n) : Vertex n) ≠ .inr x := by
        intro he
        have he' := congrArg Fin.val (Sum.inr.inj he)
        dsimp only at he'
        rw [hx] at he'
        omega
      have ha := avoids_right_lane n hn (.inr x) (by intro j; simp) hlast
      exact hdom ⟨n-1,by omega⟩ ha
    · have hl : (Sum.inr (⟨0,by omega⟩ : Fin n) : Vertex n) ≠ .inr x := by
        intro he
        exact hx (congrArg Fin.val (Sum.inr.inj he)).symm
      have ha := avoids_left_tip n hn (.inr x) hr (by simp) hl
      exact hdom ⟨0,by omega⟩ ha

#print axioms original_least_stable
end G1SharpCoreCombLSA
