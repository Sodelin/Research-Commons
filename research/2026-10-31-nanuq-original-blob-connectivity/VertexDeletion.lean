import CutCrossing
namespace Nanuq.RawBlock
open Nanuq.Source
variable {V E : Type*} (G : EdgeGraph V E)
def Avoid (v : V) (e : E) : Prop := G.source e ≠ v ∧ G.target e ≠ v
def Component (v a z : V) : Prop := z ≠ v ∧ G.UReach (Avoid G v) a z

theorem component_edge_iff {v a : V} {e : E} (he : Avoid G v e) :
    Component G v a (G.source e) ↔ Component G v a (G.target e) := by
  constructor
  · intro h
    exact ⟨he.2, h.2.trans (G.ureach_single ⟨e,he,G.inc_source_target e⟩)⟩
  · intro h
    exact ⟨he.1, h.2.trans (G.ureach_symm (G.ureach_single ⟨e,he,G.inc_source_target e⟩))⟩

theorem crossing_incident {v a : V} {e : E} (he : Crosses G (Component G v a) e) :
    G.source e = v ∨ G.target e = v := by
  by_contra h
  push_neg at h
  exact he (component_edge_iff G h)

theorem crossing_disjoint {v a b : V}
    (hab : ¬ G.UReach (Avoid G v) a b) {e : E}
    (ha : Crosses G (Component G v a) e) :
    ¬ Crosses G (Component G v b) e := by
  intro hb
  have hn : ¬ Component G v a v := fun h => h.1 rfl
  have hm : ¬ Component G v b v := fun h => h.1 rfl
  have both (z : V) (hz : Component G v a z) (hw : Component G v b z) : False :=
    hab (hz.2.trans (G.ureach_symm hw.2))
  rcases crossing_incident G ha with hs | ht
  · have h₁ : Component G v a (G.target e) := by
      by_contra h
      exact ha ⟨fun hh => False.elim (hn (hs ▸ hh)),fun hh => False.elim (h hh)⟩
    have h₂ : Component G v b (G.target e) := by
      by_contra h
      exact hb ⟨fun hh => False.elim (hm (hs ▸ hh)),fun hh => False.elim (h hh)⟩
    exact both _ h₁ h₂
  · have h₁ : Component G v a (G.source e) := by
      by_contra h
      exact ha ⟨fun hh => False.elim (h hh),fun hh => False.elim (hn (ht ▸ hh))⟩
    have h₂ : Component G v b (G.source e) := by
      by_contra h
      exact hb ⟨fun hh => False.elim (h hh),fun hh => False.elim (hm (ht ▸ hh))⟩
    exact both _ h₁ h₂

theorem two_crossings (hc : ∀ a b, G.UReach (fun _ => True) a b)
    (hnb : ∀ e, ¬ G.IsBridge e) {v a : V} (ha : a ≠ v) :
    ∃ e f, e ≠ f ∧ Crosses G (Component G v a) e ∧ Crosses G (Component G v a) f := by
  obtain ⟨e,_,he⟩ := exists_crossing G (hc a v)
    (show Component G v a a from ⟨ha,.refl⟩)
    (show ¬ Component G v a v from fun h => h.1 rfl)
  obtain ⟨f,hfe,hf⟩ := second_crossing G hnb he
  exact ⟨e,f,Ne.symm hfe,he,hf⟩

/-- Counts distinct original edge identities, including parallel edges. -/
theorem delete_vertex_connected [Fintype E]
    (hc : ∀ a b, G.UReach (fun _ => True) a b)
    (hnb : ∀ e, ¬ G.IsBridge e)
    (hd : ∀ v, Set.ncard {e | G.source e = v ∨ G.target e = v} ≤ 3)
    {v a b : V} (ha : a ≠ v) (hb : b ≠ v) :
    G.UReach (Avoid G v) a b := by
  classical
  by_contra hab
  obtain ⟨e,f,hef,he,hf⟩ := two_crossings G hc hnb ha
  obtain ⟨g,k,hgk,hg,hk⟩ := two_crossings G hc hnb hb
  have heg : e ≠ g := fun h => crossing_disjoint G hab he (h ▸ hg)
  have hek : e ≠ k := fun h => crossing_disjoint G hab he (h ▸ hk)
  have hfg : f ≠ g := fun h => crossing_disjoint G hab hf (h ▸ hg)
  have hfk : f ≠ k := fun h => crossing_disjoint G hab hf (h ▸ hk)
  have hsub : ({e,f,g,k} : Set E) ⊆ {e | G.source e = v ∨ G.target e = v} := by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl | rfl
    · exact crossing_incident G he
    · exact crossing_incident G hf
    · exact crossing_incident G hg
    · exact crossing_incident G hk
  have hn := Set.ncard_le_ncard hsub
  have hfour : ({e,f,g,k} : Set E).ncard = 4 := by
    simp [Set.ncard_insert_of_notMem, hef, heg, hek, hfg, hfk, hgk]
  have := hd v
  omega
#print axioms delete_vertex_connected
end Nanuq.RawBlock
