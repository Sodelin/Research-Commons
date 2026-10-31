import CutCrossing
namespace Nanuq.RawBlock
open Nanuq.Source
variable {V E : Type*} (G : EdgeGraph V E)

/-- A walk retraction may delete steps, but never inserts a new edge ID. -/
theorem retract_walk {keep : E → Prop} {f : E} (r : V → V)
    (hr : ∀ e, keep e → r (G.source e) = r (G.target e) ∨
      (r (G.source e) = G.source e ∧ r (G.target e) = G.target e ∧ e ≠ f))
    {a b : V} (h : G.UReach keep a b) :
    G.UReach (fun e => keep e ∧ e ≠ f) (r a) (r b) := by
  induction h with
  | refl => exact .refl
  | @tail b c h hs ih =>
    obtain ⟨e,he,hi⟩ := hs
    rcases hi with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · rcases hr e he with heq | ⟨hs,ht,hef⟩
      · simpa only [heq] using ih
      · exact ih.tail ⟨e,⟨he,hef⟩,Or.inl ⟨hs.symm,ht.symm⟩⟩
    · rcases hr e he with heq | ⟨hs,ht,hef⟩
      · simpa only [heq] using ih
      · exact ih.tail ⟨e,⟨he,hef⟩,Or.inr ⟨hs.symm,ht.symm⟩⟩

/-- Retraction to one side of a single original cut edge. No new edge is used. -/
theorem trim_cut_side {S : V → Prop} {f : E} {v w : V}
    (hi : G.Inc f v w) (hv : S v) (hw : ¬ S w)
    (hside : ∀ e, e ≠ f → (S (G.source e) ↔ S (G.target e)))
    {keep : E → Prop} {a b : V} (ha : S a) (hb : S b)
    (h : G.UReach keep a b) : G.UReach (fun e => keep e ∧ e ≠ f) a b := by
  classical
  let r := fun z => if S z then z else v
  have hr : ∀ e, keep e → r (G.source e) = r (G.target e) ∨
      (r (G.source e) = G.source e ∧ r (G.target e) = G.target e ∧ e ≠ f) := by
    intro e _
    by_cases hef : e = f
    · subst e
      left
      rcases hi with ⟨hs,ht⟩ | ⟨hs,ht⟩ <;> simp [r,hs,ht,hv,hw]
    · by_cases hs : S (G.source e)
      · exact Or.inr ⟨by simp [r,hs],by simp [r,(hside e hef).mp hs],hef⟩
      · have ht : ¬ S (G.target e) := fun ht => hs ((hside e hef).mpr ht)
        exact Or.inl (by simp [r,hs,ht])
  have hh := retract_walk G r hr h
  simpa only [r,if_pos ha,if_pos hb] using hh

theorem bridge_side_iff {f e : E} (hef : e ≠ f) :
    G.ReachWithout f (G.source f) (G.source e) ↔
      G.ReachWithout f (G.source f) (G.target e) := by
  constructor
  · intro h
    exact h.tail ⟨e,hef,G.inc_source_target e⟩
  · intro h
    exact h.tail ⟨e,hef,G.inc_symm (G.inc_source_target e)⟩

/-- Remove an original bridge from any walk with same-blob endpoints. -/
theorem trim_original_bridge {f : E} (hf : G.IsBridge f)
    {a b : V} (hab : G.SameBlob a b) {keep : E → Prop}
    (h : G.UReach keep a b) : G.UReach (fun e => keep e ∧ e ≠ f) a b := by
  classical
  let S := fun z => G.ReachWithout f (G.source f) z
  have hs : S (G.source f) := .refl
  have ht : ¬ S (G.target f) := hf
  have hside : ∀ e, e ≠ f → (S (G.source e) ↔ S (G.target e)) :=
    fun e he => bridge_side_iff G he
  have habside : S a ↔ S b := reach_side_iff G hab (fun e he =>
    hside e (fun heq => he (heq ▸ hf)))
  by_cases ha : S a
  · exact trim_cut_side G (G.inc_source_target f) hs ht hside ha (habside.mp ha) h
  · have hb : ¬ S b := fun hb => ha (habside.mpr hb)
    exact trim_cut_side G (S := fun z => ¬ S z)
      (G.inc_symm (G.inc_source_target f)) ht (fun hn => hn hs)
      (fun e he => not_congr (hside e he)) ha hb h

/-- Finite removal never reintroduces any previously excluded edge ID. -/
theorem trim_bridge_set [DecidableEq E] (F : Finset E)
    (hF : ∀ f ∈ F, G.IsBridge f) {a b : V} (hab : G.SameBlob a b)
    {keep : E → Prop} (h : G.UReach keep a b) :
    G.UReach (fun e => keep e ∧ e ∉ F) a b := by
  induction F using Finset.induction_on with
  | empty =>
    exact G.ureach_mono (fun e he => ⟨he,by simp⟩) h
  | @insert f F hf ih =>
    have hprev := ih (fun e he => hF e (Finset.mem_insert_of_mem he))
    have hh := trim_original_bridge G (hF f (Finset.mem_insert_self _ _)) hab hprev
    exact G.ureach_mono (fun e he => ⟨he.1.1,by simp [he.1.2,he.2]⟩) hh

/-- Every original nonbridge detour can be kept inside the unswitched blob. -/
theorem internal_nonbridge_detour [Fintype E] {e : E} (he : ¬ G.IsBridge e) :
    G.UReach (fun f => ¬ G.IsBridge f ∧ f ≠ e) (G.source e) (G.target e) := by
  classical
  have h : G.ReachWithout e (G.source e) (G.target e) := by
    simpa only [EdgeGraph.IsBridge,not_not] using he
  have hh := trim_bridge_set G (Finset.univ.filter G.IsBridge)
    (fun f hf => (Finset.mem_filter.mp hf).2) (G.nonbridge_sameBlob he) h
  exact G.ureach_mono (fun f hf => ⟨by simpa using hf.2,hf.1⟩) hh

#print axioms trim_cut_side
#print axioms internal_nonbridge_detour
end Nanuq.RawBlock
