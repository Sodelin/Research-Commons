import NanuqActualCurveCycle

/-! Edge-occurrence walks and their actual curves. Simplicity is a condition
on original vertices; curve simplicity is a derived conclusion. -/
namespace Nanuq.Source.EdgeGraph
open Set
variable {V E P : Type*} [TopologicalSpace P] (G : EdgeGraph V E)

inductive OccurrenceWalk : V → V → Type _
  | nil (v : V) : OccurrenceWalk v v
  | forward {a b : V} (w : OccurrenceWalk a b) (e : E) (h : G.source e = b) :
      OccurrenceWalk a (G.target e)
  | backward {a b : V} (w : OccurrenceWalk a b) (e : E) (h : G.target e = b) :
      OccurrenceWalk a (G.source e)

namespace OccurrenceWalk
variable {G}

def vertices : {a b : V} → G.OccurrenceWalk a b → Set V
  | _, _, .nil v => {v}
  | _, _, .forward w e _ => insert (G.target e) w.vertices
  | _, _, .backward w e _ => insert (G.source e) w.vertices

def edges : {a b : V} → G.OccurrenceWalk a b → Set E
  | _, _, .nil _ => ∅
  | _, _, .forward w e _ => insert e w.edges
  | _, _, .backward w e _ => insert e w.edges

def Simple : {a b : V} → G.OccurrenceWalk a b → Prop
  | _, _, .nil _ => True
  | _, _, .forward w e _ => w.Simple ∧ G.target e ∉ w.vertices
  | _, _, .backward w e _ => w.Simple ∧ G.source e ∉ w.vertices

def Nonempty : {a b : V} → G.OccurrenceWalk a b → Prop
  | _, _, .nil _ => False
  | _, _, .forward _ _ _ => True
  | _, _, .backward _ _ _ => True

theorem source_mem {a b : V} (w : G.OccurrenceWalk a b) : a ∈ w.vertices := by
  induction w with
  | nil => simp [vertices]
  | forward w e h ih => simp only [vertices];exact Set.mem_insert_of_mem _ ih
  | backward w e h ih => simp only [vertices];exact Set.mem_insert_of_mem _ ih

theorem target_mem {a b : V} (w : G.OccurrenceWalk a b) : b ∈ w.vertices := by
  cases w <;> simp [vertices]

theorem edge_endpoints_mem {a b : V} (w : G.OccurrenceWalk a b)
    {e : E} (he : e ∈ w.edges) : G.source e ∈ w.vertices ∧ G.target e ∈ w.vertices := by
  induction w with
  | nil => simpa [edges] using he
  | forward w f hf ih =>
    simp only [edges,vertices] at he ⊢
    rcases he with rfl | he
    · exact ⟨Set.mem_insert_of_mem _ (by rw [hf];exact w.target_mem),Set.mem_insert _ _⟩
    · exact ⟨Set.mem_insert_of_mem _ (ih he).1,Set.mem_insert_of_mem _ (ih he).2⟩
  | backward w f hf ih =>
    simp only [edges,vertices] at he ⊢
    rcases he with rfl | he
    · exact ⟨Set.mem_insert _ _,Set.mem_insert_of_mem _ (by rw [hf];exact w.target_mem)⟩
    · exact ⟨Set.mem_insert_of_mem _ (ih he).1,Set.mem_insert_of_mem _ (ih he).2⟩

variable (D : CurveDrawing (P := P) G)
noncomputable def curve : {a b : V} → G.OccurrenceWalk a b → Path (D.point a) (D.point b)
  | _, _, .nil v => Path.refl (D.point v)
  | _, _, .forward (.nil _) e h => (D.arc e).cast (congrArg D.point h.symm) rfl
  | _, _, .backward (.nil _) e h => (D.arc e).symm.cast (congrArg D.point h.symm) rfl
  | _, _, .forward w@(.forward _ _ _) e h => (curve w).trans ((D.arc e).cast (congrArg D.point h.symm) rfl)
  | _, _, .forward w@(.backward _ _ _) e h => (curve w).trans ((D.arc e).cast (congrArg D.point h.symm) rfl)
  | _, _, .backward w@(.forward _ _ _) e h => (curve w).trans ((D.arc e).symm.cast (congrArg D.point h.symm) rfl)
  | _, _, .backward w@(.backward _ _ _) e h => (curve w).trans ((D.arc e).symm.cast (congrArg D.point h.symm) rfl)

theorem curve_range {a b : V} (w : G.OccurrenceWalk a b) :
    Set.range (w.curve D) = {D.point a} ∪ ⋃ e ∈ w.edges, Set.range (D.arc e) := by
  induction w with
  | nil => simp [curve,edges]
  | forward w e h ih =>
    cases w with
    | nil =>
      cases h
      simp only [curve,Path.cast_coe,edges,Set.mem_empty_iff_false,Set.iUnion_of_empty]
      ext p
      simp only [Set.mem_union,Set.mem_singleton_iff,Set.mem_iUnion,Set.mem_insert_iff,Set.mem_empty_iff_false,or_false]
      constructor
      · intro hp;exact Or.inr ⟨e,rfl,hp⟩
      · rintro (rfl | ⟨f,rfl,hp⟩)
        · exact ⟨0,by simp⟩
        · exact hp
    | forward w f hf =>
      simp only [curve,Path.trans_range,Path.cast_coe,ih,edges] at *
      ext p;simp only [Set.mem_union,Set.mem_singleton_iff,Set.mem_iUnion,Set.mem_insert_iff]
      aesop
    | backward w f hf =>
      simp only [curve,Path.trans_range,Path.cast_coe,Path.symm_range,ih,edges] at *
      ext p;simp only [Set.mem_union,Set.mem_singleton_iff,Set.mem_iUnion,Set.mem_insert_iff]
      aesop
  | backward w e h ih =>
    cases w with
    | nil =>
      cases h
      simp only [curve,Path.cast_coe,Path.symm_range,edges,Set.mem_empty_iff_false,Set.iUnion_of_empty]
      ext p
      simp only [Set.mem_union,Set.mem_singleton_iff,Set.mem_iUnion,Set.mem_insert_iff,Set.mem_empty_iff_false,or_false]
      constructor
      · intro hp;exact Or.inr ⟨e,rfl,hp⟩
      · rintro (rfl | ⟨f,rfl,hp⟩)
        · exact ⟨1,by simp⟩
        · exact hp
    | forward w f hf =>
      simp only [curve,Path.trans_range,Path.cast_coe,Path.symm_range,ih,edges] at *
      ext p;simp only [Set.mem_union,Set.mem_singleton_iff,Set.mem_iUnion,Set.mem_insert_iff]
      aesop
    | backward w f hf =>
      simp only [curve,Path.trans_range,Path.cast_coe,Path.symm_range,ih,edges] at *
      ext p;simp only [Set.mem_union,Set.mem_singleton_iff,Set.mem_iUnion,Set.mem_insert_iff]
      aesop

theorem vertex_of_curve {a b : V} (w : G.OccurrenceWalk a b)
    (v : V) (t : unitInterval) (h : w.curve D t = D.point v) : v ∈ w.vertices := by
  have hp : D.point v ∈ Set.range (w.curve D) := ⟨t,h⟩
  rw [w.curve_range D] at hp
  rcases hp with he | hp
  · have he : D.point v = D.point a := he
    exact D.point_injective he ▸ w.source_mem
  · obtain ⟨e,hp⟩ := Set.mem_iUnion.mp hp
    obtain ⟨he,u,hu⟩ := Set.mem_iUnion.mp hp
    rcases D.vertex_incidence e v u hu with hv | hv
    · exact hv ▸ (w.edge_endpoints_mem he).1
    · exact hv ▸ (w.edge_endpoints_mem he).2
theorem curve_arc_boundary {a b : V} (w : G.OccurrenceWalk a b)
    (e : E) (he : e ∉ w.edges) (t u : unitInterval)
    (h : w.curve D t = D.arc e u) : u = 0 ∨ u = 1 := by
  have hp : D.arc e u ∈ Set.range (w.curve D) := ⟨t,h⟩
  rw [w.curve_range D] at hp
  rcases hp with hp | hp
  · exact D.arc_eq_vertex_parameter e a u hp
  · obtain ⟨f,hp⟩ := Set.mem_iUnion.mp hp
    obtain ⟨hf,v,hv⟩ := Set.mem_iUnion.mp hp
    have hn : f ≠ e := by intro hfe;subst f;exact he hf
    exact (D.edge_incidence f e hn v u hv).2

theorem fresh_path_joint {a b c : V} (w : G.OccurrenceWalk a b)
    (hw : Function.Injective (w.curve D)) (q : Path (D.point b) (D.point c))
    (hc : c ∉ w.vertices)
    (hb : ∀ t u, w.curve D t = q u → u = 0 ∨ u = 1)
    (t u : unitInterval) (h : w.curve D t = q u) : t = 1 ∧ u = 0 := by
  rcases hb t u h with hu | hu
  · refine ⟨hw ?_,hu⟩
    simpa [hu] using h
  · have hp : w.curve D t = D.point c := by simpa [hu] using h
    exact False.elim (hc (w.vertex_of_curve D c t hp))

theorem curve_injective {a b : V} (w : G.OccurrenceWalk a b)
    (hs : w.Simple) (hn : w.Nonempty) : Function.Injective (w.curve D) := by
  induction w with
  | nil => simpa [Nonempty] using hn
  | forward w e h ih =>
    simp only [Simple] at hs
    have hsimple : w.Simple := hs.1
    have hfresh : G.target e ∉ w.vertices := hs.2
    have hnot : e ∉ w.edges := fun he => hfresh (w.edge_endpoints_mem he).2
    cases w with
    | nil => simpa only [curve,Path.cast_coe] using D.arc_injective e
    | forward w f hf =>
      rw [curve]
      apply CurveDrawing.trans_injective_of_only_joint _ _ (ih hsimple trivial) (D.arc_injective e)
      apply fresh_path_joint D _ (ih hsimple trivial) _ hfresh
      intro t u hu
      exact curve_arc_boundary D _ e hnot t u hu
    | backward w f hf =>
      rw [curve]
      apply CurveDrawing.trans_injective_of_only_joint _ _ (ih hsimple trivial) (D.arc_injective e)
      apply fresh_path_joint D _ (ih hsimple trivial) _ hfresh
      intro t u hu
      exact curve_arc_boundary D _ e hnot t u hu
  | backward w e h ih =>
    simp only [Simple] at hs
    have hsimple : w.Simple := hs.1
    have hfresh : G.source e ∉ w.vertices := hs.2
    have hnot : e ∉ w.edges := fun he => hfresh (w.edge_endpoints_mem he).1
    have hi : Function.Injective (D.arc e).symm := by
      intro t u he
      exact unitInterval.symm_inj.mp (D.arc_injective e he)
    cases w with
    | nil => simpa only [curve,Path.cast_coe] using hi
    | forward w f hf =>
      rw [curve]
      apply CurveDrawing.trans_injective_of_only_joint _ _ (ih hsimple trivial) hi
      apply fresh_path_joint D _ (ih hsimple trivial) _ hfresh
      intro t u hu
      have hp := curve_arc_boundary D _ e hnot t (unitInterval.symm u) hu
      simpa only [unitInterval.symm_eq_zero,unitInterval.symm_eq_one,or_comm] using hp
    | backward w f hf =>
      rw [curve]
      apply CurveDrawing.trans_injective_of_only_joint _ _ (ih hsimple trivial) hi
      apply fresh_path_joint D _ (ih hsimple trivial) _ hfresh
      intro t u hu
      have hp := curve_arc_boundary D _ e hnot t (unitInterval.symm u) hu
      simpa only [unitInterval.symm_eq_zero,unitInterval.symm_eq_one,or_comm] using hp

end OccurrenceWalk
end Nanuq.Source.EdgeGraph
