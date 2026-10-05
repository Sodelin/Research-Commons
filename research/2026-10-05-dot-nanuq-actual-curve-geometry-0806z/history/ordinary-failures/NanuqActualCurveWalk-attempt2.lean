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
  | nil => exact Set.mem_singleton _
  | forward w e h ih => exact Set.mem_insert_of_mem _ ih
  | backward w e h ih => exact Set.mem_insert_of_mem _ ih

theorem target_mem {a b : V} (w : G.OccurrenceWalk a b) : b ∈ w.vertices := by
  cases w
  · exact Set.mem_singleton _
  · exact Set.mem_insert _ _
  · exact Set.mem_insert _ _

theorem edge_endpoints_mem {a b : V} (w : G.OccurrenceWalk a b)
    {e : E} (he : e ∈ w.edges) : G.source e ∈ w.vertices ∧ G.target e ∈ w.vertices := by
  induction w with
  | nil => exact False.elim he
  | forward w f hf ih =>
    rcases he with rfl | he
    · exact ⟨Set.mem_insert_of_mem _ (by rw [hf];exact w.target_mem),Set.mem_insert _ _⟩
    · exact ⟨Set.mem_insert_of_mem _ (ih he).1,Set.mem_insert_of_mem _ (ih he).2⟩
  | backward w f hf ih =>
    rcases he with rfl | he
    · exact ⟨Set.mem_insert _ _,Set.mem_insert_of_mem _ (by rw [hf];exact w.target_mem)⟩
    · exact ⟨Set.mem_insert_of_mem _ (ih he).1,Set.mem_insert_of_mem _ (ih he).2⟩

variable (D : CurveDrawing (P := P) G)
noncomputable def curve : {a b : V} → G.OccurrenceWalk a b → Path (D.point a) (D.point b)
  | _, _, .nil v => Path.refl (D.point v)
  | _, _, .forward w e h => (w.curve D).trans ((D.arc e).cast (congrArg D.point h.symm) rfl)
  | _, _, .backward w e h => (w.curve D).trans ((D.arc e).symm.cast (congrArg D.point h.symm) rfl)

theorem curve_range {a b : V} (w : G.OccurrenceWalk a b) :
    Set.range (w.curve D) = {D.point a} ∪ ⋃ e ∈ w.edges, Set.range (D.arc e) := by
  induction w with
  | nil => simp [curve,edges]
  | forward w e h ih =>
    simp only [curve,Path.trans_range,Path.cast_coe,ih,edges]
    ext p;simp only [Set.mem_union,Set.mem_singleton_iff,Set.mem_iUnion,Set.mem_insert_iff]
    aesop
  | backward w e h ih =>
    simp only [curve,Path.trans_range,Path.cast_coe,Path.symm_range,ih,edges]
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
end OccurrenceWalk
end Nanuq.Source.EdgeGraph
