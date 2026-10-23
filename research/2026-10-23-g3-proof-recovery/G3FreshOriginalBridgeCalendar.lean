import G5CalendarRoutes
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! G3 source-owned fresh ONE-bigon raw graph/calendar adapter, 2026-10-21.
Uncompiled candidate. This constructs an actual EdgeGraph and strict Calendar;
it does not assume a new RootedBinary, source law or compiler reflection.
RootedBinary degree/rooted/least-stable packaging, registry transport, admission
and the protected menu/OriginalSpan receiver remain explicit subsequent work.

The old unexposed slot keeps its ID as the lower connector. All other original
edge endpoints and all original vertex ages are literal inl transports. The
three fresh edge occurrences and two fresh vertices are disjoint sum tags.
Native parent1 may be bound to upper arm 2, with gamma=1-p_parent0.
-/

namespace GProgram.G3.FreshOriginalBridgeCalendar
open Nanuq.Source GProgram.G5

variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

abbrev FreshVertex (V : Type*) := V ⊕ Bool
abbrev FreshEdge (E : Type*) := E ⊕ Fin 3

def hybrid : FreshVertex V := .inr false
def upper : FreshVertex V := .inr true
def lowerEdge (e : E) : FreshEdge E := .inl e
def upperEdge : FreshEdge E := .inr 0
def arm0 : FreshEdge E := .inr 1
def arm1 : FreshEdge E := .inr 2

def insertedGraph (G : EdgeGraph V E) (slot : E) :
    EdgeGraph (FreshVertex V) (FreshEdge E) where
  source
    | .inl e => if e = slot then hybrid else .inl (G.source e)
    | .inr j => if j = 0 then .inl (G.source slot) else upper
  target
    | .inl e => .inl (G.target e)
    | .inr j => if j = 0 then upper else hybrid

def insertedAge {G : EdgeGraph V E} (C : Calendar G) (slot : E) :
    FreshVertex V → ℝ
  | .inl v => C.age v
  | .inr b => if b then (C.age (G.target slot) + 2*C.age (G.source slot))/3
      else (2*C.age (G.target slot) + C.age (G.source slot))/3

def newDuration {G : EdgeGraph V E} (C : Calendar G) (slot : E) : ℝ :=
  (C.age (G.source slot)-C.age (G.target slot))/3

theorem newDuration_pos {G : EdgeGraph V E} (C : Calendar G) (slot : E) :
    0 < newDuration C slot := by
  have h := C.edge_older slot
  dsimp [newDuration]
  linarith

theorem inserted_edge_older {G : EdgeGraph V E} (C : Calendar G) (slot : E)
    (e : FreshEdge E) :
    insertedAge C slot ((insertedGraph G slot).target e) <
      insertedAge C slot ((insertedGraph G slot).source e) := by
  have h := C.edge_older slot
  cases e with
  | inl e =>
    by_cases he : e = slot
    · subst e
      simp only [insertedGraph,if_pos rfl,insertedAge,hybrid,Bool.false_eq_true,
        if_false]
      linarith
    · simpa only [insertedGraph,if_neg he,insertedAge] using C.edge_older e
  | inr j =>
    by_cases hj : j = 0
    · simp only [insertedGraph,if_pos hj,insertedAge,upper,if_true]
      linarith
    · simp only [insertedGraph,if_neg hj,insertedAge,hybrid,upper,
        Bool.false_eq_true,if_false,if_true]
      linarith

def insertedCalendar {G : EdgeGraph V E} (C : Calendar G) (slot : E) :
    Calendar (insertedGraph G slot) where
  age := insertedAge C slot
  edge_older := inserted_edge_older C slot

@[simp] theorem old_age {G : EdgeGraph V E} (C : Calendar G) (slot : E) (v : V) :
    (insertedCalendar C slot).age (.inl v) = C.age v := rfl

theorem outside_source (G : EdgeGraph V E) (slot e : E) (he : e ≠ slot) :
    (insertedGraph G slot).source (.inl e) = .inl (G.source e) := by
  simp [insertedGraph,he]

@[simp] theorem old_target (G : EdgeGraph V E) (slot e : E) :
    (insertedGraph G slot).target (.inl e) = .inl (G.target e) := rfl

theorem literal_new_endpoints (G : EdgeGraph V E) (slot : E) :
    (insertedGraph G slot).source (lowerEdge slot) = hybrid ∧
    (insertedGraph G slot).target (lowerEdge slot) = .inl (G.target slot) ∧
    (insertedGraph G slot).source upperEdge = .inl (G.source slot) ∧
    (insertedGraph G slot).target upperEdge = upper ∧
    (insertedGraph G slot).source arm0 = upper ∧
    (insertedGraph G slot).target arm0 = hybrid ∧
    (insertedGraph G slot).source arm1 = upper ∧
    (insertedGraph G slot).target arm1 = hybrid := by
  norm_num [insertedGraph,lowerEdge,upperEdge,arm0,arm1]

theorem arm_ids_distinct : (arm0 : FreshEdge E) ≠ arm1 := by
  norm_num [arm0,arm1]

theorem new_edge_duration {G : EdgeGraph V E} (C : Calendar G) (slot : E)
    (e : FreshEdge E) (he : e = lowerEdge slot ∨ ∃ j : Fin 3, e = .inr j) :
    (insertedCalendar C slot).age ((insertedGraph G slot).source e) -
      (insertedCalendar C slot).age ((insertedGraph G slot).target e) =
        newDuration C slot := by
  rcases he with rfl | ⟨j,rfl⟩
  · simp [insertedCalendar,insertedGraph,lowerEdge,insertedAge,hybrid,newDuration]
    <;> ring
  · by_cases hj : j = 0
    · simp [insertedCalendar,insertedGraph,hj,insertedAge,upper,newDuration]
      <;> ring
    · simp [insertedCalendar,insertedGraph,hj,insertedAge,upper,hybrid,newDuration]
      <;> ring

def liftedLeaf (N : RootedBinary V E X) : X ↪ FreshVertex V where
  toFun x := .inl (N.leaf x)
  inj' := fun _ _ h => N.leaf.injective (Sum.inl.inj h)

def liftedRegister (reg : V → Bool) (freshBit : Bool) : FreshVertex V → Bool
  | .inl v => reg v
  | .inr b => if b then false else freshBit

@[simp] theorem liftedRegister_old (reg : V → Bool) (b : Bool) (v : V) :
    liftedRegister reg b (.inl v) = reg v := rfl

@[simp] theorem liftedRegister_hybrid (reg : V → Bool) (b : Bool) :
    liftedRegister reg b hybrid = b := rfl

theorem fresh_vertices_not_old (v : V) :
    (hybrid : FreshVertex V) ≠ .inl v ∧ upper ≠ .inl v := by
  simp [hybrid,upper]

/-- Exact endpoint exclusions required at the safe original-edge gathering
use site. They are derived from the fresh tags, not an epoch swap premise. -/
theorem fresh_nodes_avoid_outside_endpoints (G : EdgeGraph V E)
    (slot e : E) (he : e ≠ slot) (v : FreshVertex V)
    (hv : v = hybrid ∨ v = upper) :
    v ≠ (insertedGraph G slot).source (.inl e) ∧
      v ≠ (insertedGraph G slot).target (.inl e) := by
  rw [outside_source G slot e he,old_target]
  rcases hv with rfl | rfl <;> simp [hybrid,upper]

theorem outside_nodes_avoid_arm_endpoints (G : EdgeGraph V E) (slot : E)
    (v : V) (e : FreshEdge E) (he : e = arm0 ∨ e = arm1) :
    Sum.inl v ≠ (insertedGraph G slot).source e ∧
      Sum.inl v ≠ (insertedGraph G slot).target e := by
  rcases he with rfl | rfl <;>
    norm_num [insertedGraph,arm0,arm1,upper,hybrid]

end GProgram.G3.FreshOriginalBridgeCalendar
