import ZeroRunSignature
set_option warningAsError true

namespace AlexanderZeroRun
open ResearchCommons.TriangleRun ResearchCommons.TwoLiftTriangle

/-- An intrinsic predicate: no finite list includes all qualifying vertices. -/
def UnboundedRepresentatives {V : Type _} (P : V → Prop) : Prop :=
  ∀ xs : List V, ∃ v, v ∉ xs ∧ P v

theorem unboundedRepresentatives_rename {V W : Type _} (f : V → W) (g : W → V)
    (fg : ∀ x, f (g x) = x) (gf : ∀ x, g (f x) = x)
    (P : V → Prop) (Q : W → Prop) (preserve : ∀ x, P x ↔ Q (f x)) :
    UnboundedRepresentatives P ↔ UnboundedRepresentatives Q := by
  constructor
  · intro h xs
    obtain ⟨v,hv,hP⟩ := h (xs.map g)
    refine ⟨f v, ?_, (preserve v).1 hP⟩
    intro hin
    exact hv (List.mem_map.mpr ⟨f v,hin,gf v⟩)
  · intro h xs
    obtain ⟨w,hw,hQ⟩ := h (xs.map f)
    refine ⟨g w, ?_, (preserve (g w)).2 (by simpa only [fg] using hQ)⟩
    intro hin
    exact hw (List.mem_map.mpr ⟨g w,hin,fg w⟩)

private def maxLevel : List Vertex → Nat
  | [] => 0
  | x::xs => max x.1 (maxLevel xs)

private theorem mem_level_le (v : Vertex) (xs : List Vertex) (h : v ∈ xs) :
    v.1 ≤ maxLevel xs := by
  induction xs with
  | nil => simp at h
  | cons x xs ih =>
    rcases List.mem_cons.mp h with rfl | ht
    · exact Nat.le_max_left _ _
    · exact Nat.le_trans (ih ht) (Nat.le_max_right _ _)

theorem levels_iff_unbounded_representatives (P : Vertex → Prop) :
    (∀ bound, ∃ u, bound ≤ u.1 ∧ P u) ↔ UnboundedRepresentatives P := by
  constructor
  · intro h xs
    obtain ⟨u,hu,hp⟩ := h (maxLevel xs+1)
    refine ⟨u,?_,hp⟩
    intro hi
    have hl := mem_level_le u xs hi
    omega
  · intro h bound
    let xs := (List.range bound).flatMap fun n => [(n,false),(n,true)]
    obtain ⟨u,hu,hp⟩ := h xs
    refine ⟨u,?_,hp⟩
    by_cases hi : bound ≤ u.1
    · exact hi
    · exfalso
      apply hu
      apply List.mem_flatMap.mpr
      refine ⟨u.1,List.mem_range.mpr (by omega),?_⟩
      rcases u with ⟨j,b⟩
      cases b <;> simp

/-- The two-sheet source's selected sizes are characterized without any level
or birthdate information in the observation itself. -/
theorem intrinsic_component_size_iff (A : Nat → Prop) (keep : Vertex → Prop)
    (D m : Nat) (after : ∀ v, D < v.1 → keep v) :
    UnboundedRepresentatives
      (fun u => HasComponentSize (GraphTriangleEdge (twist A) keep) u (m+3)) ↔ A m :=
  (levels_iff_unbounded_representatives _).symm.trans (late_component_size_iff A keep D m after)

#print axioms unboundedRepresentatives_rename
#print axioms intrinsic_component_size_iff
end AlexanderZeroRun
