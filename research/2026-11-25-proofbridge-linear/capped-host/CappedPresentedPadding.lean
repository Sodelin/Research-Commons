import SamuelAlexanderResearch.PopulationReindex
import CappedPaddingLanguage

namespace ResearchCommons.CappedPresentedPadding
open PopulationReindex BirthOrder ResearchCommons.CappedPaddingLanguage

/-- A finite component with exact local population obligations. -/
structure FinitePad (W Time : Type) [LT Time] (k d : Nat) where
  birth : W → Time
  edge : W → W → Option Nat
  cover : List W
  cover_all : ∀ w, w ∈ cover
  ordered : ∀ w v, (edge w v).isSome = true → birth w < birth v
  label_valid : ∀ w v l, edge w v = some l → l < k
  parent_of_label : ∀ y, ¬ NoParents edge y → ∀ l, l < k → ∃ x, edge x y = some l
  children : ∀ x, ∃ ys : List W, ys.length ≤ d ∧
    ∀ y, (edge x y).isSome = true → y ∈ ys

/-- A finite disjoint component preserves the actual population contract,
with no shift or restriction on the original dates. -/
def attach {V W Time : Type} [LE Time] [LT Time]
    {birth : V → Time} {k d : Nat}
    (p : PresentedPopulation birth k d) (q : FinitePad W Time k d) :
    PresentedPopulation (Sum.elim birth q.birth) k d where
  infinite := by
    intro xs
    obtain ⟨v,hv⟩ := p.infinite (xs.filterMap fun x => match x with
      | .inl a => some a
      | .inr _ => none)
    refine ⟨Sum.inl v,?_⟩
    intro hm
    apply hv
    exact List.mem_filterMap.mpr ⟨Sum.inl v,hm,rfl⟩
  finite_sublevels := by
    intro t
    obtain ⟨xs,hx⟩ := p.finite_sublevels t
    refine ⟨xs.map Sum.inl ++ q.cover.map Sum.inr,?_⟩
    intro u h
    cases u with
    | inl u => exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨u,hx u h,rfl⟩))
    | inr u => exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨u,q.cover_all u,rfl⟩))
  edge := joined p.edge q.edge
  birth_order := by
    intro x y h
    cases x <;> cases y
    · exact p.birth_order _ _ h
    · simp [joined] at h
    · simp [joined] at h
    · exact q.ordered _ _ h
  label_valid := by
    intro x y l h
    cases x <;> cases y
    · exact p.label_valid _ _ l h
    · simp [joined] at h
    · simp [joined] at h
    · exact q.label_valid _ _ l h
  roots_finite := by
    obtain ⟨xs,hx⟩ := p.roots_finite
    refine ⟨xs.map Sum.inl ++ q.cover.map Sum.inr,?_⟩
    intro v hv
    cases v with
    | inl a =>
      have ra : NoParents p.edge a := fun x => hv (Sum.inl x)
      exact List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨a,hx a ra,rfl⟩))
    | inr a => exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨a,q.cover_all a,rfl⟩))
  parent_of_label := by
    intro v hv l hl
    cases v with
    | inl a =>
      have hreal : ¬ NoParents p.edge a := by
        intro no
        apply hv
        intro x
        cases x with
        | inl x => exact no x
        | inr _ => rfl
      obtain ⟨x,hx⟩ := p.parent_of_label a hreal l hl
      exact ⟨Sum.inl x,hx⟩
    | inr a =>
      have hreal : ¬ NoParents q.edge a := by
        intro no
        apply hv
        intro x
        cases x with
        | inl _ => rfl
        | inr x => exact no x
      obtain ⟨x,hx⟩ := q.parent_of_label a hreal l hl
      exact ⟨Sum.inr x,hx⟩
  children := by
    intro v
    cases v with
    | inl a =>
      obtain ⟨xs,hx,cover⟩ := p.children a
      refine ⟨xs.map Sum.inl, by simpa using hx,?_⟩
      intro y hy
      cases y with
      | inl y => exact List.mem_map.mpr ⟨y,cover y hy,rfl⟩
      | inr _ => simp [joined] at hy
    | inr a =>
      obtain ⟨xs,hx,cover⟩ := q.children a
      refine ⟨xs.map Sum.inr, by simpa using hx,?_⟩
      intro y hy
      cases y with
      | inl _ => simp [joined] at hy
      | inr y => exact List.mem_map.mpr ⟨y,cover y hy,rfl⟩

#print axioms attach
end ResearchCommons.CappedPresentedPadding
