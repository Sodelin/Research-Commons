import Lean

set_option warningAsError true

namespace AlexanderTerminalExtension

universe u v w
variable {V : Type u} {T : Type v} {L : Type w}

def extend (edge : V → L → V → Prop) (attached : V → L → T → Prop) :
    Sum V T → L → Sum V T → Prop
  | .inl a, l, .inl b => edge a l b
  | .inl a, l, .inr t => attached a l t
  | .inr _, _, _ => False

def Realizes {A : Type _} (edge : A → L → A → Prop) (word : Nat → L) : Prop :=
  ∃ path : Nat → A, ∀ i, edge (path i) (word i) (path (i + 1))

def Root {A : Type _} (edge : A → L → A → Prop) (a : A) : Prop :=
  ∀ b l, ¬ edge b l a

theorem realizes_iff (edge : V → L → V → Prop) (attached : V → L → T → Prop)
    (word : Nat → L) : Realizes (extend edge attached) word ↔ Realizes edge word := by
  constructor
  · rintro ⟨path, hp⟩
    have old (i : Nat) : ∃ v : V, path i = .inl v := by
      cases h : path i with
      | inl a => exact ⟨a, rfl⟩
      | inr _ =>
        have hstep := hp i
        rw [h] at hstep
        exact False.elim hstep
    let base (i : Nat) : V := Classical.choose (old i)
    have hb (i : Nat) : path i = .inl (base i) := Classical.choose_spec (old i)
    refine ⟨base, ?_⟩
    intro i
    have hstep := hp i
    rw [hb i, hb (i + 1)] at hstep
    exact hstep
  · rintro ⟨path, hp⟩
    exact ⟨fun i => .inl (path i), hp⟩

theorem old_root_iff (edge : V → L → V → Prop) (attached : V → L → T → Prop)
    (a : V) : Root (extend edge attached) (.inl a) ↔ Root edge a := by
  constructor
  · intro h b l
    exact h (.inl b) l
  · intro h b l
    cases b with
    | inl c => exact h c l
    | inr _ => simp [extend]

theorem new_not_root (edge : V → L → V → Prop) (attached : V → L → T → Prop)
    (t : T) (h : ∃ b l, attached b l t) : ¬ Root (extend edge attached) (.inr t) := by
  rintro hroot
  obtain ⟨b, l, hbl⟩ := h
  exact hroot (.inl b) l hbl

/-- Once the schedule assigns each original parent at most one terminal, the
old finite child cover extends by at most a single vertex. -/
theorem child_cover_one_spare (edge : V → L → V → Prop) (attached : V → L → T → Prop)
    (a : V) (oldChildren : List V)
    (oldCover : ∀ b l, edge a l b → b ∈ oldChildren)
    (one : ∀ t u l m, attached a l t → attached a m u → t = u) :
    ∃ cover : List (Sum V T), cover.length ≤ oldChildren.length + 1 ∧
      ∀ b l, extend edge attached (.inl a) l b → b ∈ cover := by
  classical
  by_cases h : ∃ t l, attached a l t
  · obtain ⟨t,l,ht⟩ := h
    refine ⟨.inr t :: oldChildren.map Sum.inl, by simp, ?_⟩
    intro b m hb
    cases b with
    | inl u => exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨u,oldCover u m hb,rfl⟩)
    | inr u =>
      have e := one t u l m ht hb
      subst u
      simp
  · refine ⟨oldChildren.map Sum.inl, by simp, ?_⟩
    intro b m hb
    cases b with
    | inl u => exact List.mem_map.mpr ⟨u,oldCover u m hb,rfl⟩
    | inr u => exact False.elim (h ⟨u,m,hb⟩)

#print axioms child_cover_one_spare
#print axioms realizes_iff
#print axioms old_root_iff
#print axioms new_not_root

end AlexanderTerminalExtension
