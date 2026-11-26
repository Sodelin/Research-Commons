import Lean

set_option warningAsError true

namespace AlexanderOmnibus

universe u v
variable {A : Type u} {B : Type v}

inductive Walk (E : A → A → Prop) (x : A) : A → Prop
  | nil : Walk E x x
  | step {y z : A} : Walk E x y → E y z → Walk E x z

def keepEdge (E : A → A → Prop) (keep : A → Prop) (x y : A) : Prop :=
  keep x ∧ keep y ∧ E x y

theorem walk_ends_kept (E : A → A → Prop) (keep : A → Prop)
    {x y : A} (hx : keep x) (h : Walk (keepEdge E keep) x y) : keep y := by
  cases h with
  | nil => exact hx
  | step _ he => exact he.2.1

theorem walk_image (G : A → A → Prop) (H : B → B → Prop)
    (f : A → B) (forward : ∀ x y, G x y → H (f x) (f y))
    {x y : A} (h : Walk G x y) : Walk H (f x) (f y) := by
  induction h with
  | nil => exact .nil
  | step _ he ih => exact .step ih (forward _ _ he)

theorem neighbor_lift_after_deletion
    (G : A → A → Prop) (H : B → B → Prop) (keep : B → Prop)
    (f : A → B)
    (lift : ∀ x, keep (f x) → ∀ z, H (f x) z → ∃ y, G x y ∧ f y = z)
    (x : A) (z : B) (hz : keepEdge H keep (f x) z) :
    ∃ y, keepEdge G (fun a => keep (f a)) x y ∧ f y = z := by
  obtain ⟨y, he, hy⟩ := lift x hz.1 z hz.2.2
  refine ⟨y, ⟨hz.1, ?_, he⟩, hy⟩
  simpa only [hy] using hz.2.1

theorem walk_lift_after_deletion
    (G : A → A → Prop) (H : B → B → Prop) (keep : B → Prop)
    (f : A → B)
    (lift : ∀ x, keep (f x) → ∀ z, H (f x) z → ∃ y, G x y ∧ f y = z)
    (x : A) {z : B} (hz : Walk (keepEdge H keep) (f x) z) :
    ∃ y, Walk (keepEdge G (fun a => keep (f a))) x y ∧ f y = z := by
  induction hz with
  | nil => exact ⟨x, .nil, rfl⟩
  | @step v z _ he ih =>
    obtain ⟨last, hl, hv⟩ := ih
    rw [← hv] at he
    obtain ⟨y, hly, hf⟩ := neighbor_lift_after_deletion G H keep f lift last z he
    exact ⟨y, .step hl hly, hf⟩

/-- The image of a full induced source component is a full induced host
component, assuming local neighbor surjectivity at retained source vertices. -/
theorem same_component_iff
    (G : A → A → Prop) (H : B → B → Prop) (keep : B → Prop) (f : A → B)
    (forward : ∀ x y, G x y → H (f x) (f y))
    (lift : ∀ x, keep (f x) → ∀ z, H (f x) z → ∃ y, G x y ∧ f y = z)
    (x : A) (z : B) :
    Walk (keepEdge H keep) (f x) z ↔
      ∃ y, Walk (keepEdge G (fun a => keep (f a))) x y ∧ f y = z := by
  constructor
  · exact walk_lift_after_deletion G H keep f lift x
  · rintro ⟨y, hy, rfl⟩
    exact walk_image _ _ f (fun a b e => ⟨e.1, e.2.1, forward a b e.2.2⟩) hy

theorem induced_adjacency_iff
    (G : A → A → Prop) (H : B → B → Prop) (keep : B → Prop) (f : A → B)
    (hinj : ∀ {a b : A}, f a = f b → a = b)
    (forward : ∀ x y, G x y → H (f x) (f y))
    (lift : ∀ x, keep (f x) → ∀ z, H (f x) z → ∃ y, G x y ∧ f y = z)
    (x y : A) :
    keepEdge H keep (f x) (f y) ↔ keepEdge G (fun a => keep (f a)) x y := by
  constructor
  · intro h
    obtain ⟨w, hw, he⟩ := neighbor_lift_after_deletion G H keep f lift x (f y) h
    have hwy : w = y := hinj he
    simpa only [hwy] using hw
  · intro h
    exact ⟨h.1, h.2.1, forward x y h.2.2⟩

private theorem nodup_map_of_injective (f : A → B)
    (hinj : ∀ {a b : A}, f a = f b → a = b) (xs : List A)
    (h : xs.Nodup) : (xs.map f).Nodup := by
  induction xs with
  | nil => simp
  | cons a as ih =>
    have h' := List.nodup_cons.mp h
    refine List.nodup_cons.mpr ⟨?_, ih h'.2⟩
    intro ha
    obtain ⟨b, hb, hba⟩ := List.mem_map.mp ha
    have he : b = a := hinj hba
    exact h'.1 (he ▸ hb)

private theorem same_length_subset_covers
    (xs ys : List B) (hn : xs.Nodup) (hsub : xs ⊆ ys)
    (hlen : xs.length = ys.length) : ys ⊆ xs := by
  classical
  intro z hz
  by_cases h : z ∈ xs
  · exact h
  · exfalso
    have hs : xs ⊆ ys.erase z := by
      intro b hb
      have hne : b ≠ z := by
        intro he
        exact h (he ▸ hb)
      exact (List.mem_erase_of_ne hne).2 (hsub hb)
    have hle := List.Nodup.length_le_of_subset hn hs
    have he := List.length_erase_of_mem hz
    have hpos : 0 < ys.length := List.length_pos_of_mem hz
    omega

/-- An injective weak edge map is locally onto at any vertex whose source and
target finite neighbor lists have equal length. Only the source list needs Nodup. -/
theorem neighbor_lift_of_same_degree
    (G : A → A → Prop) (H : B → B → Prop) (f : A → B)
    (hinj : ∀ {a b : A}, f a = f b → a = b)
    (forward : ∀ x y, G x y → H (f x) (f y))
    (x : A) (sourceNbr : List A) (hostNbr : List B)
    (hd : sourceNbr.Nodup)
    (hsource : ∀ y, y ∈ sourceNbr ↔ G x y)
    (htarget : ∀ z, z ∈ hostNbr ↔ H (f x) z)
    (hcount : sourceNbr.length = hostNbr.length) :
    ∀ z, H (f x) z → ∃ y, G x y ∧ f y = z := by
  have hs : sourceNbr.map f ⊆ hostNbr := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hz
    exact (htarget _).2 (forward _ _ ((hsource y).1 hy))
  have hlen : (sourceNbr.map f).length = hostNbr.length := by
    simpa using hcount
  have hc := same_length_subset_covers _ _ (nodup_map_of_injective f hinj _ hd) hs hlen
  intro z hz
  obtain ⟨y, hy, he⟩ := List.mem_map.mp (hc ((htarget z).2 hz))
  exact ⟨y, (hsource y).1 hy, he⟩

#print axioms neighbor_lift_of_same_degree
#print axioms same_component_iff
#print axioms induced_adjacency_iff

end AlexanderOmnibus
