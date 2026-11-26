import ComponentTransport

set_option warningAsError true

namespace AlexanderOmnibus

universe u v
variable {A : Type u} {B : Type v}

/-- Local degree witnesses at retained source vertices suffice for both
component coverage and reflection of induced edges after deletion. -/
theorem transport_of_retained_degrees
    (G : A → A → Prop) (H : B → B → Prop) (keep : B → Prop) (f : A → B)
    (hinj : ∀ {a b : A}, f a = f b → a = b)
    (forward : ∀ x y, G x y → H (f x) (f y))
    (degrees : ∀ x, keep (f x) → ∃ (ns : List A) (nt : List B),
      ns.Nodup ∧ (∀ y, y ∈ ns ↔ G x y) ∧
        (∀ z, z ∈ nt ↔ H (f x) z) ∧ ns.length = nt.length) :
    (∀ x z, Walk (keepEdge H keep) (f x) z ↔
      ∃ y, Walk (keepEdge G (fun a => keep (f a))) x y ∧ f y = z) ∧
    (∀ x y, keepEdge H keep (f x) (f y) ↔
      keepEdge G (fun a => keep (f a)) x y) := by
  have lift : ∀ x, keep (f x) → ∀ z, H (f x) z → ∃ y, G x y ∧ f y = z := by
    intro x hx
    obtain ⟨ns, nt, hd, hs, ht, hc⟩ := degrees x hx
    exact neighbor_lift_of_same_degree G H f hinj forward x ns nt hd hs ht hc
  exact ⟨same_component_iff G H keep f forward lift,
    induced_adjacency_iff G H keep f hinj forward lift⟩

private def twoPath (x y : Fin 2) : Prop := x ≠ y
private def threePath (x y : Fin 3) : Prop :=
  (x.val + 1 = y.val) ∨ (y.val + 1 = x.val)
private def includeTwo (x : Fin 2) : Fin 3 := ⟨x.val, by have := x.isLt; omega⟩

/-- Dropping the degree condition would make even neighbor lifting false:
the middle of the host path has a neighbor outside the image. -/
theorem unequal_degree_counterexample :
    (∀ a b : Fin 2, includeTwo a = includeTwo b → a = b) ∧
    (∀ a b, twoPath a b → threePath (includeTwo a) (includeTwo b)) ∧
    threePath (includeTwo 1) 2 ∧
    ¬ (∃ y, twoPath 1 y ∧ includeTwo y = 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a b h
    exact Fin.ext (congrArg (fun t : Fin 3 => t.val) h)
  · intro a b h
    unfold twoPath at h
    have hval : a.val ≠ b.val := fun h' => h (Fin.ext h')
    have ha := a.isLt
    have hb := b.isLt
    change a.val + 1 = b.val ∨ b.val + 1 = a.val
    omega
  · exact Or.inl rfl
  · rintro ⟨y, _, h⟩
    have hval : y.val = 2 := congrArg Fin.val h
    have hy := y.isLt
    omega

#print axioms transport_of_retained_degrees
#print axioms unequal_degree_counterexample

end AlexanderOmnibus
