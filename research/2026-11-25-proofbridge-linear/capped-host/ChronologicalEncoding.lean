import SamuelAlexanderResearch.PopulationReindex

/-! Exact encoding of a chronological edge-labelled relation. No edge, label,
or fixed source gender is changed when presenting the graph to the Nat provider. -/

namespace ChronologicalEncoding

open BirthOrder PopulationReindex PopulationCounting

universe u v
variable {V : Type u} {Time : Type v} [LE Time] [LT Time]
variable {birth : V → Time} {k d : Nat}

structure RelationalPopulation (birth : V → Time) (k d : Nat) where
  E : V → V → Nat → Prop
  unique : ∀ x y a b, E x y a → E x y b → a = b
  valid : ∀ x y l, E x y l → l < k
  increasing : ∀ x y l, E x y l → birth x < birth y
  infinite : InfiniteVertices V
  sublevel : FiniteSublevels birth
  roots : FiniteCover (fun y => ∀ x l, ¬ E x y l)
  parent : ∀ y, (¬ ∀ x l, ¬ E x y l) → ∀ l, l < k → ∃ x, E x y l
  children : ∀ x, ∃ ys : List V, ys.length ≤ d ∧
    ∀ y, (∃ l, E x y l) → y ∈ ys

noncomputable def encode (p : RelationalPopulation birth k d) (x y : V) : Option Nat := by
  classical
  exact if h : ∃ l, p.E x y l then some (Classical.choose h) else none

theorem encode_some_iff (p : RelationalPopulation birth k d) (x y : V) (l : Nat) :
    encode p x y = some l ↔ p.E x y l := by
  classical
  unfold encode
  split
  · rename_i h
    constructor
    · intro hsome
      cases hsome
      exact Classical.choose_spec h
    · intro he
      exact congrArg some (p.unique _ _ _ _ (Classical.choose_spec h) he)
  · rename_i h
    constructor
    · intro hnone; cases hnone
    · intro hE; exact False.elim (h ⟨l, hE⟩)

theorem encode_isSome_iff (p : RelationalPopulation birth k d) (x y : V) :
    (encode p x y).isSome = true ↔ ∃ l, p.E x y l := by
  constructor
  · intro h
    cases he : encode p x y with
    | none => simp [he] at h
    | some l => exact ⟨l, (encode_some_iff p x y l).mp he⟩
  · rintro ⟨l, hl⟩
    simp [(encode_some_iff p x y l).mpr hl]

theorem encode_noParents_iff (p : RelationalPopulation birth k d) (y : V) :
    NoParents (encode p) y ↔ ∀ x l, ¬ p.E x y l := by
  constructor
  · intro h x l he
    have := (encode_some_iff p x y l).mpr he
    simp [h x] at this
  · intro h x
    cases he : encode p x y with
    | none => rfl
    | some l => exact False.elim (h x l ((encode_some_iff p x y l).mp he))

noncomputable def present (p : RelationalPopulation birth k d) :
    PresentedPopulation birth k d where
  infinite := p.infinite
  finite_sublevels := p.sublevel
  edge := encode p
  birth_order := by
    intro x y he
    obtain ⟨l, hl⟩ := (encode_isSome_iff p x y).mp he
    exact p.increasing x y l hl
  label_valid := fun x y l h => p.valid x y l ((encode_some_iff p x y l).mp h)
  roots_finite := by
    obtain ⟨xs, hxs⟩ := p.roots
    exact ⟨xs, fun y h => hxs y ((encode_noParents_iff p y).mp h)⟩
  parent_of_label := by
    intro y hy l hl
    obtain ⟨x, hx⟩ := p.parent y (fun h => hy ((encode_noParents_iff p y).mpr h)) l hl
    exact ⟨x, (encode_some_iff p x y l).mpr hx⟩
  children := by
    intro x
    obtain ⟨ys, hsize, hys⟩ := p.children x
    exact ⟨ys, hsize, fun y he => hys y ((encode_isSome_iff p x y).mp he)⟩

variable [Std.IsLinearPreorder Time] [Std.LawfulOrderLT Time]

theorem exact_label (p : RelationalPopulation birth k d) (i j l : Nat) :
    (toNatPopulation (present p)).edge i j = some l ↔
      p.E ((enumeration (present p)).toFun i) ((enumeration (present p)).toFun j) l :=
  encode_some_iff p _ _ _

theorem exact_adjacency (p : RelationalPopulation birth k d) (i j : Nat) :
    ((toNatPopulation (present p)).edge i j).isSome = true ∨
      ((toNatPopulation (present p)).edge j i).isSome = true ↔
    (∃ l, p.E ((enumeration (present p)).toFun i) ((enumeration (present p)).toFun j) l) ∨
      (∃ l, p.E ((enumeration (present p)).toFun j) ((enumeration (present p)).toFun i) l) :=
  or_congr (encode_isSome_iff p _ _) (encode_isSome_iff p _ _)

theorem exact_source_gender (p : RelationalPopulation birth k d) (gender : V → Nat) :
    (∀ x y l, p.E x y l → gender x = l) ↔
      ∀ i j l, (toNatPopulation (present p)).edge i j = some l →
        gender ((enumeration (present p)).toFun i) = l := by
  constructor
  · intro h i j l hij
    exact h _ _ _ ((exact_label p i j l).mp hij)
  · intro h x y l hxy
    obtain ⟨i, hi⟩ := (enumeration (present p)).surjective x
    obtain ⟨j, hj⟩ := (enumeration (present p)).surjective y
    have h' := h i j l ((exact_label p i j l).mpr (by simpa [hi, hj] using hxy))
    simpa [hi] using h'

end ChronologicalEncoding

#print axioms ChronologicalEncoding.exact_label
#print axioms ChronologicalEncoding.exact_adjacency
#print axioms ChronologicalEncoding.exact_source_gender
