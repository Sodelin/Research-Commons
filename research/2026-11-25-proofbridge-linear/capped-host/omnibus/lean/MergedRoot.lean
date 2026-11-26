import TwoLiftLanguage
set_option warningAsError true

namespace AlexanderOmnibus.MergedRoot

abbrev Vertex := Option (Nat × Bool)

def level : Vertex → Nat
  | none => 0
  | some (n, _) => n+1

def merge : Nat × Bool → Vertex
  | (0, _) => none
  | (n+1, s) => some (n, s)

theorem merge_level (u : Nat × Bool) : level (merge u) = u.1 := by
  rcases u with ⟨n,s⟩
  cases n <;> rfl

def Up (twist : Nat → Bool) : Vertex → Vertex → Prop
  | none, some (i, _) => i = 1
  | some (i, s), some (j, t) =>
      (j = i+1 ∧ t = s) ∨ (j = i+2 ∧ t = Bool.xor s (twist (i+1)))
  | _, none => False

def Edge (labels twist : Nat → Bool) (u v : Vertex) (l : Bool) : Prop :=
  BinaryAvoidance.Edge labels (level u) (level v) l ∧ Up twist u v

theorem merge_preserves_up (twist : Nat → Bool) (u v : Nat × Bool)
    (h : ResearchCommons.TwoLiftTriangle.Up twist u v) :
    Up twist (merge u) (merge v) := by
  rcases u with ⟨i,s⟩
  rcases v with ⟨j,t⟩
  change (0 < i ∧ j = i+1 ∧ t = s) ∨
    (j = i+2 ∧ t = Bool.xor s (twist i)) at h
  cases i with
  | zero =>
    rcases h with ⟨hi, _, _⟩ | ⟨hj,_⟩
    · omega
    · subst j
      rfl
  | succ i =>
    cases j with
    | zero =>
      rcases h with ⟨_,hj,_⟩ | ⟨hj,_⟩ <;> omega
    | succ j =>
      change (j = i+1 ∧ t = s) ∨ (j = i+2 ∧ t = Bool.xor s (twist (i+1)))
      rcases h with ⟨_,hj,hs⟩ | ⟨hj,hs⟩
      · exact .inl ⟨by omega, hs⟩
      · exact .inr ⟨by omega, hs⟩

theorem same_language (labels twist word : Nat → Bool) :
    (∃ p : Nat → Vertex, ∀ n, Edge labels twist (p n) (p (n+1)) (word n)) ↔
    (∃ p : Nat → Nat, ∀ n, BinaryAvoidance.Edge labels (p n) (p (n+1)) (word n)) := by
  constructor
  · rintro ⟨p,h⟩
    exact ⟨fun n => level (p n), fun n => (h n).1⟩
  · intro h
    obtain ⟨p,hp⟩ := (ResearchCommons.TwoLiftLanguage.same_language labels twist word).mpr h
    refine ⟨fun n => merge (p n), fun n => ⟨?_, ?_⟩⟩
    · simpa only [merge_level] using (hp n).1
    · exact merge_preserves_up twist _ _ (hp n).2

def children (twist : Nat → Bool) : Vertex → List Vertex
  | none => [some (1,false), some (1,true)]
  | some (i,s) => [some (i+1,s), some (i+2,Bool.xor s (twist (i+1)))]

theorem children_spec (twist : Nat → Bool) (u v : Vertex) :
    v ∈ children twist u ↔ Up twist u v := by
  cases u with
  | none =>
    cases v with
    | none => simp [children, Up]
    | some v =>
      rcases v with ⟨i,s⟩
      cases s <;> simp [children, Up]
  | some u =>
    rcases u with ⟨i,s⟩
    cases v with
    | none => simp [children, Up]
    | some v =>
      rcases v with ⟨j,t⟩
      simp [children, Up]

theorem children_exactly_two (twist : Nat → Bool) (u : Vertex) :
    (children twist u).length = 2 ∧ (children twist u).Nodup := by
  cases u with
  | none => simp [children]
  | some u =>
    rcases u with ⟨i,s⟩
    simp [children]

private theorem xor_flip (x s b : Bool) :
    s = Bool.xor x b ↔ x = Bool.xor s b := by
  cases x <;> cases s <;> cases b <;> decide

def parents (twist : Nat → Bool) : Vertex → List Vertex
  | none => []
  | some (0,_) => []
  | some (1,s) => [some (0,s), none]
  | some (i+2,s) =>
      [some (i+1,s), some (i,Bool.xor s (twist (i+1)))]

theorem level_step (twist : Nat → Bool) (u v : Vertex) (h : Up twist u v) :
    2 ≤ level v ∧ (level v = level u+1 ∨ level v = level u+2) := by
  cases v with
  | none => cases u <;> simp [Up] at h
  | some v =>
    rcases v with ⟨j,s⟩
    cases u with
    | none => simp [Up] at h; simp [h, level]
    | some u =>
      rcases u with ⟨i,t⟩
      change (_ ∧ _) ∨ (_ ∧ _) at h
      simp only [level]
      rcases h with ⟨h,_⟩ | ⟨h,_⟩ <;> omega

theorem edge_exists_iff (labels twist : Nat → Bool) (u v : Vertex) :
    (∃ l, Edge labels twist u v l) ↔ Up twist u v := by
  constructor
  · rintro ⟨l, _, hup⟩
    exact hup
  · intro h
    obtain ⟨hv, hs | hl⟩ := level_step twist u v h
    · exact ⟨BinaryAvoidance.row labels (level v), ⟨hv, .inl ⟨hs, rfl⟩⟩, h⟩
    · exact ⟨!(BinaryAvoidance.row labels (level v)), ⟨hv, .inr ⟨hl, rfl⟩⟩, h⟩

theorem parents_spec (twist : Nat → Bool) (u v : Vertex) :
    u ∈ parents twist v ↔ Up twist u v := by
  cases v with
  | none => cases u <;> simp [parents, Up]
  | some v =>
    rcases v with ⟨j,s⟩
    cases j with
    | zero =>
      cases u with
      | none => simp [parents, Up]
      | some u =>
        rcases u with ⟨i,t⟩
        simp [parents, Up]
    | succ j =>
      cases j with
      | zero =>
        cases u with
        | none => simp [parents, Up]
        | some u =>
          rcases u with ⟨i,t⟩
          simp [parents, Up, eq_comm]
      | succ j =>
        cases u with
        | none => simp [parents, Up]
        | some u =>
          rcases u with ⟨i,t⟩
          simp [parents, Up, xor_flip t s]
          constructor
          · rintro (⟨h, e⟩ | ⟨h, e⟩)
            · exact .inl ⟨h.symm, e.symm⟩
            · subst i
              exact .inr ⟨rfl,e⟩
          · rintro (⟨h, e⟩ | ⟨h, e⟩)
            · exact .inl ⟨h.symm, e.symm⟩
            · subst i
              exact .inr ⟨rfl,e⟩

theorem roots_exactly (twist : Nat → Bool) (v : Vertex) :
    (∀ u, ¬ Up twist u v) ↔ v = none ∨ ∃ s : Bool, v = some (0,s) := by
  cases v with
  | none => simp [← parents_spec, parents]
  | some v =>
    rcases v with ⟨i,s⟩
    cases i with
    | zero => simp [← parents_spec, parents]
    | succ i =>
      constructor
      · intro h
        have hex : Up twist (some (i,s)) (some (i+1,s)) := Or.inl ⟨rfl,rfl⟩
        exact False.elim (h _ hex)
      · simp

theorem label_unique (labels twist : Nat → Bool) (u v : Vertex) (a b : Bool)
    (ha : Edge labels twist u v a) (hb : Edge labels twist u v b) : a = b := by
  rcases ha.1.2 with ⟨ha, ea⟩ | ⟨ha, ea⟩ <;>
    rcases hb.1.2 with ⟨hb, eb⟩ | ⟨hb, eb⟩
  · exact ea.trans eb.symm
  · omega
  · omega
  · exact ea.trans eb.symm

theorem level_increases (labels twist : Nat → Bool) (u v : Vertex) (l : Bool)
    (h : Edge labels twist u v l) : level u < level v := by
  rcases (level_step twist u v h.2).2 with h | h <;> omega

theorem two_parents_opposite_labels (labels twist : Nat → Bool) (i : Nat) (s : Bool) :
    ∃ a b : Vertex, a ≠ b ∧
      Edge labels twist a (some (i+1,s)) (BinaryAvoidance.row labels (i+2)) ∧
      Edge labels twist b (some (i+1,s)) (!(BinaryAvoidance.row labels (i+2))) := by
  let a : Vertex := some (i,s)
  have ha : Edge labels twist a (some (i+1,s)) (BinaryAvoidance.row labels (i+2)) := by
    exact ⟨⟨by simp [level], .inl ⟨by simp [level, a], rfl⟩⟩, .inl ⟨rfl,rfl⟩⟩
  cases i with
  | zero =>
    exact ⟨a, none, by simp [a], ha, ⟨⟨by simp [level], .inr ⟨rfl,rfl⟩⟩, rfl⟩⟩
  | succ i =>
    let b : Vertex := some (i, Bool.xor s (twist (i+1)))
    have hx : s = Bool.xor (Bool.xor s (twist (i+1))) (twist (i+1)) := by
      exact (xor_flip _ _ _).2 rfl
    exact ⟨a,b,by simp [a,b],ha, ⟨⟨by simp [level], .inr ⟨by simp [level,b],rfl⟩⟩, .inr ⟨rfl,hx⟩⟩⟩

#print axioms label_unique
#print axioms two_parents_opposite_labels
#print axioms parents_spec
#print axioms roots_exactly
#print axioms edge_exists_iff
#print axioms same_language
#print axioms children_spec
#print axioms children_exactly_two

end AlexanderOmnibus.MergedRoot
