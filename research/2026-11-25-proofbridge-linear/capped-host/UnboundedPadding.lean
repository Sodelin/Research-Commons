import CappedPaddingLanguage

namespace ResearchCommons.CappedPaddingLanguage

/-- An infinite word in a disjoint union is realized entirely in one side. -/
theorem realizes_joined {V W K : Type} (base : V → V → Option K)
    (pad : W → W → Option K) (word : Nat → K) :
    Realizes (joined base pad) word ↔ Realizes base word ∨ Realizes pad word := by
  constructor
  · intro h
    obtain ⟨path, step⟩ := h
    cases first : path 0 with
    | inl v =>
      have left (n : Nat) : ∃ a, path n = Sum.inl a := by
        induction n with
        | zero => exact ⟨v,first⟩
        | succ n ih =>
          obtain ⟨a,ha⟩ := ih
          cases next : path (n+1) with
          | inl b => exact ⟨b,rfl⟩
          | inr b =>
            have no := step n
            simp [ha,next,joined] at no
      let f := fun n => Classical.choose (left n)
      have lift (n : Nat) : path n = Sum.inl (f n) := Classical.choose_spec (left n)
      exact Or.inl ⟨f, fun n => by simpa only [lift n,lift (n+1),joined] using step n⟩
    | inr v =>
      have right (n : Nat) : ∃ a, path n = Sum.inr a := by
        induction n with
        | zero => exact ⟨v,first⟩
        | succ n ih =>
          obtain ⟨a,ha⟩ := ih
          cases next : path (n+1) with
          | inr b => exact ⟨b,rfl⟩
          | inl b =>
            have no := step n
            simp [ha,next,joined] at no
      let f := fun n => Classical.choose (right n)
      have lift (n : Nat) : path n = Sum.inr (f n) := Classical.choose_spec (right n)
      have pr : Realizes pad word :=
        ⟨f,fun n => by simpa only [lift n,lift (n+1),joined] using step n⟩
      exact Or.inr pr
  · rintro (⟨path, step⟩ | ⟨path, step⟩)
    · exact ⟨fun n => Sum.inl (path n), step⟩
    · exact ⟨fun n => Sum.inr (path n), step⟩


/-- Exact local condition: a padding word is harmless iff the base already realizes it. -/
theorem padding_iff {V W K : Type} (base : V → V → Option K)
    (pad : W → W → Option K) (word : Nat → K) :
    (Realizes (joined base pad) word ↔ Realizes base word) ↔
      (Realizes pad word → Realizes base word) := by
  rw [realizes_joined]
  constructor
  · exact fun h hp => h.mp (Or.inr hp)
  · exact fun h => ⟨fun hab => hab.elim id h, Or.inl⟩

/-- A label-preserving map into the base also certifies harmless padding;
it permits cycles and routes all words through a single reusable witness. -/
theorem padding_preserves_of_simulation {V W K : Type} (base : V → V → Option K)
    (pad : W → W → Option K) (f : W → V)
    (maps : ∀ x y k, pad x y = some k → base (f x) (f y) = some k)
    (word : Nat → K) :
    Realizes (joined base pad) word ↔ Realizes base word := by
  apply (padding_iff base pad word).mpr
  rintro ⟨p, steps⟩
  exact ⟨f ∘ p, fun n => maps (p n) (p (n+1)) (word n) (steps n)⟩

/-- Any decreasing accessibility certificate suffices; no uniform bound is needed. -/
theorem no_realization_of_wellFounded {W K : Type} (pad : W → W → Option K)
    (r : W → W → Prop) (wf : WellFounded r)
    (decreases : ∀ x y k, pad x y = some k → r y x) (word : Nat → K) :
    ¬ Realizes pad word := by
  rintro ⟨path, step⟩
  have impossible (x : W) : ∀ n, path n = x → False := by
    induction x using wf.induction with
    | h x ih =>
      intro n h
      have hd := decreases (path n) (path (n+1)) (word n) (step n)
      rw [h] at hd
      exact ih _ hd (n+1) rfl
  exact impossible (path 0) 0 rfl

theorem padding_preserves_of_wellFounded {V W K : Type} (base : V → V → Option K)
    (pad : W → W → Option K) (r : W → W → Prop) (wf : WellFounded r)
    (decreases : ∀ x y k, pad x y = some k → r y x) (word : Nat → K) :
    Realizes (joined base pad) word ↔ Realizes base word :=
  (padding_iff base pad word).mpr fun h =>
    (no_realization_of_wellFounded pad r wf decreases word h).elim

/-- Existing bounded-rank clients are covered without changing their geometry. -/
theorem padding_preserves_of_bounded_rise {V W K : Type} (base : V → V → Option K)
    (pad : W → W → Option K) (rank : W → Nat) (limit : Nat)
    (bounded : ∀ x, rank x ≤ limit)
    (rise : ∀ x y k, pad x y = some k → rank x < rank y) (word : Nat → K) :
    Realizes (joined base pad) word ↔ Realizes base word := by
  let height := fun x : W => limit - rank x
  apply padding_preserves_of_wellFounded base pad (InvImage (· < ·) height)
    (InvImage.wf height Nat.lt_wfRel.wf)
  intro x y k h
  have hx := bounded x
  have hy := bounded y
  have hr := rise x y k h
  change limit - rank y < limit - rank x
  omega

/-- A single graph has finite chains of arbitrarily large length. -/
def countdownEdge (x y : Nat) : Option Unit :=
  if y+1 = x then some () else none

theorem countdown_padding_preserves {V : Type} (base : V → V → Option Unit)
    (word : Nat → Unit) :
    Realizes (joined base countdownEdge) word ↔ Realizes base word := by
  apply padding_preserves_of_wellFounded base countdownEdge (· < ·) Nat.lt_wfRel.wf
  intro x y k h
  simp only [countdownEdge] at h
  split at h
  · rename_i he
    omega
  · contradiction

theorem countdown_has_no_uniform_rising_rank
    (rank : Nat → Nat) (limit : Nat) (bounded : ∀ x, rank x ≤ limit)
    (rise : ∀ x y k, countdownEdge x y = some k → rank x < rank y) : False := by
  have rankDown (n : Nat) : rank n + n ≤ rank 0 := by
    induction n with
    | zero => omega
    | succ n ih =>
      have h := rise (n+1) n () (by simp [countdownEdge])
      omega
  have h := rankDown (limit+1)
  have b := bounded 0
  omega

#print axioms realizes_joined
#print axioms padding_iff
#print axioms padding_preserves_of_simulation
#print axioms padding_preserves_of_wellFounded
#print axioms countdown_has_no_uniform_rising_rank
end ResearchCommons.CappedPaddingLanguage
