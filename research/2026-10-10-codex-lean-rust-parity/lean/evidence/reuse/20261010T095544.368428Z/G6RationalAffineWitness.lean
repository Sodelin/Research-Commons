import StrictAffineElimination

/-!
# Executable rational witnesses for strict affine source cells

Contributor: Codex / lean_reuse, 10 October 2026.
This fills the witness-returning gap of the existing Boolean Fourier--Motzkin
decider. It reuses the exact emitted rational rows and elimination criterion.
It does not supply an original graph, a source chart, nonlinear law constraints,
an unknown-size source census, or general G3 exact recognition.

The chosen coordinate is the midpoint of distinct finite extremal bounds,
their shared endpoint when equal, one unit beyond a lone finite bound, or zero.
All executable definitions use rational arithmetic and decidable finite data.
-/
namespace UnifiedLean.G6.RationalAffineWitness

open UnifiedLean.G6.StrictAffineElimination

/-- A deterministic rational coordinate for a compatible finite interval. -/
def boundsWitness (L U : Finset (ℚ × Bool)) : ℚ :=
  if hL : L.Nonempty then
    let a := (L.image Prod.fst).max' (hL.image _)
    if hU : U.Nonempty then
      let b := (U.image Prod.fst).min' (hU.image _)
      if a < b then (a + b) / 2 else a
    else a + 1
  else if hU : U.Nonempty then
    (U.image Prod.fst).min' (hU.image _) - 1
  else 0

/-- Strict and weak bounds, empty sides, and feasible singleton intervals
are handled by the same executable coordinate selection. -/
theorem boundsWitness_spec (L U : Finset (ℚ × Bool))
    (h : ∀ l ∈ L, ∀ u ∈ U, Rel (l.2 || u.2) l.1 u.1) :
    (∀ l ∈ L, Rel l.2 l.1 (boundsWitness L U)) ∧
    (∀ u ∈ U, Rel u.2 (boundsWitness L U) u.1) := by
  by_cases hL : L.Nonempty
  · let A := L.image Prod.fst
    have hA : A.Nonempty := hL.image _
    let a := A.max' hA
    obtain ⟨l₀, hl₀, hlval⟩ := Finset.mem_image.mp (A.max'_mem hA)
    have lower_le : ∀ l ∈ L, l.1 ≤ a := by
      intro l hl
      exact A.le_max' _ (Finset.mem_image.mpr ⟨l, hl, rfl⟩)
    by_cases hU : U.Nonempty
    · let B := U.image Prod.fst
      have hB : B.Nonempty := hU.image _
      let b := B.min' hB
      obtain ⟨u₀, hu₀, huval⟩ := Finset.mem_image.mp (B.min'_mem hB)
      have upper_le : ∀ u ∈ U, b ≤ u.1 := by
        intro u hu
        exact B.min'_le _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
      have hab : a ≤ b := by
        have hz := rel_le (h l₀ hl₀ u₀ hu₀)
        simpa only [hlval, huval] using hz
      by_cases hlt : a < b
      · have hw : boundsWitness L U = (a + b) / 2 := by
          simp only [boundsWitness, dif_pos hL, dif_pos hU]
          change (if a < b then (a + b) / 2 else a) = (a + b) / 2
          exact if_pos hlt
        rw [hw]
        constructor
        · intro l hl
          apply rel_of_lt
          have := lower_le l hl
          linarith
        · intro u hu
          apply rel_of_lt
          have := upper_le u hu
          linarith
      · have heq : a = b := le_antisymm hab (le_of_not_gt hlt)
        have hw : boundsWitness L U = a := by
          simp only [boundsWitness, dif_pos hL, dif_pos hU]
          change (if a < b then (a + b) / 2 else a) = a
          exact if_neg hlt
        rw [hw]
        constructor
        · intro l hl
          have hz := rel_or_left (h l hl u₀ hu₀)
          simpa only [huval, ← heq] using hz
        · intro u hu
          have hz := rel_or_right (h l₀ hl₀ u hu)
          simpa only [hlval] using hz
    · have hw : boundsWitness L U = a + 1 := by
        simp only [boundsWitness, dif_pos hL, dif_neg hU]
        rfl
      rw [hw]
      constructor
      · intro l hl
        apply rel_of_lt
        have := lower_le l hl
        linarith
      · intro u hu
        exact False.elim (hU ⟨u, hu⟩)
  · by_cases hU : U.Nonempty
    · let B := U.image Prod.fst
      have hB : B.Nonempty := hU.image _
      let b := B.min' hB
      have upper_le : ∀ u ∈ U, b ≤ u.1 := by
        intro u hu
        exact B.min'_le _ (Finset.mem_image.mpr ⟨u, hu, rfl⟩)
      have hw : boundsWitness L U = b - 1 := by
        simp only [boundsWitness, dif_neg hL, dif_pos hU]
        rfl
      rw [hw]
      constructor
      · intro l hl
        exact False.elim (hL ⟨l, hl⟩)
      · intro u hu
        apply rel_of_lt
        have := upper_le u hu
        linarith
    · have hw : boundsWitness L U = 0 := by
        simp only [boundsWitness, dif_neg hL, dif_neg hU]
      rw [hw]
      exact ⟨fun l hl => False.elim (hL ⟨l, hl⟩),
        fun u hu => False.elim (hU ⟨u, hu⟩)⟩

def lowerBounds {n : ℕ} (R : Finset (Row (n+1))) (x : Fin n → ℚ) :
    Finset (ℚ × Bool) :=
  (R.filter fun r => r.last < 0).image (fun r => (r.endpoint x, r.strict))

def upperBounds {n : ℕ} (R : Finset (Row (n+1))) (x : Fin n → ℚ) :
    Finset (ℚ × Bool) :=
  (R.filter fun r => 0 < r.last).image (fun r => (r.endpoint x, r.strict))

/-- Back-substitute one coordinate, without an existence oracle. -/
def liftWitness {n : ℕ} (R : Finset (Row (n+1))) (x : Fin n → ℚ) : ℚ :=
  boundsWitness (lowerBounds R x) (upperBounds R x)

theorem liftWitness_correct {n : ℕ} (R : Finset (Row (n+1))) (x : Fin n → ℚ)
    (hx : ∀ q ∈ project R, q.Holds x) :
    ∀ r ∈ R, r.Holds (Fin.snoc x (liftWitness R x)) := by
  obtain ⟨z, hz⟩ := (project_iff R x).mpr hx
  have hL : ∀ l ∈ lowerBounds R x, Rel l.2 l.1 z := by
    intro l hl
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hl
    obtain ⟨hr, hneg⟩ := Finset.mem_filter.mp hr
    exact (r.holds_neg x z hneg).mp (hz r hr)
  have hU : ∀ u ∈ upperBounds R x, Rel u.2 z u.1 := by
    intro u hu
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hu
    obtain ⟨hr, hpos⟩ := Finset.mem_filter.mp hr
    exact (r.holds_pos x z hpos).mp (hz r hr)
  have hb := boundsWitness_spec (lowerBounds R x) (upperBounds R x)
    ((finite_bounds_iff _ _).mp ⟨z, hL, hU⟩)
  intro r hr
  rcases lt_trichotomy r.last 0 with hneg | hzero | hpos
  · apply (r.holds_neg x (liftWitness R x) hneg).mpr
    exact hb.1 (r.endpoint x, r.strict)
      (Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, hneg⟩, rfl⟩)
  · apply (r.holds_zero x (liftWitness R x) hzero).mpr
    exact (r.holds_zero x z hzero).mp (hz r hr)
  · apply (r.holds_pos x (liftWitness R x) hpos).mpr
    exact hb.2 (r.endpoint x, r.strict)
      (Finset.mem_image.mpr ⟨r, Finset.mem_filter.mpr ⟨hr, hpos⟩, rfl⟩)

/-- A total rational witness-returning solver. `none` means infeasible;
`some q` returns a vector on the original, jointly compiled variables. -/
def solveRational : (n : ℕ) → Finset (Row n) → Option (Fin n → ℚ)
  | 0, R =>
    if ∀ r ∈ R, Rel r.strict (0 : ℚ) r.bound then some Fin.elim0 else none
  | n+1, R =>
    (solveRational n (project R)).map (fun x => Fin.snoc x (liftWitness R x))

/-- An independently executable positive-output certificate checker. -/
def checkRationalWitness {n : ℕ} (R : Finset (Row n)) (q : Fin n → ℚ) : Bool :=
  decide (∀ r ∈ R, r.Holds q)

theorem checkRationalWitness_correct {n : ℕ} (R : Finset (Row n)) (q : Fin n → ℚ) :
    checkRationalWitness R q = true ↔ ∀ r ∈ R, r.Holds q := by
  simp only [checkRationalWitness, decide_eq_true_eq]

theorem solveRational_isSome (n : ℕ) (R : Finset (Row n)) :
    (solveRational n R).isSome = decideFeasible n R := by
  induction n with
  | zero =>
    simp only [solveRational, decideFeasible]
    split <;> simp_all
  | succ n ih =>
    simp only [solveRational, Option.isSome_map, decideFeasible, ih]

theorem solveRational_sound {n : ℕ} (R : Finset (Row n)) (q : Fin n → ℚ)
    (h : solveRational n R = some q) : ∀ r ∈ R, r.Holds q := by
  induction n with
  | zero =>
    simp only [solveRational] at h
    split at h
    · rename_i hx
      have hq : Fin.elim0 = q := Option.some.inj h
      intro r hr
      rw [← hq]
      simpa only [Row.Holds, Row.eval, Finset.univ_eq_empty, Finset.sum_empty,
        Rat.cast_id] using hx r hr
    · contradiction
  | succ n ih =>
    simp only [solveRational] at h
    cases hx : solveRational n (project R) with
    | none => simp only [hx, Option.map_none] at h; contradiction
    | some x =>
      simp only [hx, Option.map_some, Option.some.injEq] at h
      rw [← h]
      exact liftWitness_correct R x (ih (project R) x hx)

/-- Row evaluation commutes with the canonical rational-to-real embedding. -/
theorem rationalWitness_real {n : ℕ} (R : Finset (Row n)) (q : Fin n → ℚ)
    (hq : ∀ r ∈ R, r.Holds q) :
    ∀ r ∈ R, r.Holds (fun i => (q i : ℝ)) := by
  intro r hr
  have he : r.eval (fun i => (q i : ℝ)) = (r.eval q : ℝ) := by
    simp [Row.eval, Rat.cast_sum, Rat.cast_mul]
  rw [Row.Holds, he]
  exact (rat_rel_cast r.strict (r.eval q) r.bound).mpr (hq r hr)

/-- Full soundness and completeness over the original real affine contract. -/
theorem solveRational_complete (n : ℕ) (R : Finset (Row n)) :
    (∃ q, solveRational n R = some q) ↔ Feasible ℝ R := by
  rw [← decideFeasible_correct (K := ℝ), ← solveRational_isSome]
  cases h : solveRational n R <;> simp

theorem solveRational_none_iff (n : ℕ) (R : Finset (Row n)) :
    solveRational n R = none ↔ ¬ Feasible ℝ R := by
  rw [← solveRational_complete]
  cases h : solveRational n R <;> simp

theorem solveRational_checked {n : ℕ} (R : Finset (Row n)) (q : Fin n → ℚ)
    (h : solveRational n R = some q) : checkRationalWitness R q = true :=
  (checkRationalWitness_correct R q).mpr (solveRational_sound R q h)

/-- The ordered wire implementation retains duplicates: zero rows first,
then the Cartesian product with positive rows outermost and negative rows
innermost. This is extensionally the existing finite-set projection. -/
def projectList {n : ℕ} (R : List (Row (n+1))) : List (Row n) :=
  (R.filter fun r => r.last = 0).map Row.drop ++
  (R.filter fun r => 0 < r.last).flatMap (fun p =>
    (R.filter fun r => r.last < 0).map (fun m => p.combine m))

theorem projectList_toFinset {n : ℕ} (R : List (Row (n+1))) :
    (projectList R).toFinset = project R.toFinset := by
  ext q
  simp only [projectList, project, List.mem_toFinset, List.mem_append,
    List.mem_map, List.mem_flatMap, List.mem_filter, Finset.mem_union,
    Finset.mem_image, Finset.mem_filter, Finset.mem_product, List.mem_toFinset,
    Prod.exists]
  aesop

def solveList : (n : ℕ) → List (Row n) → Option (Fin n → ℚ)
  | 0, R =>
    if ∀ r ∈ R, Rel r.strict (0 : ℚ) r.bound then some Fin.elim0 else none
  | n+1, R =>
    (solveList n (projectList R)).map (fun x => Fin.snoc x (liftWitness R.toFinset x))

/-- Exact refinement of ordered/duplicate wire rows to the proved solver;
the selected vector is equal, rather than merely another feasible vector. -/
theorem solveList_eq_solveRational (n : ℕ) (R : List (Row n)) :
    solveList n R = solveRational n R.toFinset := by
  induction n with
  | zero => simp only [solveList, solveRational, List.mem_toFinset]
  | succ n ih =>
    simp only [solveList, solveRational, ih, projectList_toFinset]

theorem solveList_sound {n : ℕ} (R : List (Row n)) (q : Fin n → ℚ)
    (h : solveList n R = some q) : ∀ r ∈ R, r.Holds q := by
  rw [solveList_eq_solveRational] at h
  simpa only [List.mem_toFinset] using solveRational_sound R.toFinset q h

theorem solveList_complete (n : ℕ) (R : List (Row n)) :
    (∃ q, solveList n R = some q) ↔ Feasible ℝ R.toFinset := by
  rw [solveList_eq_solveRational, solveRational_complete]

theorem solveList_none_iff (n : ℕ) (R : List (Row n)) :
    solveList n R = none ↔ ¬ Feasible ℝ R.toFinset := by
  rw [solveList_eq_solveRational, solveRational_none_iff]

#print axioms boundsWitness_spec
#print axioms liftWitness_correct
#print axioms checkRationalWitness_correct
#print axioms solveRational_isSome
#print axioms solveRational_sound
#print axioms rationalWitness_real
#print axioms solveRational_complete
#print axioms solveRational_none_iff
#print axioms solveRational_checked
#print axioms projectList_toFinset
#print axioms solveList_eq_solveRational
#print axioms solveList_sound
#print axioms solveList_complete
#print axioms solveList_none_iff

end UnifiedLean.G6.RationalAffineWitness
