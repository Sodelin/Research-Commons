import BinaryPhysicalGame

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY UNELABORATED CANDIDATE. No execution.

The actual lower-family DAGs, not a detached one-hot oracle. Available
targets are roots with arrows to EVERY untargeted observed vertex.
Each rival orders the latter as S,a,b,R and deletes only a -> b.
Classical unseen-separator lower-bound attribution: Zhang--Shiragur--Uhler
and Franquesa Mones--Zhang--Uhler; the informative-root extension is the
separately hand-reviewed restricted-intervention construction.
-/

namespace RestrictedCausal.HardFamily

open SelectedWalk CanonicalSelection LatentRoots OriginalProjection
open InducingSeparation FiniteTargetImage GraphEquivalence

abbrev Labels (k u : Nat) := Sum (Fin k) (Fin u)

def Available {k u : Nat} : Labels k u → Prop
  | .inl _ => True
  | .inr _ => False

abbrev Index (u : Nat) :=
  Σ p : OrderedPair (Fin u), ({x : Fin u // x ≠ p.val.1 ∧ x ≠ p.val.2} → Bool)

namespace Index

variable {u : Nat}

def «first» (q : Index u) : Fin u := q.1.val.1
def second (q : Index u) : Fin u := q.1.val.2

theorem distinct (q : Index u) : q.first ≠ q.second := ne_of_lt q.1.property

def before (q : Index u) (x : Fin u) : Bool :=
  if h : x ≠ q.first ∧ x ≠ q.second then q.2 ⟨x, h⟩ else false

theorem before_first (q : Index u) : q.before q.first = false := by simp [before]
theorem before_second (q : Index u) : q.before q.second = false := by simp [before]

theorem before_excludes (q : Index u) {x : Fin u} (h : q.before x = true) :
    x ≠ q.first ∧ x ≠ q.second := by
  constructor
  · intro same; subst x; rw [before_first] at h; cases h
  · intro same; subst x; rw [before_second] at h; cases h

def stage (q : Index u) (x : Fin u) : Nat :=
  if q.before x = true then 0 else if x = q.first then 1 else if x = q.second then 2 else 3

def key (q : Index u) (x : Fin u) : Nat := q.stage x * (u + 1) + x.val

theorem key_first (q : Index u) : q.key q.first = u + 1 + q.first.val := by
  simp [key, stage, before_first]

theorem key_second (q : Index u) : q.key q.second = 2 * (u + 1) + q.second.val := by
  simp [key, stage, before_second, q.distinct.symm]

theorem key_injective (q : Index u) : Function.Injective q.key := by
  intro x y same
  apply Fin.ext
  have moduli := congrArg (fun n => n % (u + 1)) same
  have hx : x.val < u + 1 := by omega
  have hy : y.val < u + 1 := by omega
  simpa only [key, Nat.add_mod, Nat.mul_mod, Nat.mod_self, Nat.mul_zero,
    Nat.zero_add, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] using moduli

theorem first_before_second (q : Index u) : q.key q.first < q.key q.second := by
  rw [key_first, key_second]
  have ha := q.first.isLt
  have hb := q.second.isLt
  omega

theorem key_lt_first (q : Index u) (x : Fin u) :
    q.key x < q.key q.first ↔ q.before x = true := by
  rw [key_first]
  have hx := x.isLt
  have ha := q.first.isLt
  by_cases hS : q.before x = true
  · simp only [key, stage, if_pos hS, Nat.zero_mul, Nat.zero_add]
    exact ⟨fun _ => hS, fun _ => by omega⟩
  · by_cases hA : x = q.first
    · subst x; simp [key, stage, before_first]
    · by_cases hB : x = q.second
      · subst x
        rw [key_second]
        constructor
        · intro «impossible»; omega
        · intro «impossible»; exact (hS «impossible»).elim
      · simp only [key, stage, if_neg hS, if_neg hA, if_neg hB]
        constructor
        · intro «impossible»; omega
        · intro «impossible»; exact (hS «impossible»).elim

theorem key_lt_second (q : Index u) (x : Fin u) :
    q.key x < q.key q.second ↔ q.before x = true ∨ x = q.first := by
  rw [key_second]
  have hx := x.isLt
  have hb := q.second.isLt
  by_cases hS : q.before x = true
  · simp only [key, stage, if_pos hS, Nat.zero_mul, Nat.zero_add]
    exact ⟨fun _ => Or.inl hS, fun _ => by omega⟩
  · by_cases hA : x = q.first
    · subst x
      rw [key_first]
      exact ⟨fun _ => Or.inr rfl, fun _ => by have ha := q.first.isLt; omega⟩
    · by_cases hB : x = q.second
      · subst x
        rw [key_second]
        simp only [lt_self_iff_false, hS, hA, false_or]
      · simp only [key, stage, if_neg hS, if_neg hA, if_neg hB]
        constructor
        · intro «impossible»; omega
        · rintro («impossible» | «impossible»)
          · exact (hS «impossible»).elim
          · exact (hA «impossible»).elim

theorem first_to_remainder (q : Index u) (x : Fin u)
    (hS : ¬ q.before x = true) (hA : x ≠ q.first) (hB : x ≠ q.second) :
    q.key q.first < q.key x ∧ q.key q.second < q.key x := by
  rw [key_first, key_second]
  simp only [key, stage, if_neg hS, if_neg hA, if_neg hB]
  have ha := q.first.isLt
  have hb := q.second.isLt
  omega

theorem predecessor_of_before (q : Index u) (x y : Fin u)
    (hy : q.before y = true) (edge : q.key x < q.key y) : q.before x = true := by
  by_contra hx
  have hyBound := y.isLt
  simp only [key, stage, if_pos hy] at edge
  by_cases hA : x = q.first
  · subst x
    simp only [before_first, Bool.false_eq_true, if_false, if_pos rfl] at edge
    omega
  · by_cases hB : x = q.second
    · simp only [if_neg hx, if_neg hA, if_pos hB] at edge
      omega
    · simp only [if_neg hx, if_neg hA, if_neg hB] at edge
      omega

end Index

def insideArrow {u : Nat} (source : Option (Index u)) (x y : Fin u) : Prop :=
  match source with
  | none => x < y
  | some q => q.key x < q.key y ∧ ¬ (x = q.first ∧ y = q.second)

def arrow {k u : Nat} (source : Option (Index u)) : Labels k u → Labels k u → Prop
  | .inl _, .inr _ => True
  | .inr x, .inr y => insideArrow source x y
  | _, .inl _ => False

def rank {k u : Nat} (source : Option (Index u)) : Labels k u → Nat
  | .inl _ => 0
  | .inr x => 1 + match source with | none => x.val | some q => q.key x

theorem arrow_rank_strict {k u : Nat} (source : Option (Index u)) {x y : Labels k u}
    (edge : arrow source x y) : rank source x < rank source y := by
  cases x with
  | inl t => cases y with
    | inl s => exact edge.elim
    | inr y => simp only [rank]; omega
  | inr x => cases y with
    | inl t => exact edge.elim
    | inr y =>
        cases source with
        | none => change x.val < y.val at edge; change 1 + x.val < 1 + y.val; omega
        | some q => change q.key x < q.key y ∧ _ at edge
                    change 1 + q.key x < 1 + q.key y; omega

theorem route_rank_mono {V : Type*} (D : V → V → Prop) (r : V → Nat)
    (strict : ∀ a b, D a b → r a < r b) {a b : V} {xs : List V}
    (route : Route D a xs b) : r a ≤ r b := by
  induction route with
  | nil a => exact Nat.le_refl _
  | cons edge tail ih => exact Nat.le_trans (strict _ _ edge).le ih

theorem arrow_acyclic {k u : Nat} (source : Option (Index u))
    (a : Labels k u) (xs : List (Labels k u)) (route : Route (arrow source) a xs a) : xs = [] := by
  cases route with
  | nil => rfl
  | cons edge tail =>
      have strict := arrow_rank_strict source edge
      have mono := route_rank_mono (arrow source) (rank source) (fun _ _ => arrow_rank_strict source) tail
      omega

theorem target_has_no_parent {k u : Nat} (source : Option (Index u))
    (t : Fin k) (v : Labels k u) : ¬ arrow source v (.inl t) := by cases v <;> exact id

theorem targets_cause_all {k u : Nat} (source : Option (Index u)) (t : Fin k) (x : Fin u) :
    arrow source (.inl t : Labels k u) (.inr x) := True.intro

theorem rival_parent_first {u : Nat} (q : Index u) (x : Fin u) :
    insideArrow (some q) x q.first ↔ q.before x = true := by
  change (q.key x < q.key q.first ∧ ¬ (x = q.first ∧ q.first = q.second)) ↔ _
  simp only [q.distinct, and_false, not_false_eq_true, and_true, q.key_lt_first]

theorem rival_parent_second {u : Nat} (q : Index u) (x : Fin u) :
    insideArrow (some q) x q.second ↔ q.before x = true := by
  change (q.key x < q.key q.second ∧ ¬ (x = q.first ∧ q.second = q.second)) ↔ _
  rw [q.key_lt_second]
  constructor
  · rintro ⟨inS | atA, notMissing⟩
    · exact inS
    · exact (notMissing ⟨atA, rfl⟩).elim
  · intro inS
    exact ⟨Or.inl inS, fun h => (q.before_excludes inS).1 h.1⟩

theorem rival_endpoints_to_remainder {k u : Nat} (q : Index u) (x : Fin u)
    (hS : ¬ q.before x = true) (hA : x ≠ q.first) (hB : x ≠ q.second) :
    arrow (some q) (.inr q.first : Labels k u) (.inr x) ∧
      arrow (some q) (.inr q.second : Labels k u) (.inr x) := by
  have «order» := q.first_to_remainder x hS hA hB
  exact ⟨⟨«order».1, fun h => hB h.2⟩, ⟨«order».2, fun h => q.distinct h.1.symm⟩⟩

theorem inside_adjacent_except {u : Nat} (source : Option (Index u)) (x y : Fin u)
    (different : x ≠ y)
    (notMissing : ∀ q, source = some q →
      ¬ (x = q.first ∧ y = q.second) ∧ ¬ (y = q.first ∧ x = q.second)) :
    insideArrow source x y ∨ insideArrow source y x := by
  cases source with
  | none => exact lt_or_gt_of_ne different
  | some q =>
      have unequal : q.key x ≠ q.key y := fun h => different (q.key_injective h)
      rcases lt_or_gt_of_ne unequal with forward | backward
      · exact Or.inl ⟨forward, (notMissing q rfl).1⟩
      · exact Or.inr ⟨backward, (notMissing q rfl).2⟩

end RestrictedCausal.HardFamily
