import Std

namespace SocialScience.Learning

/-- Exact consistency with a finite list of labeled observations. -/
def Fits {X Y : Type} (hypothesis : X → Y) (evidence : List (X × Y)) : Prop :=
  ∀ item, item ∈ evidence → hypothesis item.1 = item.2

theorem fits_empty {X Y : Type} (hypothesis : X → Y) : Fits hypothesis [] := by
  intro item h
  simp at h

theorem fits_cons_iff {X Y : Type} (hypothesis : X → Y) (x : X) (y : Y)
    (evidence : List (X × Y)) :
    Fits hypothesis ((x, y) :: evidence) ↔ hypothesis x = y ∧ Fits hypothesis evidence := by
  constructor
  · intro h
    constructor
    · exact h (x, y) (by simp)
    · intro item member
      exact h item (by simp [member])
  · rintro ⟨atNew, atOld⟩ item member
    simp only [List.mem_cons] at member
    rcases member with same | old
    · subst item
      exact atNew
    · exact atOld item old

theorem fits_append_iff {X Y : Type} (hypothesis : X → Y)
    (first second : List (X × Y)) :
    Fits hypothesis (first ++ second) ↔ Fits hypothesis first ∧ Fits hypothesis second := by
  constructor
  · intro h
    constructor
    · intro item member
      exact h item (List.mem_append.mpr (Or.inl member))
    · intro item member
      exact h item (List.mem_append.mpr (Or.inr member))
  · rintro ⟨hfirst, hsecond⟩ item member
    rcases List.mem_append.mp member with hf | hs
    · exact hfirst item hf
    · exact hsecond item hs

theorem more_evidence_narrows_models {X Y : Type} (hypothesis : X → Y)
    {small large : List (X × Y)} (included : ∀ item, item ∈ small → item ∈ large)
    (fitsLarge : Fits hypothesis large) : Fits hypothesis small :=
  fun item member => fitsLarge item (included item member)

theorem truth_survives_correct_label {X Y : Type} (truth : X → Y)
    (evidence : List (X × Y)) (x : X) (fits : Fits truth evidence) :
    Fits truth ((x, truth x) :: evidence) :=
  (fits_cons_iff truth x (truth x) evidence).mpr ⟨rfl, fits⟩

theorem distinguishing_query_eliminates_rival {X Y : Type} (truth rival : X → Y)
    (evidence : List (X × Y)) (x : X) (different : rival x ≠ truth x) :
    ¬ Fits rival ((x, truth x) :: evidence) := by
  intro fits
  exact different ((fits_cons_iff rival x (truth x) evidence).mp fits).1

theorem conflicting_labels_impossible {X Y : Type} (hypothesis : X → Y)
    (evidence : List (X × Y)) (x : X) (a b : Y)
    (first : (x, a) ∈ evidence) (second : (x, b) ∈ evidence) (different : a ≠ b) :
    ¬ Fits hypothesis evidence := by
  intro fits
  exact different ((fits (x, a) first).symm.trans (fits (x, b) second))

theorem incorrect_label_excludes_truth {X Y : Type} (truth : X → Y)
    (evidence : List (X × Y)) (x : X) (label : Y) (wrong : truth x ≠ label) :
    ¬ Fits truth ((x, label) :: evidence) := by
  intro fits
  exact wrong ((fits_cons_iff truth x label evidence).mp fits).1

/-- Duplicating the same list changes no exact-consistency constraint. -/
theorem duplicate_evidence_same_models {X Y : Type} (hypothesis : X → Y)
    (evidence : List (X × Y)) :
    Fits hypothesis (evidence ++ evidence) ↔ Fits hypothesis evidence := by
  rw [fits_append_iff]
  exact ⟨fun h => h.1, fun h => ⟨h, h⟩⟩

end SocialScience.Learning
