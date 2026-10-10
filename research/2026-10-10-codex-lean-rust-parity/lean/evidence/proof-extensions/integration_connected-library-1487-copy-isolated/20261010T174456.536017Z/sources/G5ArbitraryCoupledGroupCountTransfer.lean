import G5GroupRelabeling

/-!
# Coupled quartet witnesses for arbitrary shared original group IDs
Contributor: dot / OpenAI, 2026-10-03.
The SAME group selector is used for repeated quartet labels. All fifteen
original-label grouping patterns are handled by equality cases, without adding
diagonal observations or independent replicas of one original group.
This is a kernel theorem; source-current-selector binding is a separate port.
-/
namespace GProgram.G5.QuartetKernel
open scoped Classical
variable {G α β : Type*} [DecidableEq G] [DecidableEq α] [DecidableEq β]

def arbitraryCoupledWitness (pos : G → Fin 2 → α) (owner : Fin 4 → G) : Prop :=
  ∃ choice : G → Fin 2, quartetAt (fun i => pos (owner i) (choice (owner i)))

lemma arbitrary_coupled_reindex {r : Nat} (pos : G → Fin 2 → α) (e : Fin r → G)
    (he : Function.Injective e) (owner : Fin 4 → Fin r) :
    arbitraryCoupledWitness pos (e ∘ owner) ↔ coupledQuartetWitness (fun i => pos (e i)) owner := by
  constructor
  · rintro ⟨choice,h⟩
    exact ⟨choice ∘ e,h⟩
  · rintro ⟨choice,h⟩
    refine ⟨Function.extend e choice (fun _ => 0),?_⟩
    simpa only [quartetAt,groupSelected,Function.comp_apply,he.extend_apply] using h

lemma arbitrary_cross_group_blocks (pos : G → Fin 2 → α) (owner : Fin 4 → G)
    (h : owner 0 = owner 2 ∨ owner 0 = owner 3 ∨ owner 1 = owner 2 ∨ owner 1 = owner 3) :
    ¬arbitraryCoupledWitness pos owner := by
  rintro ⟨choice,hw⟩
  simp only [quartetAt] at hw
  rcases h with h | h | h | h <;> rcases hw with hw | hw <;> grind

lemma arbitrary_injective_iff_selector (pos : G → Fin 2 → α) (owner : Fin 4 → G)
    (ho : Function.Injective owner) :
    arbitraryCoupledWitness pos owner ↔ selectorWitness (fun i => pos (owner i)) := by
  have he := arbitrary_coupled_reindex pos owner ho (id : Fin 4 → Fin 4)
  simpa only [Function.comp_id,four_coupled_iff_selectorWitness] using he

lemma arbitrary_two_iff_count (pos : G → Fin 2 → α) (owner : Fin 4 → G)
    (h01 : owner 0 = owner 1) (h23 : owner 2 = owner 3) (h02 : owner 0 ≠ owner 2) :
    arbitraryCoupledWitness pos owner ↔ pairCount (pos (owner 0)) (pos (owner 2)) < 4 := by
  let e : Fin 2 → G := ![owner 0,owner 2]
  have he : Function.Injective e := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [e]
  have howner : owner = e ∘ ownersTwo := by
    funext i
    fin_cases i <;> simp [e,ownersTwo,h01,h23]
  rw [howner,arbitrary_coupled_reindex pos e he ownersTwo,two_coupled_iff_count_lt_four]
  rfl

lemma arbitrary_three_iff_three (pos : G → Fin 2 → α) (owner : Fin 4 → G)
    (h01 : owner 0 = owner 1) (h02 : owner 0 ≠ owner 2) (h03 : owner 0 ≠ owner 3)
    (h23 : owner 2 ≠ owner 3) :
    arbitraryCoupledWitness pos owner ↔ threeGroupWitness (pos (owner 0)) (pos (owner 2)) (pos (owner 3)) := by
  let e : Fin 3 → G := ![owner 0,owner 2,owner 3]
  have he : Function.Injective e := by
    intro i j h
    fin_cases i <;> fin_cases j <;> simp_all [e]
  have howner : owner = e ∘ ownersThree := by
    funext i
    fin_cases i <;> simp [e,ownersThree,h01]
  rw [howner,arbitrary_coupled_reindex pos e he ownersThree,three_coupled_iff_threeGroupWitness]
  rfl

lemma arbitrary_swap_sides (pos : G → Fin 2 → α) (owner : Fin 4 → G) :
    arbitraryCoupledWitness pos owner ↔ arbitraryCoupledWitness pos ![owner 2,owner 3,owner 0,owner 1] := by
  unfold arbitraryCoupledWitness
  apply exists_congr
  intro choice
  simp only [quartetAt,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two,Matrix.cons_val_three]
  exact or_comm

/-- The existing coupled one/two/three/four-group kernels cover arbitrary
original group maps. Only DISTINCT GROUP pair counts are used. -/
theorem arbitrary_coupled_witness_iff_of_distinct_group_counts
    (pos : G → Fin 2 → α) (pos₂ : G → Fin 2 → β) (owner : Fin 4 → G)
    (hcounts : ∀ g h : G, g ≠ h → pairCount (pos g) (pos h) = pairCount (pos₂ g) (pos₂ h)) :
    arbitraryCoupledWitness pos owner ↔ arbitraryCoupledWitness pos₂ owner := by
  by_cases hc : owner 0 = owner 2 ∨ owner 0 = owner 3 ∨ owner 1 = owner 2 ∨ owner 1 = owner 3
  · exact iff_of_false (arbitrary_cross_group_blocks pos owner hc) (arbitrary_cross_group_blocks pos₂ owner hc)
  · have h02 : owner 0 ≠ owner 2 := fun h => hc (Or.inl h)
    have h03 : owner 0 ≠ owner 3 := fun h => hc (Or.inr (Or.inl h))
    have h12 : owner 1 ≠ owner 2 := fun h => hc (Or.inr (Or.inr (Or.inl h)))
    have h13 : owner 1 ≠ owner 3 := fun h => hc (Or.inr (Or.inr (Or.inr h)))
    by_cases h01 : owner 0 = owner 1
    · by_cases h23 : owner 2 = owner 3
      · rw [arbitrary_two_iff_count pos owner h01 h23 h02,
          arbitrary_two_iff_count pos₂ owner h01 h23 h02,hcounts _ _ h02]
      · rw [arbitrary_three_iff_three pos owner h01 h02 h03 h23,
          arbitrary_three_iff_three pos₂ owner h01 h02 h03 h23]
        apply not_iff_not.mp
        rw [threeGroup_absence_iff,threeGroup_absence_iff]
        simp only [hcounts _ _ h02,hcounts _ _ h03,hcounts _ _ h23]
    · by_cases h23 : owner 2 = owner 3
      · let swapped : Fin 4 → G := ![owner 2,owner 3,owner 0,owner 1]
        rw [arbitrary_swap_sides pos owner,arbitrary_swap_sides pos₂ owner]
        have hs01 : swapped 0 = swapped 1 := by simpa [swapped] using h23
        have hs02 : swapped 0 ≠ swapped 2 := by simpa [swapped] using h02.symm
        have hs03 : swapped 0 ≠ swapped 3 := by simpa [swapped] using h12.symm
        have hs23 : swapped 2 ≠ swapped 3 := by simpa [swapped] using h01
        rw [arbitrary_three_iff_three pos swapped hs01 hs02 hs03 hs23,
          arbitrary_three_iff_three pos₂ swapped hs01 hs02 hs03 hs23]
        apply not_iff_not.mp
        rw [threeGroup_absence_iff,threeGroup_absence_iff]
        simp only [hcounts _ _ hs02,hcounts _ _ hs03,hcounts _ _ hs23]
      · have hi : Function.Injective owner := by
          intro i j h
          fin_cases i <;> fin_cases j <;> grind
        rw [arbitrary_injective_iff_selector pos owner hi,arbitrary_injective_iff_selector pos₂ owner hi]
        apply selectorWitness_iff_of_six_distinct_counts
        intro i j hij
        exact hcounts _ _ (fun he => hij (hi he))

#print axioms arbitrary_coupled_witness_iff_of_distinct_group_counts
end GProgram.G5.QuartetKernel
