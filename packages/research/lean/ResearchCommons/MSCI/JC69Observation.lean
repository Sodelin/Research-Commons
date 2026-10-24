import ResearchCommons.MSCI.JC69Tree

/-! Original-label probability receiver for the constructed SAME-tree channel.
It reuses the retained original Valid/TimedBound source interfaces. No new
source/tree/clock factory, unranked quotient, or measure-mixing premise is
silently supplied. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69Observation
open GProgram.SourceForest
open GProgram.G2.FaithfulPairAgeDecoration GProgram.G2.ChronologicalDecoration
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69Tree
open scoped Classical BigOperators
variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]

/-- Exactly the original full copy vector, rather than an extra occurrence
observation. The complete source's ONE live root supplies the cover below. -/
def originalPatternEquiv (t : Genealogy Copy) (ht : t.WellLabelled)
    (hc : t.leaves = Finset.univ) : Pattern t ≃ (Copy → Base) where
  toFun := patternLabels t
  invFun := labelPattern t
  left_inv := label_pattern_pattern_labels t ht
  right_inv := by
    intro p
    funext c
    exact pattern_labels_label_pattern t p c (by rw [hc]; exact Finset.mem_univ c)

/-- This proves the actual normalized PMF point probability at each ORIGINAL
label vector from the SAME decoded source matrix. It is not a desired-law
premise or a claim that an arbitrary supplied tree is a physical source. -/
theorem actual_original_label_probability {V E : Type*}
    (s : State V E Copy) (hs : Valid s) (hcard : s.live.card ≤ 1)
    (leafAge : Copy → ℝ) (M : Copy → Copy → ℝ) (bound : ℝ)
    (hm : TimedBound leafAge M s bound) (l : Copy) (hl : l ∈ s.live)
    (p : Copy → Base) :
    (actualLabelledTreeKernel s hs leafAge M bound hm l hl p).toReal =
      rootLikelihood (s.genealogy l)
        (clockSurvivals leafAge _ (decode M _)) (labelPattern (s.genealogy l) p) := by
  let t := s.genealogy l
  have hc : t.leaves = Finset.univ := actual_single_root_covers_original_copies s hs hcard l hl
  have he : ∀ a : Pattern t, p = patternLabels t a ↔ a = labelPattern t p := by
    intro a
    constructor
    · intro h
      have hh := congrArg (labelPattern t) h
      rw [label_pattern_pattern_labels t (hs.wellLabelled l hl)] at hh
      exact hh.symm
    · intro h
      subst a
      apply funext
      intro c
      exact (pattern_labels_label_pattern t p c (by rw [hc]; exact Finset.mem_univ c)).symm
  have hmap :
      actualLabelledTreeKernel s hs leafAge M bound hm l hl p =
        actualTreeKernel s hs leafAge M bound hm l hl (labelPattern t p) := by
    unfold actualLabelledTreeKernel
    rw [PMF.map_apply, tsum_fintype]
    change (∑ a : Pattern t, if p = patternLabels t a then
      actualTreeKernel s hs leafAge M bound hm l hl a else 0) = _
    calc
      _ = if p = patternLabels t (labelPattern t p) then
          actualTreeKernel s hs leafAge M bound hm l hl (labelPattern t p) else 0 :=
        Finset.sum_eq_single (labelPattern t p)
          (fun b _ hb => by
            rw [if_neg (fun h => hb ((he b).mp h))])
          (fun h => False.elim (h (Finset.mem_univ _)))
      _ = _ := if_pos ((he _).mpr rfl)
  rw [hmap]
  exact actual_tree_kernel_probability s hs leafAge M bound hm l hl _


/-- Fourier output on exactly the original full copy vector. The inverse
fibre is derived from valid full-source support, not assumed as a readout law.
The root/tree/clock bank is the SAME one used in the point probability. -/
theorem actual_original_label_fourier {V E : Type*}
    (s : State V E Copy) (hs : Valid s) (hcard : s.live.card ≤ 1)
    (leafAge : Copy → ℝ) (M : Copy → Copy → ℝ) (bound : ℝ)
    (hm : TimedBound leafAge M s bound) (l : Copy) (hl : l ∈ s.live)
    (charges : Copy → Base) :
    (∑ p : Copy → Base, (actualLabelledTreeKernel s hs leafAge M bound hm l hl p).toReal *
      ∏ c : Copy, character (charges c) (p c)) =
      if totalCharge charges (s.genealogy l) = 0 then
        amplitude charges (s.genealogy l)
          (clockSurvivals leafAge _ (decode M _)) else 0 := by
  let t := s.genealogy l
  let x := clockSurvivals leafAge t (decode M t)
  have ht : t.WellLabelled := hs.wellLabelled l hl
  have hc : t.leaves = Finset.univ :=
    actual_single_root_covers_original_copies s hs hcard l hl
  have he := Fintype.sum_equiv (originalPatternEquiv t ht hc)
    (fun q : Pattern t => rootLikelihood t x q * patternCharacter charges t q)
    (fun p : Copy → Base =>
      (actualLabelledTreeKernel s hs leafAge M bound hm l hl p).toReal *
        ∏ c : Copy, character (charges c) (p c))
    (by
      intro q
      rw [actual_original_label_probability s hs hcard leafAge M bound hm l hl]
      change rootLikelihood t x q * patternCharacter charges t q =
        rootLikelihood t x (labelPattern t (patternLabels t q)) *
          ∏ c : Copy, character (charges c) (patternLabels t q c)
      rw [label_pattern_pattern_labels t ht]
      have hh := label_pattern_character charges (patternLabels t q) t ht
      rw [label_pattern_pattern_labels t ht, hc] at hh
      rw [hh])
  rw [← he]
  exact root_fourier t x charges

end ResearchCommons.MSCI.JC69Observation
