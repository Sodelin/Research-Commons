import ResearchCommons.MSCI.JC69Observation
import Mathlib.MeasureTheory.Group.Arithmetic

/-! Measurable probabilities of the SAME original timed-tree channel.
Recursive real decorations retain G2's canonical product measurable spaces;
original matrix coordinates retain their ordinary real Borel spaces.
No discrete topology on ages, new source factory, or desired mixing law.
-/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69Measurable
open GProgram.SourceForest
open GProgram.G2.FaithfulPairAgeDecoration GProgram.G2.ChronologicalDecoration
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69Tree
open ResearchCommons.MSCI.JC69Observation
open scoped BigOperators NNReal Classical
variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]

theorem root_age_measurable (leafAge : Copy → ℝ) (t : Genealogy Copy) :
    Measurable (fun d : Decoration t => rootAge leafAge t d) := by
  cases t with
  | leaf c => exact measurable_const
  | graft a b =>
      simpa only [rootAge, Decoration, decorationMeasurable] using
        (measurable_fst : Measurable (fun d : ℝ × Decoration a × Decoration b => d.1))

private theorem branch_probability_measurable {A : Type*} [MeasurableSpace A]
    (x : A → ℝ) (hx : Measurable x) (a b : Base) :
    Measurable (fun z => probability (x z) a b) := by
  by_cases h : a = b
  · simp only [probability, if_pos h]
    fun_prop
  · simp only [probability, if_neg h]
    fun_prop

theorem clock_likelihood_measurable (leafAge : Copy → ℝ) (t : Genealogy Copy)
    (a : Base) (p : Pattern t) :
    Measurable (fun d : Decoration t =>
      likelihood t (clockSurvivals leafAge t d) a p) := by
  induction t generalizing a with
  | leaf c => exact measurable_const
  | graft l r hl hr =>
      have hleft : Measurable (fun d : ℝ × Decoration l × Decoration r => d.2.1) :=
        measurable_snd.fst
      have hright : Measurable (fun d : ℝ × Decoration l × Decoration r => d.2.2) :=
        measurable_snd.snd
      have hleftAge := (root_age_measurable leafAge l).comp hleft
      have hrightAge := (root_age_measurable leafAge r).comp hright
      have hleftX : Measurable (fun d : ℝ × Decoration l × Decoration r =>
          Real.exp (-((4/3 : ℝ) * (d.1 - rootAge leafAge l d.2.1)))) :=
        Real.continuous_exp.measurable.comp
          ((measurable_const.mul (measurable_fst.sub hleftAge)).neg)
      have hrightX : Measurable (fun d : ℝ × Decoration l × Decoration r =>
          Real.exp (-((4/3 : ℝ) * (d.1 - rootAge leafAge r d.2.2)))) :=
        Real.continuous_exp.measurable.comp
          ((measurable_const.mul (measurable_fst.sub hrightAge)).neg)
      have hL : Measurable (fun d : ℝ × Decoration l × Decoration r =>
          ∑ b : Base, probability
            (Real.exp (-((4/3 : ℝ) * (d.1 - rootAge leafAge l d.2.1)))) a b *
              likelihood l (clockSurvivals leafAge l d.2.1) b p.1) :=
        Finset.measurable_sum Finset.univ (fun b _ =>
          (branch_probability_measurable _ hleftX a b).mul ((hl b p.1).comp hleft))
      have hR : Measurable (fun d : ℝ × Decoration l × Decoration r =>
          ∑ b : Base, probability
            (Real.exp (-((4/3 : ℝ) * (d.1 - rootAge leafAge r d.2.2)))) a b *
              likelihood r (clockSurvivals leafAge r d.2.2) b p.2) :=
        Finset.measurable_sum Finset.univ (fun b _ =>
          (branch_probability_measurable _ hrightX a b).mul ((hr b p.2).comp hright))
      simpa only [Decoration, decorationMeasurable, clockSurvivals, likelihood] using hL.mul hR

theorem root_probability_measurable (leafAge : Copy → ℝ) (t : Genealogy Copy)
    (p : Pattern t) :
    Measurable (fun d : Decoration t =>
      rootLikelihood t (clockSurvivals leafAge t d) p) := by
  exact Finset.measurable_sum Finset.univ (fun a _ =>
    measurable_const.mul (clock_likelihood_measurable leafAge t a p))

/-- The matrix is the actual G2 pair-age coordinate, not a separately fitted
edge bank. The theorem holds as a measurable real function even outside the
admitted matrix set; actual probability claims use original TimedBound. -/
theorem decoded_probability_measurable (leafAge : Copy → ℝ) (t : Genealogy Copy)
    (p : Pattern t) :
    Measurable (fun M : Copy → Copy → ℝ =>
      rootLikelihood t (clockSurvivals leafAge t (decode M t)) p) :=
  (root_probability_measurable leafAge t p).comp (decode_measurable t)

/-- Finite sites share the SAME random genealogy and complete matrix.
This is a product inside the conditional kernel, before source integration. -/
theorem decoded_locus_measurable (L : Nat) (leafAge : Copy → ℝ)
    (t : Genealogy Copy) (p : Fin L → Pattern t) :
    Measurable (fun M : Copy → Copy → ℝ =>
      locusLikelihood L t (clockSurvivals leafAge t (decode M t)) p) :=
  Finset.measurable_prod Finset.univ (fun j _ =>
    decoded_probability_measurable leafAge t (p j))

/-- Actual original-copy PMF coordinates are measurable on their existing
admitted SAME-matrix carrier. The chosen bound is only proof data for the
existing TimedBound; it changes neither matrix, tree nor branch rates. This
does not construct the actual source measure or descend to its unranked output. -/
theorem actual_original_probability_measurable {V E : Type*}
    (s : State V E Copy) (hs : Valid s) (hcard : s.live.card ≤ 1)
    (leafAge : Copy → ℝ) (l : Copy) (hl : l ∈ s.live) (p : Copy → Base) :
    Measurable (fun z : {M : Copy → Copy → ℝ // ∃ b : ℝ, TimedBound leafAge M s b} =>
      (actualLabelledTreeKernel s hs leafAge z.val z.property.choose
        z.property.choose_spec l hl p).toReal) := by
  have he :
      (fun z : {M : Copy → Copy → ℝ // ∃ b : ℝ, TimedBound leafAge M s b} =>
        (actualLabelledTreeKernel s hs leafAge z.val z.property.choose
          z.property.choose_spec l hl p).toReal) =
      (fun z : {M : Copy → Copy → ℝ // ∃ b : ℝ, TimedBound leafAge M s b} =>
        rootLikelihood (s.genealogy l)
          (clockSurvivals leafAge _ (decode z.val _)) (labelPattern (s.genealogy l) p)) := by
    funext z
    exact actual_original_label_probability s hs hcard leafAge z.val z.property.choose
      z.property.choose_spec l hl p
  rw [he]
  exact (decoded_probability_measurable leafAge (s.genealogy l)
    (labelPattern (s.genealogy l) p)).comp measurable_subtype_coe

end ResearchCommons.MSCI.JC69Measurable
