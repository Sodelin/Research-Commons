import G2ActualDecorationFold

/-!
# Genuine measurability of the original decoration fold

Contributor: dot (OpenAI), 7 October 2026. New reconstruction of the missing
legacy interface. The accepted faithful decoder removes existential real
age decorations on valid source forests. Real ages and matrices retain their
usual product measurable spaces; only the already finite source Code is
discrete. The original fold, source compiler and preserved consumers are
unchanged. No probability, successful-trace or chronology premise is used.
-/

namespace GProgram.G2.DecorationMeasurability
set_option backward.isDefEq.respectTransparency false
open MeasureTheory GProgram.SourceForest Nanuq.Source
open GProgram.G2.FaithfulPairAgeDecoration GProgram.G2.SourceGraftDecoration
open GProgram.G2.ActualDecorationFold GProgram.G2.LiteralMarkedClockTrace
open UnifiedLean.Source.UniformizedSourceStep
open scoped Classical

variable {V E Copy X : Type*}
variable [DecidableEq Copy] [Fintype Copy]

/-- The supplied matrix itself selects the only possible decoration of each
live well-labelled genealogy through the accepted faithful decoder. This
predicate is defined for every fixed forest, without a validity premise. -/
noncomputable def CanonicalDecorates (leafAge : Copy → ℝ)
    (M : Copy → Copy → ℝ) (s : State V E Copy) : Prop :=
  ∀ l ∈ s.live, ∀ x ∈ (s.genealogy l).leaves,
    ∀ y ∈ (s.genealogy l).leaves,
      M x y = pairAge leafAge (s.genealogy l)
        (decode M (s.genealogy l)) x y

lemma forest_decorates_iff_canonical (leafAge : Copy → ℝ)
    (M : Copy → Copy → ℝ) (s : State V E Copy) (hs : Valid s) :
    ForestDecorates leafAge M s ↔ CanonicalDecorates leafAge M s := by
  constructor
  · intro h l hl
    obtain ⟨d,hd⟩ := h l hl
    have he := decode_of_pair_agreement leafAge (s.genealogy l)
      (hs.wellLabelled l hl) d M hd
    simpa only [he] using hd
  · intro h l hl
    exact ⟨decode M (s.genealogy l),h l hl⟩

lemma canonical_decorates_measurable (leafAge : Copy → ℝ)
    (s : State V E Copy) :
    Measurable (fun M : Copy → Copy → ℝ => CanonicalDecorates leafAge M s) := by
  apply Measurable.forall
  intro l
  apply Measurable.imp measurable_const
  apply Measurable.forall
  intro x
  apply Measurable.imp measurable_const
  apply Measurable.forall
  intro y
  apply Measurable.imp measurable_const
  exact (measurableSet_eq_fun
    ((measurable_pi_apply y).comp (measurable_pi_apply x))
    ((pairAge_measurable leafAge (s.genealogy l) x y).comp
      (decode_measurable (s.genealogy l)))).mem

variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- Joint measurability of the same destination-based age update. The finite
codes may be fixed in turn; every remaining coordinate is either the supplied
real age or the corresponding original matrix entry. -/
lemma coded_age_update_joint_measurable (N : RootedBinary V E X)
    {sample : Copy → X} :
    Measurable (fun z : Code N sample ×
        (Code N sample × (ℝ × (Copy → Copy → ℝ))) =>
      codedAgeUpdate N z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  apply measurable_from_prod_countable_right
  intro s
  apply measurable_from_prod_countable_right
  intro d
  apply measurable_pi_lambda
  intro x
  apply measurable_pi_lambda
  intro y
  by_cases h : (state s).ancestor x ≠ (state s).ancestor y ∧
      (state d).ancestor x = (state d).ancestor y
  · simpa only [codedAgeUpdate,if_pos h] using
      (measurable_fst : Measurable (fun z : ℝ × (Copy → Copy → ℝ) => z.1))
  · simpa only [codedAgeUpdate,if_neg h,Function.comp_def] using
      (measurable_pi_apply y).comp ((measurable_pi_apply x).comp
        (measurable_snd : Measurable (fun z : ℝ × (Copy → Copy → ℝ) => z.2)))

/-- Exact right-associated carrier required by the preserved complete
calendar-and-tail consumer. Both active and inactive branches are included,
so this theorem applies to arbitrary raw records, including failed prefixes. -/
lemma fold_matrix_joint_measurable (N : RootedBinary V E X)
    {sample : Copy → X} (n : Nat) :
    Measurable (fun z : Code N sample ×
        (ℝ × ((Copy → Copy → ℝ) × ClockTrace N sample n)) =>
      foldMatrix N n z.1 z.2.1 z.2.2.1 z.2.2.2) := by
  induction n with
  | zero => exact measurable_snd.snd.fst
  | succ n ih =>
      have hh : Measurable (fun z : Code N sample ×
          (ℝ × ((Copy → Copy → ℝ) × ClockTrace N sample (n+1))) => z.2.2.2 0) :=
        (measurable_pi_apply 0).comp measurable_snd.snd.snd
      have ht : Measurable (fun z : Code N sample ×
          (ℝ × ((Copy → Copy → ℝ) × ClockTrace N sample (n+1))) =>
          fun i : Fin n => z.2.2.2 i.succ) := by
        apply measurable_pi_lambda
        intro i
        exact (measurable_pi_apply i.succ).comp measurable_snd.snd.snd
      have hu : Measurable (fun z : Code N sample ×
          (ℝ × ((Copy → Copy → ℝ) × ClockTrace N sample (n+1))) =>
          codedAgeUpdate N z.1 (z.2.2.2 0).2.2
            (z.2.1+(z.2.2.2 0).2.1) z.2.2.1) :=
        (coded_age_update_joint_measurable N).comp
          (measurable_fst.prodMk (hh.snd.snd.prodMk
            ((measurable_snd.fst.add hh.snd.fst).prodMk measurable_snd.snd.fst)))
      have ha := ih.comp (hh.snd.snd.prodMk
        (measurable_snd.fst.prodMk (hu.prodMk ht)))
      have hi := ih.comp (measurable_fst.prodMk
        (measurable_snd.fst.prodMk (measurable_snd.snd.fst.prodMk ht)))
      exact Measurable.ite (measurableSet_eq_fun hh.fst measurable_const) ha hi

/-- The original existential forest-decoration predicate is measurable on
admitted source codes because their validity is already part of Code. -/
lemma forest_decorates_joint_measurable (N : RootedBinary V E X)
    {sample : Copy → X} (leafAge : Copy → ℝ) :
    Measurable (fun z : Code N sample × (Copy → Copy → ℝ) =>
      ForestDecorates leafAge z.2 (state z.1)) := by
  apply measurable_from_prod_countable_right
  intro s
  have he : (fun M : Copy → Copy → ℝ => ForestDecorates leafAge M (state s)) =
      (fun M => CanonicalDecorates leafAge M (state s)) := by
    funext M
    exact propext (forest_decorates_iff_canonical leafAge M (state s) s.property.forest)
  rw [he]
  exact canonical_decorates_measurable leafAge (state s)

#print axioms forest_decorates_iff_canonical
#print axioms canonical_decorates_measurable
#print axioms coded_age_update_joint_measurable
#print axioms fold_matrix_joint_measurable
#print axioms forest_decorates_joint_measurable

end GProgram.G2.DecorationMeasurability
