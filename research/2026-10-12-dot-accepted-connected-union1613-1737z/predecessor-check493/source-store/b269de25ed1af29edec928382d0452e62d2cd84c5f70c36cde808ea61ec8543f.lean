import G2OriginalProgramSafety

/-!
Measurability of strict chronological tree support.
Contributor: dot (OpenAI), 6 October 2026.
Valid source codes permit the explicit faithful decoder to replace existential
age decorations, including parent/child inequalities and internal time bounds.
-/
namespace GProgram.G2.TimedBoundMeasurability
set_option backward.isDefEq.respectTransparency false
open MeasureTheory GProgram.SourceForest Nanuq.Source
open GProgram.G2.FaithfulPairAgeDecoration GProgram.G2.ChronologicalDecoration
open GProgram.G2.DecorationMeasurability GProgram.G2.SourceGraftDecoration
open UnifiedLean.Source.UniformizedSourceStep
open scoped Classical
variable {V E Copy X : Type*}
variable [DecidableEq Copy] [Fintype Copy]

lemma root_age_measurable (leafAge : Copy → ℝ) (t : Genealogy Copy) :
    Measurable (rootAge leafAge t) := by
  cases t with
  | leaf x => exact measurable_const
  | graft a b => exact measurable_fst

lemma chronological_measurable (leafAge : Copy → ℝ) (t : Genealogy Copy) :
    Measurable (Chronological leafAge t) := by
  induction t with
  | leaf x => exact measurable_const
  | graft a b ha hb =>
      have hca : Measurable (fun d : ℝ × Decoration a × Decoration b => Chronological leafAge a d.2.1) := ha.comp measurable_snd.fst
      have hcb : Measurable (fun d : ℝ × Decoration a × Decoration b => Chronological leafAge b d.2.2) := hb.comp measurable_snd.snd
      have hla : Measurable (fun d : ℝ × Decoration a × Decoration b => rootAge leafAge a d.2.1 < d.1) :=
        (measurableSet_lt ((root_age_measurable leafAge a).comp measurable_snd.fst) measurable_fst).mem
      have hlb : Measurable (fun d : ℝ × Decoration a × Decoration b => rootAge leafAge b d.2.2 < d.1) :=
        (measurableSet_lt ((root_age_measurable leafAge b).comp measurable_snd.snd) measurable_fst).mem
      simpa only [Chronological,Decoration,decorationMeasurable] using hca.and (hcb.and (hla.and hlb))

lemma internal_bound_joint_measurable (t : Genealogy Copy) :
    Measurable (fun z : ℝ × Decoration t => InternalBound z.1 t z.2) := by
  induction t with
  | leaf x => exact measurable_const
  | graft a b ha hb =>
      have hroot : Measurable (fun z : ℝ × (ℝ × Decoration a × Decoration b) => z.2.1 ≤ z.1) :=
        (measurableSet_le measurable_snd.fst measurable_fst).mem
      have hca : Measurable (fun z : ℝ × (ℝ × Decoration a × Decoration b) => InternalBound z.1 a z.2.2.1) :=
        ha.comp (measurable_fst.prodMk measurable_snd.snd.fst)
      have hcb : Measurable (fun z : ℝ × (ℝ × Decoration a × Decoration b) => InternalBound z.1 b z.2.2.2) :=
        hb.comp (measurable_fst.prodMk measurable_snd.snd.snd)
      simpa only [InternalBound,Decoration,decorationMeasurable] using hroot.and (hca.and hcb)

noncomputable def CanonicalTimedBound (leafAge : Copy → ℝ) (M : Copy → Copy → ℝ)
    (s : State V E Copy) (bound : ℝ) : Prop :=
  CanonicalDecorates leafAge M s ∧ ∀ l ∈ s.live,
    Chronological leafAge (s.genealogy l) (decode M (s.genealogy l)) ∧
    InternalBound bound (s.genealogy l) (decode M (s.genealogy l))

lemma timed_bound_iff_canonical (leafAge : Copy → ℝ) (M : Copy → Copy → ℝ)
    (s : State V E Copy) (hs : Valid s) (bound : ℝ) :
    TimedBound leafAge M s bound ↔ CanonicalTimedBound leafAge M s bound := by
  constructor
  · intro h
    refine ⟨(forest_decorates_iff_canonical leafAge M s hs).mp (timed_bound_decorates leafAge M s bound h),?_⟩
    intro l hl
    obtain ⟨d,hd,hc,hi⟩ := h l hl
    have he := decode_of_pair_agreement leafAge _ (hs.wellLabelled l hl) d M hd
    simpa only [he] using And.intro hc hi
  · intro h l hl
    exact ⟨decode M (s.genealogy l),h.1 l hl,(h.2 l hl).1,(h.2 l hl).2⟩

lemma canonical_timed_bound_measurable (leafAge : Copy → ℝ) (s : State V E Copy) :
    Measurable (fun z : ℝ × (Copy → Copy → ℝ) => CanonicalTimedBound leafAge z.2 s z.1) := by
  apply Measurable.and ((canonical_decorates_measurable leafAge s).comp measurable_snd)
  apply Measurable.forall
  intro l
  apply Measurable.imp measurable_const
  have hd : Measurable (fun z : ℝ × (Copy → Copy → ℝ) => decode z.2 (s.genealogy l)) :=
    (decode_measurable (s.genealogy l)).comp measurable_snd
  exact ((chronological_measurable leafAge (s.genealogy l)).comp hd).and
    ((internal_bound_joint_measurable (s.genealogy l)).comp (measurable_fst.prodMk hd))

variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

lemma timed_bound_joint_measurable (N : RootedBinary V E X) {sample : Copy → X}
    (leafAge : Copy → ℝ) :
    Measurable (fun z : Code N sample × (ℝ × (Copy → Copy → ℝ)) =>
      TimedBound leafAge z.2.2 (state z.1) z.2.1) := by
  apply measurable_from_prod_countable_right
  intro s
  have he : (fun z : ℝ × (Copy → Copy → ℝ) => TimedBound leafAge z.2 (state s) z.1) =
      (fun z => CanonicalTimedBound leafAge z.2 (state s) z.1) := by
    funext z
    exact propext (timed_bound_iff_canonical leafAge z.2 (state s) s.property.forest z.1)
  rw [he]
  exact canonical_timed_bound_measurable leafAge (state s)

#print axioms timed_bound_joint_measurable
end GProgram.G2.TimedBoundMeasurability
