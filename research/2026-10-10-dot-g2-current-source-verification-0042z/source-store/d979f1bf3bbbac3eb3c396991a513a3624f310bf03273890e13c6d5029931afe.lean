import UnifiedLean.Source.SourceFirstMarkDistribution
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Actual exponential race: split an original CURRENT pair clock

Contributor: dot, 2026-10-02. Finite product-measure coordinate decomposition
for the current source pair clocks, feeding the explicit winning-label/time
calculation. This standard measure identity is not a desired race law field.
Ordered half-rate choices remain internal encoding; physical unordered/unranked
readout and post-event reset/path binding must be retained as separate gates.
-/
namespace UnifiedLean.Source.SourceExponentialRace
set_option backward.isDefEq.respectTransparency false
open MeasureTheory Set ProbabilityTheory
open scoped Classical BigOperators NNReal ENNReal
variable {I : Type*} [Fintype I] [DecidableEq I]

abbrev Other (p : I) := {q : I // q ≠ p}

/-- Literal clock coordinate split, preserving every original choice ID. -/
noncomputable def splitClock (p : I) : (I → ℝ) ≃ᵐ (ℝ × (Other p → ℝ)) where
  toFun c := (c p,fun q => c q.val)
  invFun z q := if h : q = p then z.1 else z.2 ⟨q,h⟩
  left_inv c := by
    funext q
    by_cases h : q = p
    · subst q; simp
    · simp [h]
  right_inv z := by
    apply Prod.ext
    · simp
    · funext q; simp [q.property]
  measurable_toFun := by
    change Measurable (fun c : I → ℝ => (c p,fun q : Other p => c q.val))
    fun_prop
  measurable_invFun := by
    change Measurable (fun z : ℝ × (Other p → ℝ) => fun q : I =>
      if h : q = p then z.1 else z.2 ⟨q,h⟩)
    apply measurable_pi_lambda
    intro q
    by_cases h : q = p
    · simp only [dif_pos h]; fun_prop
    · simp only [dif_neg h]; fun_prop

lemma splitClock_preimage_pi (p : I) (sets : I → Set ℝ) :
    (splitClock p).symm ⁻¹' (Set.univ.pi sets) =
      sets p ×ˢ Set.univ.pi (fun q : Other p => sets q.val) := by
  ext z
  simp only [Set.mem_preimage,Set.mem_pi,Set.mem_prod,Set.mem_univ,true_implies]
  change (∀ q : I, (if h : q = p then z.1 else z.2 ⟨q,h⟩) ∈ sets q) ↔
    (z.1 ∈ sets p ∧ ∀ q : Other p, z.2 q ∈ sets q.val)
  constructor
  · intro h
    refine ⟨by simpa using h p,?_⟩
    intro q
    simpa only [dif_neg q.property] using h q.val
  · rintro ⟨hp,hother⟩ q
    by_cases hq : q = p
    · subst q; simpa using hp
    · simpa only [dif_neg hq] using hother ⟨q,hq⟩

/-- Standard finite product split derived on measurable rectangles; no
conditional race/winner probability has been supplied. -/
theorem splitClock_measurePreserving (mu : I → Measure ℝ) [∀ i, SigmaFinite (mu i)] (p : I) :
    MeasurePreserving (splitClock p) (Measure.pi mu)
      ((mu p).prod (Measure.pi (fun q : Other p => mu q.val))) := by
  apply MeasurePreserving.symm (splitClock p).symm
  refine ⟨(splitClock p).symm.measurable, (Measure.pi_eq (fun sets hsets => ?_)).symm⟩
  rw [(splitClock p).symm.map_apply,splitClock_preimage_pi,Measure.prod_prod,Measure.pi_pi]
  letI : Unique {q : I // q = p} :=
    {default := ⟨p,rfl⟩,uniq := by intro q; exact Subtype.ext q.property}
  have hh := Fintype.prod_subtype_mul_prod_subtype (fun q : I => q = p) (fun q => mu q (sets q))
  have hd : (default : {q : I // q = p}).val = p := (default : {q : I // q = p}).property
  simpa only [Fintype.prod_unique,hd] using hh

/-- Winning CURRENT original pair p no later than t, with all other genuine
pair clocks strictly later. This is a latent source event, not a new readout. -/
def winnerBefore (p : I) (t : ℝ) : Set (I → ℝ) :=
  {c | c p ≤ t ∧ ∀ q : I, q ≠ p → c p < c q}

def splitWinnerBefore (p : I) (t : ℝ) : Set (ℝ × (Other p → ℝ)) :=
  {z | z.1 ≤ t ∧ ∀ q : Other p, z.1 < z.2 q}

lemma winnerBefore_preimage (p : I) (t : ℝ) :
    (splitClock p) ⁻¹' splitWinnerBefore p t = winnerBefore p t := by
  ext c
  simp only [Set.mem_preimage,splitWinnerBefore,winnerBefore,Set.mem_setOf_eq,splitClock,
    MeasurableEquiv.coe_mk]
  constructor
  · rintro ⟨ht,h⟩
    exact ⟨ht,fun q hq => h ⟨q,hq⟩⟩
  · rintro ⟨ht,h⟩
    exact ⟨ht,fun q => h q.val q.property⟩

lemma measurable_split_winner (p : I) (t : ℝ) : MeasurableSet (splitWinnerBefore p t) := by
  have h1 : MeasurableSet {z : ℝ × (Other p → ℝ) | z.1 ≤ t} :=
    measurableSet_le measurable_fst measurable_const
  have h2 : MeasurableSet (⋂ q : Other p, {z : ℝ × (Other p → ℝ) | z.1 < z.2 q}) :=
    MeasurableSet.iInter (fun q => measurableSet_lt measurable_fst
      ((measurable_pi_apply q).comp measurable_snd))
  simpa only [splitWinnerBefore,Set.setOf_and,Set.setOf_forall] using h1.inter h2

/-- Actual race event probability reduces by Fubini to the winning coordinate's
integral of independent competitor tails. -/
theorem actual_race_measure_reduction (mu : I → Measure ℝ) [∀ i, SigmaFinite (mu i)]
    (p : I) (t : ℝ) :
    (Measure.pi mu) (winnerBefore p t) =
      ∫⁻ x in Set.Iic t, (Measure.pi (fun q : Other p => mu q.val))
        (Set.univ.pi (fun _ : Other p => Set.Ioi x)) ∂(mu p) := by
  rw [← winnerBefore_preimage,
    (splitClock_measurePreserving mu p).measure_preimage_equiv (splitWinnerBefore p t)]
  rw [Measure.prod_apply (measurable_split_winner p t)]
  have hsets : ∀ x : ℝ, (Prod.mk x) ⁻¹' splitWinnerBefore p t =
      if x ≤ t then Set.univ.pi (fun _ : Other p => Set.Ioi x) else ∅ := by
    intro x
    by_cases hx : x ≤ t <;> ext c <;> simp [splitWinnerBefore,hx,Set.mem_pi]
  simp_rw [hsets]
  rw [← lintegral_indicator measurableSet_Iic]
  apply lintegral_congr
  intro x
  by_cases hx : x ≤ t <;> simp [hx,Set.indicator]

#print axioms splitClock_measurePreserving
#print axioms actual_race_measure_reduction
end UnifiedLean.Source.SourceExponentialRace
