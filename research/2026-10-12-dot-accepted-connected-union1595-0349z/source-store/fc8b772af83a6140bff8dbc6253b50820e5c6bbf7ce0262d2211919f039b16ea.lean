import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.MeasureTheory.Measure.Restrict

/-!
Unnormalized finite endpoint-fibre product regrouping.
Contributor: dot (OpenAI), 6 October 2026.

This is generic measure algebra, using Mathlib's standard restriction,
pushforward, finite sum and product identities. It proves no source Markov,
projectivity or whole-calendar path law and makes no novelty claim for those
standard identities. Empty finite carriers and zero-mass fibres are retained.
-/
namespace GProgram.G2.FiniteFibreTransport
open MeasureTheory Set
open scoped Classical BigOperators

variable {α S Q O β T : Type*}
variable [MeasurableSpace α] [MeasurableSpace S] [MeasurableSpace Q]
variable [MeasurableSpace O] [MeasurableSpace β] [MeasurableSpace T]
variable [Fintype S] [Fintype Q]
variable [MeasurableSingletonClass S] [MeasurableSingletonClass Q]

/-- Measurable endpoint fibres give an unnormalized finite partition,
including when the endpoint carrier is empty. -/
lemma finite_fibre_decomposition (μ : Measure α) (e : α → S) (he : Measurable e) :
    μ = ∑ s : S, μ.restrict {x | e x = s} := by
  have hd : Pairwise (fun s t : S => Disjoint {x | e x = s} {x | e x = t}) := by
    intro s t hst
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact hst (hx.symm.trans hy)
  have hm (s : S) : MeasurableSet {x | e x = s} := he (MeasurableSet.singleton s)
  have hu : (⋃ s : S, {x | e x = s}) = Set.univ := by
    ext x
    simp
  have h := Measure.restrict_iUnion (μ := μ) hd hm
  rw [hu,Measure.restrict_univ,Measure.sum_fintype] at h
  exact h

/-- The projected terminal restriction selects precisely the original fibres
with matching projected endpoint. This is an identity of joint observed
measures, without positive-mass or conditional-law assumptions. -/
lemma observed_endpoint_fibre_restrict (μ : Measure α) (e : α → S) (o : α → O)
    (f : S → Q) (k : O → Q) (ho : Measurable o) (hk : Measurable k)
    (hcompat : ∀ x, k (o x) = f (e x)) (s : S) (q : Q) :
    (((μ.restrict {x | e x = s}).map o).restrict {z | k z = q}) =
      if f s = q then (μ.restrict {x | e x = s}).map o else 0 := by
  have hq : MeasurableSet {z | k z = q} := hk (MeasurableSet.singleton q)
  rw [Measure.restrict_map ho hq,Measure.restrict_restrict (ho hq)]
  by_cases hs : f s = q
  · rw [if_pos hs]
    have hset : (o ⁻¹' {z | k z = q}) ∩ {x | e x = s} = {x | e x = s} := by
      ext x
      constructor
      · exact And.right
      · intro hx
        refine ⟨?_,hx⟩
        change k (o x) = q
        rw [hcompat x,hx,hs]
    rw [hset]
  · rw [if_neg hs]
    have hset : (o ⁻¹' {z | k z = q}) ∩ {x | e x = s} = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      apply hs
      calc
        f s = f (e x) := congrArg f hx.2.symm
        _ = k (o x) := (hcompat x).symm
        _ = q := hx.1
    rw [hset,Measure.restrict_empty,Measure.map_zero]

lemma observed_fibre_eq_finite_sum (μ : Measure α) (e : α → S) (o : α → O)
    (f : S → Q) (k : O → Q) (he : Measurable e) (ho : Measurable o) (hk : Measurable k)
    (hcompat : ∀ x, k (o x) = f (e x)) (q : Q) :
    (μ.map o).restrict {z | k z = q} =
      ∑ s : S, if f s = q then (μ.restrict {x | e x = s}).map o else 0 := by
  have hmap : μ.map o = ∑ s : S, (μ.restrict {x | e x = s}).map o := by
    have h := congrArg (fun η : Measure α => η.map o) (finite_fibre_decomposition μ e he)
    rw [Measure.map_finset_sum' ho.aemeasurable] at h
    exact h
  rw [hmap,← Measure.sum_fintype,Measure.restrict_sum_of_countable,Measure.sum_fintype]
  apply Finset.sum_congr rfl
  intro s hs
  exact observed_endpoint_fibre_restrict μ e o f k ho hk hcompat s q

lemma prod_finite_sum_left (m : S → Measure O) (ν : Measure β) [SFinite ν] :
    (∑ s : S, m s).prod ν = ∑ s : S, (m s).prod ν := by
  rw [← Measure.sum_fintype,Measure.prod_sum_left,Measure.sum_fintype]

/-- Regroup actual endpoint fibres by their projected terminal state. Every
fibre remains unnormalized, and the full observation o is retained jointly.
No injectivity, surjectivity, nonemptiness or independence is assumed. -/
theorem finite_endpoint_fibre_product_regroup (μ : Measure α) [IsFiniteMeasure μ]
    (e : α → S) (o : α → O) (f : S → Q) (k : O → Q)
    (he : Measurable e) (ho : Measurable o) (hk : Measurable k)
    (hcompat : ∀ x, k (o x) = f (e x))
    (ν : Q → Measure β) [∀ q, SFinite (ν q)] :
    ∑ s : S, ((μ.restrict {x | e x = s}).map o).prod (ν (f s)) =
      ∑ q : Q, ((μ.map o).restrict {z | k z = q}).prod (ν q) := by
  let m : S → Measure O := fun s => (μ.restrict {x | e x = s}).map o
  calc
    ∑ s : S, (m s).prod (ν (f s)) =
        ∑ s : S, ∑ q : Q, if f s = q then (m s).prod (ν q) else 0 := by
      apply Finset.sum_congr rfl
      intro s hs
      simp
    _ = ∑ q : Q, ∑ s : S, if f s = q then (m s).prod (ν q) else 0 :=
      Finset.sum_comm
    _ = ∑ q : Q, (∑ s : S, if f s = q then m s else 0).prod (ν q) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [prod_finite_sum_left]
      apply Finset.sum_congr rfl
      intro s hs
      split_ifs <;> simp only [Measure.zero_prod]
    _ = ∑ q : Q, ((μ.map o).restrict {z | k z = q}).prod (ν q) := by
      apply Finset.sum_congr rfl
      intro q hq
      rw [observed_fibre_eq_finite_sum μ e o f k he ho hk hcompat q]

/-- Replace the joint observed measure by an established equal measure and
apply a measurable concatenation. Equality of observed measures and the
literal endpoint-readout compatibility remain explicit, separate inputs. -/
theorem finite_endpoint_fibre_product_regroup_map (μ : Measure α) [IsFiniteMeasure μ]
    (e : α → S) (o : α → O) (f : S → Q) (k : O → Q)
    (he : Measurable e) (ho : Measurable o) (hk : Measurable k)
    (hcompat : ∀ x, k (o x) = f (e x))
    (ν : Q → Measure β) [∀ q, SFinite (ν q)]
    (π : Measure O) (hπ : μ.map o = π) (g : O × β → T) (hg : Measurable g) :
    ∑ s : S, (((μ.restrict {x | e x = s}).map o).prod (ν (f s))).map g =
      ∑ q : Q, ((π.restrict {z | k z = q}).prod (ν q)).map g := by
  have h := congrArg (fun η : Measure (O × β) => η.map g)
    (finite_endpoint_fibre_product_regroup μ e o f k he ho hk hcompat ν)
  rw [Measure.map_finset_sum' hg.aemeasurable,
    Measure.map_finset_sum' hg.aemeasurable,hπ] at h
  exact h

#print axioms finite_fibre_decomposition
#print axioms observed_endpoint_fibre_restrict
#print axioms observed_fibre_eq_finite_sum
#print axioms prod_finite_sum_left
#print axioms finite_endpoint_fibre_product_regroup
#print axioms finite_endpoint_fibre_product_regroup_map
end GProgram.G2.FiniteFibreTransport
