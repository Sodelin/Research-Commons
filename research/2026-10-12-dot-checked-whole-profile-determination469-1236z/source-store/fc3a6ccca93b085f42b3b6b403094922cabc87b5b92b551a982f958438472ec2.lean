import G7FiniteForestReassembly
import Mathlib.Algebra.MvPolynomial.Eval

/-! Actual full finite forest epoch law: one shared rational multivariate
polynomial table in the original physical survival variables. -/
universe uC
namespace GProgram.G7.FullEpochPolynomial
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.SourceEpochRenewal
open GProgram.G7.WholeAncestorPanelCode GProgram.G7.PopulationForestReassembly
open GProgram.G7.FiniteForestReassembly GProgram.G7.SinglePopulationPolynomialKernel
open G1ActualJointEpoch DotG6.ActualPopulationPanelSplit
open scoped Classical NNReal BigOperators
variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

noncomputable def survival (r : PositivePairRates E) (t : ℝ≥0) (i : Option E) : ℝ :=
  Real.exp (-pairRate r i * (t:ℝ))

noncomputable def evaluate (r : PositivePairRates E) (t : ℝ≥0)
    (p : MvPolynomial (Option E) ℚ) : ℝ :=
  MvPolynomial.eval₂ (Rat.castHom ℝ) (survival r t) p

def PolynomialLaw {A : Type*} (law : PositivePairRates E → ℝ≥0 → PMF A) : Prop :=
  ∃ p : A → MvPolynomial (Option E) ℚ,
    ∀ r t a, evaluate r t (p a) = (law r t a).toReal

noncomputable def embed (i : Option E) (p : Polynomial ℚ) : MvPolynomial (Option E) ℚ :=
  p.sum (fun n a => MvPolynomial.C a * MvPolynomial.X i ^ n)

lemma evaluate_embed (r : PositivePairRates E) (t : ℝ≥0) (i : Option E) (p : Polynomial ℚ) :
    evaluate r t (embed i p) = Polynomial.eval₂ (Rat.castHom ℝ) (survival r t i) p := by
  simp [evaluate,embed,Polynomial.eval₂_eq_sum,Polynomial.sum_def,
    MvPolynomial.eval₂_mul]

lemma polynomialLaw_pure {A : Type*} (a : A) :
    PolynomialLaw (E := E) (fun _ _ => PMF.pure a) := by
  refine ⟨fun b => if a = b then 1 else 0, ?_⟩
  intro r t b
  by_cases h : a = b <;> simp [evaluate,PMF.pure_apply,h,eq_comm]

lemma polynomialLaw_map {A B : Type*} [Fintype A]
    (law : PositivePairRates E → ℝ≥0 → PMF A) (h : PolynomialLaw law) (f : A → B) :
    PolynomialLaw (fun r t => (law r t).map f) := by
  obtain ⟨p,hp⟩ := h
  refine ⟨fun b => ∑ a : A, if f a = b then p a else 0, ?_⟩
  intro r t b
  rw [map_probability_real]
  simp only [evaluate,MvPolynomial.eval₂_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases he : f a = b
  · simp only [if_pos he,mul_one]
    exact hp r t a
  · simp [he]

lemma polynomialLaw_product {A B : Type*} [Fintype A] [Fintype B]
    (p : PositivePairRates E → ℝ≥0 → PMF A) (q : PositivePairRates E → ℝ≥0 → PMF B)
    (hp : PolynomialLaw p) (hq : PolynomialLaw q) :
    PolynomialLaw (fun r t => independentProduct (p r t) (q r t)) := by
  obtain ⟨P,hP⟩ := hp
  obtain ⟨Q,hQ⟩ := hq
  refine ⟨fun ab => P ab.1 * Q ab.2, ?_⟩
  intro r t ab
  rw [independentProduct_apply,ENNReal.toReal_mul]
  simp only [evaluate,MvPolynomial.eval₂_mul]
  exact congrArg₂ (fun x y : ℝ => x*y) (hP r t ab.1) (hQ r t ab.2)

variable {Copy : Type*} [DecidableEq Copy] [Fintype Copy]

lemma colocated_polynomial_law (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (hs : CoLocated N s i) :
    PolynomialLaw (fun r t => (sourceTimeKernel N r t s).map (projection N Finset.univ)) := by
  apply polynomialLaw_map
  refine ⟨fun d => embed i (populationPolynomial N s d), ?_⟩
  intro r t d
  rw [evaluate_embed]
  exact actual_population_polynomial N s d i hs r t

lemma panelCode_copyLocation (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (hc : AncestorClosed (state s) keep)
    (x : SelectedCopy keep) :
    copyLocation (state (panelCode N s keep hc)) x = copyLocation (state s) x.val := by
  change copyLocation (decodeSnapshot N.root (encodeSnapshot
    (restrictState (state s) s.property.forest keep hc)
    (restrictState_valid (state s) s.property.forest keep hc))) x = _
  rw [decode_encode_copyLocation]
  rfl

def ActiveIn (N : RootedBinary V E X) {sample : Copy → X} (s : Code N sample)
    (todo : Finset (Option E)) : Prop :=
  ∀ x i, copyLocation (state s) x = originalPlace N i → i ∈ todo

lemma no_active_choices (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (h : ActiveIn N s ∅) : IsEmpty (Choice N s) := by
  refine ⟨fun p => ?_⟩
  have hp := Finset.mem_filter.mp (Finset.mem_offDiag.mp p.2.property).1
  have hr : (state s).ancestor p.2.val.1 = p.2.val.1 :=
    s.property.forest.representative _ hp.1
  have hx : copyLocation (state s) p.2.val.1 = originalPlace N p.1 := by
    change (state s).location ((state s).ancestor p.2.val.1) = _
    rw [hr]
    exact hp.2
  exact Finset.notMem_empty _ (h _ _ hx)

lemma inactive_epoch (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (h : ActiveIn N s ∅) (r : PositivePairRates E) (t : ℝ≥0) :
    sourceTimeKernel N r t s = PMF.pure s := by
  letI := no_active_choices N s h
  apply PMF.ext
  intro d
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [actual_source_kernel_first_jump]
  by_cases he : s = d <;> simp [totalRate,PMF.pure_apply,he,eq_comm]

lemma exterior_active (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (todo : Finset (Option E))
    (h : ActiveIn N s (insert i todo)) :
    let keep := populationPanel (state s) (originalPlace N i)
    let hc : AncestorClosed (state s) keep :=
      locationPanel_closed (state s) s.property.forest (originalPlace N i)
    ActiveIn N (panelCode N s (Finset.univ \ keep) (closed_complement (state s) keep hc)) todo := by
  dsimp only
  intro x j hx
  rw [panelCode_copyLocation] at hx
  rcases Finset.mem_insert.mp (h x.val j hx) with he | hj
  · subst j
    have hn := (Finset.mem_sdiff.mp x.property).2
    exact False.elim (hn ((mem_populationPanel _ _ _).mpr hx))
  · exact hj

theorem polynomial_by_active_set (N : RootedBinary V E X) (todo : Finset (Option E)) :
    ∀ (C : Type uC) [DecidableEq C] [Fintype C] (sample : C → X)
      (s : Code N sample), ActiveIn N s todo →
      PolynomialLaw (fun r t => (sourceTimeKernel N r t s).map (projection N Finset.univ)) := by
  induction todo using Finset.induction_on with
  | empty =>
    intro C _ _ sample s hs
    have he : (fun (r : PositivePairRates E) (t : ℝ≥0) =>
        (sourceTimeKernel N r t s).map (projection N Finset.univ)) =
        (fun _ _ => PMF.pure (projection N Finset.univ s)) := by
      funext r t
      rw [inactive_epoch N s hs r t,PMF.pure_map]
    rw [he]
    exact polynomialLaw_pure _
  | @insert i todo hi ih =>
    intro C _ _ sample s hs
    let keep := populationPanel (state s) (originalPlace N i)
    have hc : AncestorClosed (state s) keep :=
      locationPanel_closed (state s) s.property.forest (originalPlace N i)
    have hleft := colocated_polynomial_law N (panelCode N s keep hc) i
      (panelCode_colocated N s i)
    have hright := ih (SelectedCopy (Finset.univ \ keep))
      (selectedSample sample (Finset.univ \ keep))
      (panelCode N s (Finset.univ \ keep) (closed_complement (state s) keep hc))
      (exterior_active N s i todo hs)
    have hout := polynomialLaw_map _ (polynomialLaw_product _ _ hleft hright)
      (joinIndex N s keep)
    obtain ⟨P,hP⟩ := hout
    refine ⟨P,?_⟩
    intro r t a
    dsimp only
    rw [actual_finite_forest_reassembly N r t s (originalPlace N i)]
    exact hP r t a

/-- One rational multivariate table works simultaneously for EVERY positive
original physical rate bank and nonnegative duration, with the actual full
selected forest and original register as its finite output. -/
theorem actual_full_epoch_polynomial (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) :
    PolynomialLaw (fun r t => (sourceTimeKernel N r t s).map (projection N Finset.univ)) :=
  polynomial_by_active_set N Finset.univ Copy sample s (fun _ _ _ => Finset.mem_univ _)

end GProgram.G7.FullEpochPolynomial
