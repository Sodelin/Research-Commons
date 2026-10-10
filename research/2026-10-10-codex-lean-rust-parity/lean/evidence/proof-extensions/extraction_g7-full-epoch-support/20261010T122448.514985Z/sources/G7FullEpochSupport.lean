import G7SparseRowProducts
import G7EffectivePanelJoin

/-!
# Literal support products refine the complete original epoch coefficients

Contributor: Codex / lean_reuse_successor, 2026-10-10.
The executable baseline uses the actual entering Code, its whole ancestor
population panels, the original ordered merger coefficients, and constructive
literal panel joins. Each restricted tree is mapped back by the original
subtype label embedding. No complete Code or selected-index carrier is scanned.
The proof compares the entire rational polynomial to unchanged fullCoefficients,
not a finite collection of rates. Physical epoch semantics retain inherited
ActiveIn/positive-bank/nonnegative-duration premises. Draft pending fresh audit.
-/
universe uC
namespace GProgram.G7.FullEpochSupport
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.SourceForestSilentPruning
open GProgram.G7.SinglePopulationPolynomialKernel
open GProgram.G7.EffectiveSourceEnumeration GProgram.G7.EffectivePopulationCoefficients
open GProgram.G7.WholeAncestorPanelCode GProgram.G7.PopulationForestReassembly
open GProgram.G7.EffectiveFullEpochCoefficients
open GProgram.G7.EffectiveCoefficientSupport GProgram.G7.PopulationSelectedSupport
open GProgram.G7.EffectivePanelJoin GProgram.G7.SparseRowProducts
open GProgram.G7.FullEpochPolynomial
open DotG6.ActualPopulationPanelSplit
open scoped BigOperators NNReal

variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [FinEnum V] [FinEnum E]
variable {Copy : Type uC} [DecidableEq Copy] [Fintype Copy] [FinEnum Copy]

def populationRows (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) : Rows (Option E) (Code N sample) :=
  (destinations N (Fintype.card Copy) s).dedup.map fun d =>
    (d,embedExpr i (coefficients N (Fintype.card Copy) s d))

lemma read_populationRows (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (a : SelectedIndex N sample Finset.univ) :
    readRows (project N Finset.univ) (populationRows N s i) a =
      populationSelectedSupport N s i a := by
  simp only [populationRows,readRows,List.flatMap_map,populationSelectedSupport]

lemma polynomial_populationRows (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (a : SelectedIndex N sample Finset.univ) :
    polynomial (readRows (project N Finset.univ) (populationRows N s i) a) =
      polynomial (populationSelected N s i a) := by
  rw [read_populationRows,polynomial_populationSelectedSupport]

lemma merger_register (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) :
    (merger N s p).val.register = s.val.register := rfl

lemma destinations_register (N : RootedBinary V E X) {sample : Copy → X}
    (fuel : Nat) (s d : Code N sample) (hd : d ∈ destinations N fuel s) :
    d.val.register = s.val.register := by
  induction fuel generalizing s with
  | zero =>
      have he : d = s := List.mem_singleton.mp hd
      rw [he]
  | succ fuel ih =>
      by_cases h : s.val.live.card ≤ 1
      · rw [destinations,if_pos h] at hd
        have he : d = s := List.mem_singleton.mp hd
        rw [he]
      · rw [destinations,if_neg h] at hd
        rcases List.mem_cons.mp hd with he | hd
        · rw [he]
        · rcases List.mem_flatMap.mp hd with ⟨p,_,hd⟩
          exact (ih (merger N s p) hd).trans (merger_register N s p)

lemma populationRows_register (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (row : Code N sample × Sparse (Option E))
    (hrow : row ∈ populationRows N s i) : row.1.val.register = s.val.register := by
  rcases List.mem_map.mp hrow with ⟨d,hd,he⟩
  rw [← he]
  exact destinations_register N (Fintype.card Copy) s d (List.mem_dedup.mp hd)

/-- The same source population restriction as the unchanged inherited readout.
Every output row carries an explicit original admitted Code witness. -/
def fullRows (N : RootedBinary V E X) : (todo : List (Option E)) →
    (C : Type uC) → [DecidableEq C] → [Fintype C] → [FinEnum C] →
    (sample : C → X) → (s : Code N sample) → Rows (Option E) (Code N sample)
  | [],C,_,_,_,sample,s => [(s,single 1)]
  | i::todo,C,_,_,_,sample,s =>
      let keep := Finset.univ.filter (fun x => copyLocation (sourceState s) x = place N i)
      let hc : AncestorClosed (state s) keep :=
        locationPanel_closed (state s) s.property.forest (originalPlace N i)
      let left := panel N s keep hc
      let right := panel N s (Finset.univ \ keep) (closed_complement (state s) keep hc)
      multiplyRows (joinedCode N keep) (populationRows N left i)
        (fullRows N todo (SelectedCopy (Finset.univ \ keep))
          (selectedSample sample (Finset.univ \ keep)) right)

lemma fullRows_cons (N : RootedBinary V E X) {sample : Copy → X}
    (i : Option E) (todo : List (Option E)) (s : Code N sample) :
    fullRows N (i::todo) Copy sample s =
      let keep := populationPanel (state s) (originalPlace N i)
      let hc : AncestorClosed (state s) keep :=
        locationPanel_closed (state s) s.property.forest (originalPlace N i)
      let left := panel N s keep hc
      let right := panel N s (Finset.univ \ keep) (closed_complement (state s) keep hc)
      multiplyRows (joinedCode N keep) (populationRows N left i)
        (fullRows N todo (SelectedCopy (Finset.univ \ keep))
          (selectedSample sample (Finset.univ \ keep)) right) := rfl

/-- All row witnesses retain the same complete original entering register.
No panel draws an independent replacement register. -/
theorem fullRows_register (N : RootedBinary V E X) (todo : List (Option E))
    {sample : Copy → X} (s : Code N sample)
    (row : Code N sample × Sparse (Option E)) (hrow : row ∈ fullRows N todo Copy sample s) :
    row.1.val.register = s.val.register := by
  cases todo with
  | nil =>
      have he : row = (s,single 1) := List.mem_singleton.mp hrow
      rw [he]
  | cons i todo =>
      let keep := populationPanel (state s) (originalPlace N i)
      let hc : AncestorClosed (state s) keep :=
        locationPanel_closed (state s) s.property.forest (originalPlace N i)
      let left := panel N s keep hc
      rw [fullRows_cons] at hrow
      rcases List.mem_flatMap.mp hrow with ⟨a,ha,hrow⟩
      rcases List.mem_map.mp hrow with ⟨b,_,he⟩
      rw [← he]
      change a.1.val.register = s.val.register
      exact (populationRows_register N left i a ha).trans (by rfl)

/-- Universal polynomial identity; no physical rate, CoLocated or ActiveIn
premise is needed for this purely executable/algebraic equality. -/
theorem polynomial_fullRows (N : RootedBinary V E X) (todo : List (Option E)) :
    ∀ (C : Type uC) [DecidableEq C] [Fintype C] [FinEnum C] (sample : C → X)
      (s : Code N sample) (a : SelectedIndex N sample Finset.univ),
      polynomial (readRows (project N Finset.univ) (fullRows N todo C sample s) a) =
        polynomial (fullCoefficients N todo C sample s a) := by
  classical
  induction todo with
  | nil =>
      intro C _ _ _ sample s a
      by_cases h : project N Finset.univ s = a
      · simp [fullRows,readRows,fullCoefficients,h]
      · simp [fullRows,readRows,fullCoefficients,h,polynomial,single]
  | cons i todo ih =>
      intro C _ _ _ sample s a
      let keep := populationPanel (state s) (originalPlace N i)
      let hc : AncestorClosed (state s) keep :=
        locationPanel_closed (state s) s.property.forest (originalPlace N i)
      let left := panel N s keep hc
      let right := panel N s (Finset.univ \ keep) (closed_complement (state s) keep hc)
      have hrows : fullRows N (i::todo) C sample s =
          multiplyRows (joinedCode N keep) (populationRows N left i)
            (fullRows N todo (SelectedCopy (Finset.univ \ keep))
              (selectedSample sample (Finset.univ \ keep)) right) := rfl
      rw [hrows,polynomial_read_multiplyRows_partition
        (joinedCode N keep) (project N Finset.univ) (project N Finset.univ)
        (project N Finset.univ) (joinSelected N s keep)
        (fun a b => joinedSelected_eq N s keep a b),
        fullCoefficients_cons,polynomial_enumerate]
      apply Finset.sum_congr rfl
      intro ab _
      by_cases h : joinSelected N s keep ab = a
      · simp only [if_pos h,polynomial_product,polynomial_populationRows]
        rw [ih]
      · simp only [if_neg h,polynomial,List.map_nil,List.sum_nil]

theorem value_fullRows (N : RootedBinary V E X) (todo : List (Option E))
    {sample : Copy → X} (s : Code N sample) (a : SelectedIndex N sample Finset.univ)
    (x : Option E → ℝ) :
    value (readRows (project N Finset.univ) (fullRows N todo Copy sample s) a) x =
      value (fullCoefficients N todo Copy sample s a) x := by
  have h := congrArg (MvPolynomial.eval₂ (Rat.castHom ℝ) x)
    (polynomial_fullRows N todo Copy sample s a)
  rw [eval_polynomial,eval_polynomial] at h
  exact h

theorem fullRows_actual (N : RootedBinary V E X) (todo : List (Option E))
    {sample : Copy → X} (s : Code N sample) (hs : ActiveIn N s todo.toFinset)
    (a : SelectedIndex N sample Finset.univ) (r : PositivePairRates E) (t : ℝ≥0) :
    value (readRows (project N Finset.univ) (fullRows N todo Copy sample s) a)
        (survival r t) =
      (((sourceTimeKernel N r t s).map (projection N Finset.univ)) a).toReal := by
  rw [value_fullRows]
  exact fullCoefficients_actual N todo Copy sample s hs a r t

def epochRows (N : RootedBinary V E X) {sample : Copy → X} (s : Code N sample) :
    Rows (Option E) (Code N sample) :=
  fullRows N (FinEnum.toList (Option E)) Copy sample s

theorem polynomial_epochRows (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (a : SelectedIndex N sample Finset.univ) :
    polynomial (readRows (project N Finset.univ) (epochRows N s) a) =
      polynomial (epochCoefficients N s a) :=
  polynomial_fullRows N (FinEnum.toList (Option E)) Copy sample s a

theorem epochRows_actual (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (a : SelectedIndex N sample Finset.univ)
    (r : PositivePairRates E) (t : ℝ≥0) :
    evaluate r t (polynomial (readRows (project N Finset.univ) (epochRows N s) a)) =
      (((sourceTimeKernel N r t s).map (projection N Finset.univ)) a).toReal := by
  rw [polynomial_epochRows]
  exact actual_full_epoch_coefficients N s a r t

#print axioms polynomial_fullRows
#print axioms fullRows_register
#print axioms fullRows_actual
#print axioms epochRows_actual
end GProgram.G7.FullEpochSupport
