import G7EffectivePopulationCoefficients
import G7FullEpochPolynomial

/-!
Executable sparse rational coefficient lists for the full actual finite
original-source forest epoch. Contributor: dot, 2026-10-10, implementing the
population-split proof already accepted in G7FullEpochPolynomial.

The output is a list of rational monomials, not Mathlib's noncomputable
MvPolynomial implementation. Every finite carrier is enumerated by FinEnum;
the recursion consumes an explicit list of original populations. The actual
source forest splits, selected views, original registers and reassembly are
unchanged. This supplies interval-kernel coefficients, not independent
whole-edge parameter coverage, cofacial admission, or effective QE.
-/
universe uC
namespace GProgram.G7.EffectiveFullEpochCoefficients
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceForestSilentPruning UnifiedLean.Source.SourceCopyCarrierTransport
open UnifiedLean.Source.FiniteSourceSnapshot
open GProgram.G7.WholeAncestorPanelCode GProgram.G7.PopulationForestReassembly
open GProgram.G7.FiniteForestReassembly GProgram.G7.FullEpochPolynomial
open GProgram.G7.SinglePopulationPolynomialKernel
open GProgram.G7.EffectiveSourceEnumeration GProgram.G7.EffectivePopulationCoefficients
open DotG6.ActualPopulationPanelSplit
open scoped NNReal BigOperators
variable {V E X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [FinEnum V] [FinEnum E]

/-- Repeated variables and monomials are permitted; no normalization oracle. -/
abbrev Sparse (I : Type*) := List (List (I × Nat) × ℚ)

def single {I : Type*} (q : ℚ) : Sparse I := [([],q)]
def product {I : Type*} (a b : Sparse I) : Sparse I :=
  a.flatMap fun x => b.map fun y => (x.1 ++ y.1, x.2*y.2)
def embedExpr {I : Type*} (i : I) (p : Expr) : Sparse I :=
  p.map fun z => ([(i,z.1)],z.2)

noncomputable def value {I : Type*} (p : Sparse I) (x : I → ℝ) : ℝ :=
  (p.map fun z => (z.2:ℝ) * (z.1.map fun a => x a.1 ^ a.2).prod).sum

noncomputable def polynomial {I : Type*} (p : Sparse I) : MvPolynomial I ℚ :=
  (p.map fun z => MvPolynomial.C z.2 *
    (z.1.map fun a => MvPolynomial.X a.1 ^ a.2).prod).sum

lemma eval_polynomial {I : Type*} (p : Sparse I) (x : I → ℝ) :
    MvPolynomial.eval₂ (Rat.castHom ℝ) x (polynomial p) = value p x := by
  simp [polynomial,value]

@[simp] lemma value_nil {I : Type*} (x : I → ℝ) : value [] x = 0 := rfl
@[simp] lemma value_single {I : Type*} (q : ℚ) (x : I → ℝ) :
    value (single q) x = (q:ℝ) := by simp [single,value]
lemma value_append {I : Type*} (a b : Sparse I) (x : I → ℝ) :
    value (a++b) x = value a x + value b x := by simp [value,List.sum_append]

lemma value_product {I : Type*} (a b : Sparse I) (x : I → ℝ) :
    value (product a b) x = value a x * value b x := by
  induction a with
  | nil => simp [product,value]
  | cons z a ih =>
      have hrow : value (b.map fun y => (z.1++y.1,z.2*y.2)) x =
          (z.2:ℝ) * (z.1.map fun a => x a.1 ^ a.2).prod * value b x := by
        induction b with
        | nil => simp [value]
        | cons y b ib =>
            simp only [List.map_cons,List.prod_append,List.map_append,
              value,List.sum_cons,Rat.cast_mul] at *
            rw [ib]
            ring
      simp only [product,List.flatMap_cons,value_append]
      rw [hrow,ih]
      simp [value,add_mul]

lemma value_flatMap {A I : Type*} (l : List A) (f : A → Sparse I) (x : I → ℝ) :
    value (l.flatMap f) x = (l.map fun a => value (f a) x).sum := by
  induction l with
  | nil => rfl
  | cons a l ih => simp only [List.flatMap_cons,value_append,List.map_cons,List.sum_cons,ih]

lemma value_enumerate {A I : Type*} [Fintype A] [FinEnum A]
    (f : A → Sparse I) (x : I → ℝ) :
    value ((FinEnum.toList A).flatMap f) x = ∑ a : A, value (f a) x := by
  rw [value_flatMap]
  rw [((enumeration_perm A).map (fun a => value (f a) x)).sum_eq]
  exact Finset.sum_map_toList _ _

lemma value_embedExpr (i : Option E) (p : Expr) (r : PositivePairRates E) (t : ℝ≥0) :
    value (embedExpr i p) (survival r t) =
      Polynomial.eval₂ (Rat.castHom ℝ) (survival r t i) (exprPolynomial p) := by
  induction p with
  | nil => simp [embedExpr,value,exprPolynomial]
  | cons z p ih =>
      simp only [embedExpr,List.map_cons,value,List.sum_cons,List.prod_cons,
        List.prod_nil,mul_one,exprPolynomial_cons,Polynomial.eval₂_add,
        Polynomial.eval₂_mul,Polynomial.eval₂_C,Polynomial.eval₂_pow,Polynomial.eval₂_X] at *
      exact congrArg (fun q => (z.2:ℝ)*(survival r t i)^z.1+q) ih

variable {Copy : Type uC} [DecidableEq Copy] [Fintype Copy] [FinEnum Copy]

/-- The executable full selected-state pushforward of the literal population row. -/
def populationSelected (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (a : SelectedIndex N sample Finset.univ) :
    Sparse (Option E) :=
  (FinEnum.toList (Code N sample)).flatMap fun d =>
    if project N Finset.univ d = a then
      embedExpr i (coefficients N (Fintype.card Copy) s d) else []

lemma populationSelected_actual (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (hs : CoLocated N s i)
    (a : SelectedIndex N sample Finset.univ) (r : PositivePairRates E) (t : ℝ≥0) :
    value (populationSelected N s i a) (survival r t) =
      (((sourceTimeKernel N r t s).map (projection N Finset.univ)) a).toReal := by
  classical
  rw [populationSelected,value_enumerate,map_probability_real]
  apply Finset.sum_congr rfl
  intro d _
  by_cases h : project N Finset.univ d = a
  · rw [if_pos h,value_embedExpr,coefficients_polynomial]
    have hp : projection N Finset.univ d = a := h
    rw [if_pos hp,mul_one]
    exact actual_population_polynomial N s d i hs r t
  · have hp : projection N Finset.univ d ≠ a := h
    simp [h,hp]

/-- Executable counterparts of the inherited panel and reassembly functions.
Their data bodies agree definitionally; source validity proofs are erased. -/
def restrictGenealogy (keep : Finset Copy) :
    (g : Genealogy Copy) → g.leaves ⊆ keep → Genealogy (SelectedCopy keep)
  | .leaf x,h => .leaf ⟨x,h (by simp [Genealogy.leaves])⟩
  | .graft a b,h => .graft
      (restrictGenealogy keep a (fun x hx => h (by simp [Genealogy.leaves,hx])))
      (restrictGenealogy keep b (fun x hx => h (by simp [Genealogy.leaves,hx])))

def panelState (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) (hc : AncestorClosed s keep) : State V E (SelectedCopy keep) where
  live := Finset.univ.filter (fun a => a.val ∈ s.live)
  ancestor x := ⟨s.ancestor x.val,(hc x.val).mp x.property⟩
  genealogy a := if ha : a.val ∈ s.live then
    restrictGenealogy keep (s.genealogy a.val) (live_tree_subset s hs keep hc a ha)
    else .leaf a
  location a := s.location a.val
  register := s.register
  history := []

def panel (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (hc : AncestorClosed (state s) keep) :
    Code N (selectedSample sample keep) :=
  encodeActual N (selectedSample sample keep) (panelState (sourceState s) s.property.forest keep hc)
    ⟨restrictState_valid (state s) s.property.forest keep hc,
      fun x => s.property.original_descendant x.val⟩

def lift (keep : Finset Copy) (v : SelectedView V E (SelectedCopy keep)) :
    SelectedView V E Copy where
  genealogy x := if hx : x ∈ keep then (v.genealogy ⟨x,hx⟩).map (mapLabels Subtype.val) else none
  population x := if hx : x ∈ keep then v.population ⟨x,hx⟩ else none
  register := v.register

def join (keep : Finset Copy) (a b : SelectedView V E Copy) : SelectedView V E Copy where
  genealogy x := if x ∈ keep then a.genealogy x else b.genealogy x
  population x := if x ∈ keep then a.population x else b.population x
  register := a.register

def index (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (v : SelectedView V E Copy) : SelectedIndex N sample Finset.univ :=
  letI := enumeratedExistsDecidable (fun d : Code N sample =>
    view N.root d.val Finset.univ = v)
  if h : ∃ d : Code N sample, view N.root d.val Finset.univ = v then
    ⟨v,h⟩ else project N Finset.univ s

def joinSelected (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy)
    (ab : SelectedIndex N (selectedSample sample keep) Finset.univ ×
      SelectedIndex N (selectedSample sample (Finset.univ \ keep)) Finset.univ) :
    SelectedIndex N sample Finset.univ :=
  index N s (join keep (lift keep ab.1.val) (lift (Finset.univ \ keep) ab.2.val))

theorem panel_eq (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (hc : AncestorClosed (state s) keep) :
    panel N s keep hc = panelCode N s keep hc := rfl

theorem joinSelected_eq (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (keep : Finset Copy) (ab) :
    joinSelected N s keep ab = joinIndex N s keep ab := rfl

/-- Structural recursion over the actual original population enumeration.
Each recursive call discards precisely one complete current-population panel. -/
def fullCoefficients (N : RootedBinary V E X) : (todo : List (Option E)) →
    (C : Type uC) → [DecidableEq C] → [Fintype C] → [FinEnum C] →
    (sample : C → X) → (s : Code N sample) →
    SelectedIndex N sample Finset.univ → Sparse (Option E)
  | [],C,_,_,_,sample,s,a => single (if project N Finset.univ s = a then 1 else 0)
  | i::todo,C,_,_,_,sample,s,a =>
      let keep := Finset.univ.filter (fun x => copyLocation (sourceState s) x = place N i)
      let hc : AncestorClosed (state s) keep :=
        locationPanel_closed (state s) s.property.forest (originalPlace N i)
      let left := panel N s keep hc
      let right := panel N s (Finset.univ \ keep) (closed_complement (state s) keep hc)
      (FinEnum.toList (SelectedIndex N (selectedSample sample keep) Finset.univ ×
        SelectedIndex N (selectedSample sample (Finset.univ \ keep)) Finset.univ)).flatMap fun ab =>
        if joinSelected N s keep ab = a then
          product (populationSelected N left i ab.1)
            (fullCoefficients N todo (SelectedCopy (Finset.univ \ keep))
              (selectedSample sample (Finset.univ \ keep)) right ab.2)
        else []

/-- The exact output coefficients represent the actual full source forest,
with uniform positive physical banks and every nonnegative epoch duration. -/
theorem fullCoefficients_actual (N : RootedBinary V E X) (todo : List (Option E)) :
    ∀ (C : Type uC) [DecidableEq C] [Fintype C] [FinEnum C] (sample : C → X)
      (s : Code N sample), ActiveIn N s todo.toFinset →
      ∀ (a : SelectedIndex N sample Finset.univ) (r : PositivePairRates E) (t : ℝ≥0),
        value (fullCoefficients N todo C sample s a) (survival r t) =
          (((sourceTimeKernel N r t s).map (projection N Finset.univ)) a).toReal := by
  classical
  induction todo with
  | nil =>
      intro C _ _ _ sample s hs a r t
      rw [inactive_epoch N s hs r t,PMF.pure_map]
      by_cases h : project N Finset.univ s = a
      · have hp : projection N Finset.univ s = a := h
        simp [fullCoefficients,h,hp,PMF.pure_apply]
      · have hp : projection N Finset.univ s ≠ a := h
        simp [fullCoefficients,h,hp,PMF.pure_apply,Ne.symm hp]
  | cons i todo ih =>
      intro C _ _ _ sample s hs a r t
      let keep := populationPanel (state s) (originalPlace N i)
      have hc : AncestorClosed (state s) keep :=
        locationPanel_closed (state s) s.property.forest (originalPlace N i)
      have hr := exterior_active N s i todo.toFinset hs
      rw [actual_finite_forest_reassembly N r t s (originalPlace N i),map_probability_real]
      change value ((FinEnum.toList _).flatMap _) (survival r t) = _
      rw [value_enumerate]
      apply Finset.sum_congr rfl
      intro ab _
      by_cases h : joinSelected N s keep ab = a
      · have hj : joinIndex N s keep ab = a := h
        rw [if_pos h,value_product,if_pos hj,mul_one,G1ActualJointEpoch.independentProduct_apply,
          ENNReal.toReal_mul]
        exact congrArg₂ (fun x y : ℝ => x*y)
          (populationSelected_actual N (panel N s keep hc) i (panelCode_colocated N s i) ab.1 r t)
          (ih _ _ (panel N s (Finset.univ \ keep) (closed_complement (state s) keep hc))
            hr ab.2 r t)
      · have hj : joinIndex N s keep ab ≠ a := h
        simp [h,hj]

/-- All original population IDs are generated by the explicit finite carrier. -/
def epochCoefficients (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (a : SelectedIndex N sample Finset.univ) : Sparse (Option E) :=
  fullCoefficients N (FinEnum.toList (Option E)) Copy sample s a

theorem actual_full_epoch_coefficients (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (a : SelectedIndex N sample Finset.univ)
    (r : PositivePairRates E) (t : ℝ≥0) :
    evaluate r t (polynomial (epochCoefficients N s a)) =
      (((sourceTimeKernel N r t s).map (projection N Finset.univ)) a).toReal := by
  rw [evaluate,eval_polynomial]
  exact fullCoefficients_actual N _ Copy sample s (by intro x i _; simp) a r t

end GProgram.G7.EffectiveFullEpochCoefficients
