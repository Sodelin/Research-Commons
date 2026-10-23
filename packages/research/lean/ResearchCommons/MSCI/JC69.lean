import ResearchCommons.MSCI.KilledClocks
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-! The retained clock-JC observation channel, downstream formalization.
The alphabet and character group are BOTH (Z/2)^2 with literal bit numbering.
These are the actual normalized branch probabilities, not a desired channel
identity passed as a field. Timed-genealogy support, whole-tree/locus assembly
and the complete bounded observation theorem remain separate. -/
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 3000000
namespace ResearchCommons.MSCI.JC69
open scoped BigOperators NNReal
abbrev Base := Fin 2 × Fin 2

def number (a : Base) : Fin 4 :=
  ⟨a.1.val + 2*a.2.val, by have h1 := a.1.isLt; have h2 := a.2.isLt; omega⟩

def ofNumber : Fin 4 → Base := ![(0,0),(1,0),(0,1),(1,1)]

theorem ofNumber_number (a : Base) : ofNumber (number a) = a := by
  rcases a with ⟨a,b⟩
  fin_cases a <;> fin_cases b <;> rfl

theorem number_ofNumber (i : Fin 4) : number (ofNumber i) = i := by
  fin_cases i <;> rfl

def bitSign (k a : Fin 2) : ℝ := if k = 1 ∧ a = 1 then -1 else 1

def character (k a : Base) : ℝ := bitSign k.1 a.1 * bitSign k.2 a.2

theorem character_zero (a : Base) : character 0 a = 1 := by
  simp [character, bitSign]

theorem character_sq (k a : Base) : character k a * character k a = 1 := by
  rcases k with ⟨k0,k1⟩
  rcases a with ⟨a0,a1⟩
  fin_cases k0 <;> fin_cases k1 <;> fin_cases a0 <;> fin_cases a1 <;>
    norm_num [character, bitSign]

/-- Adding current-block charges multiplies their characters. -/
theorem character_add (k l a : Base) :
    character (k+l) a = character k a * character l a := by
  rcases k with ⟨k0,k1⟩
  rcases l with ⟨l0,l1⟩
  rcases a with ⟨a0,a1⟩
  fin_cases k0 <;> fin_cases k1 <;> fin_cases l0 <;> fin_cases l1 <;>
    fin_cases a0 <;> fin_cases a1 <;> norm_num [character, bitSign, Fin.add_def]

/-- Uniform finite-panel character product. No genealogy/copy-size cap is
introduced by the four-element alphabet. -/
theorem character_sum {I : Type*} [DecidableEq I] (s : Finset I)
    (charges : I → Base) (a : Base) :
    character (∑ i ∈ s, charges i) a = ∏ i ∈ s, character (charges i) a := by
  induction s using Finset.induction_on with
  | empty => simp [character_zero]
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, Finset.prod_insert hi, character_add, ih]

/-- The charge of an actual complete CURRENT tree is the product character
of its original sampled descendants, including arbitrary opaque subtrees. -/
theorem actual_current_tree_character
    {V E Copy Site : Type*} [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
    [Fintype V] [Fintype E] [Fintype Copy] [Fintype Site]
    (s : GProgram.SourceForest.State V E Copy)
    (characters : Copy → Site → Base) (l : Copy) (j : Site) (a : Base) :
    character (ResearchCommons.MSCI.currentCharge s characters l j) a =
      ∏ x ∈ (s.genealogy l).leaves, character (characters x j) a := by
  exact character_sum _ (fun x => characters x j) a

def probability (x : ℝ) (a b : Base) : ℝ :=
  if a = b then (1+3*x)/4 else (1-x)/4

theorem probability_nonnegative {x : ℝ} (hx : 0 ≤ x) (hx1 : x ≤ 1) (a b : Base) :
    0 ≤ probability x a b := by
  by_cases h : a = b
  · rw [probability, if_pos h]
    nlinarith
  · rw [probability, if_neg h]
    nlinarith

theorem probability_row_sum (x : ℝ) (a : Base) :
    (∑ b : Base, probability x a b) = 1 := by
  rcases a with ⟨a0,a1⟩
  fin_cases a0 <;> fin_cases a1 <;>
    norm_num [probability, Fintype.sum_prod_type, Fin.sum_univ_two] <;> ring

theorem probability_symmetric (x : ℝ) (a b : Base) :
    probability x a b = probability x b a := by
  simp only [probability, eq_comm]

theorem probability_one (a b : Base) :
    probability 1 a b = if a = b then 1 else 0 := by
  by_cases h : a = b <;> norm_num [probability, h]

/-- Exact polynomial semigroup, including endpoint survivals zero and one. -/
theorem probability_semigroup (x y : ℝ) (a c : Base) :
    (∑ b : Base, probability x a b * probability y b c) = probability (x*y) a c := by
  rcases a with ⟨a0,a1⟩
  rcases c with ⟨c0,c1⟩
  fin_cases a0 <;> fin_cases a1 <;> fin_cases c0 <;> fin_cases c1 <;>
    norm_num [probability, Fintype.sum_prod_type, Fin.sum_univ_two] <;> ring

/-- The trivial Fourier charge has eigenvalue one; all three nontrivial
charges have eigenvalue x. This is an identity of the constructed kernel. -/
theorem fourier_transfer (x : ℝ) (a k : Base) :
    (∑ b : Base, probability x a b * character k b) =
      (if k = 0 then 1 else x) * character k a := by
  rcases a with ⟨a0,a1⟩
  rcases k with ⟨k0,k1⟩
  fin_cases a0 <;> fin_cases a1 <;> fin_cases k0 <;> fin_cases k1 <;>
    norm_num [probability, character, bitSign, Fintype.sum_prod_type, Fin.sum_univ_two] <;> ring

/-- Actual normalized PMF for a branch with an admitted survival coordinate. -/
def kernel (x : Set.Icc (0 : ℝ) 1) (a : Base) : PMF Base :=
  PMF.ofFintype (fun b => ENNReal.ofReal (probability x a b)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg
      (fun b _ => probability_nonnegative x.property.1 x.property.2 a b),
      probability_row_sum]
    simp)

theorem kernel_probability (x : Set.Icc (0 : ℝ) 1) (a b : Base) :
    (kernel x a b).toReal = probability x a b := by
  change (ENNReal.ofReal (probability x a b)).toReal = _
  exact ENNReal.toReal_ofReal (probability_nonnegative x.property.1 x.property.2 a b)

/-- Known normalized clock: diagonal generator -1, off-diagonal 1/3. -/
def clockSurvival (t : ℝ≥0) : Set.Icc (0 : ℝ) 1 :=
  ⟨Real.exp (-((4/3 : ℝ)*t)), (Real.exp_pos _).le,
    Real.exp_le_one_iff.mpr (by have ht := t.property; nlinarith)⟩

/-- A strictly positive survival has an actual finite nonnegative branch
time. The endpoint one gives time zero; no independent fit is introduced. -/
def timeOfSurvival (x : Set.Ioc (0 : ℝ) 1) : ℝ≥0 :=
  ⟨-((3/4 : ℝ)) * Real.log x, by
    have hl := Real.log_nonpos x.property.1.le x.property.2
    nlinarith⟩

theorem clock_survival_timeOfSurvival (x : Set.Ioc (0 : ℝ) 1) :
    (clockSurvival (timeOfSurvival x) : ℝ) = x := by
  change Real.exp (-((4/3 : ℝ) * (-((3/4 : ℝ)) * Real.log x))) = x
  rw [show -((4/3 : ℝ) * (-((3/4 : ℝ)) * Real.log x)) = Real.log x by ring]
  exact Real.exp_log x.property.1

def clockKernel (t : ℝ≥0) : Base → PMF Base := kernel (clockSurvival t)

theorem normalized_generator (a b : Base) :
    HasDerivAt (fun t : ℝ => probability (Real.exp ((-(4/3 : ℝ))*t)) a b)
      (if a = b then (-1 : ℝ) else 1/3) 0 := by
  have he : HasDerivAt (fun t : ℝ => Real.exp ((-(4/3 : ℝ))*t)) (-(4/3 : ℝ)) 0 := by
    simpa only [id_eq, mul_zero, Real.exp_zero, one_mul, mul_one] using
      ((hasDerivAt_id (0 : ℝ)).const_mul (-(4/3 : ℝ))).exp
  by_cases h : a = b
  · have hd := ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).add
        (he.const_mul (3 : ℝ))).div_const 4
    have hnum : ((0 : ℝ) + 3 * (-(4/3 : ℝ))) / 4 = -1 := by norm_num
    rw [hnum] at hd
    simp only [probability, if_pos h]
    convert hd using 1 <;> rfl
  · have hd := ((hasDerivAt_const (0 : ℝ) (1 : ℝ)).sub he).div_const 4
    have hnum : ((0 : ℝ) - (-(4/3 : ℝ))) / 4 = 1/3 := by norm_num
    rw [hnum] at hd
    simp only [probability, if_neg h]
    convert hd using 1 <;> rfl

/-- Two conditionally independent branches from ONE uniform ancestral base.
This is the explicit common-root sum, not a product of separate genealogies. -/
theorem uniform_root_pair_probability (x : ℝ) (b c : Base) :
    (∑ a : Base, (1/4 : ℝ) * probability x a b * probability x a c) =
      (1/4 : ℝ) * probability (x*x) b c := by
  simp_rw [mul_assoc]
  rw [← Finset.mul_sum]
  congr 1
  calc
    (∑ a : Base, probability x a b * probability x a c) =
        ∑ a : Base, probability x b a * probability x a c := by
      apply Finset.sum_congr rfl
      intro a _
      rw [probability_symmetric x a b]
    _ = _ := probability_semigroup x x b c

theorem pair_fourier (x : ℝ) (k : Base) :
    (∑ b : Base, ∑ c : Base,
      ((1/4 : ℝ) * probability (x*x) b c) * character k b * character k c) =
      if k = 0 then 1 else x*x := by
  rcases k with ⟨k0,k1⟩
  fin_cases k0 <;> fin_cases k1 <;>
    norm_num [probability, character, bitSign, Fintype.sum_prod_type, Fin.sum_univ_two] <;> ring

/-- Actual equal-branch clock-JC pair correlation at MRCA age t. -/
theorem clock_pair_correlation (t : ℝ≥0) (k : Base) (hk : k ≠ 0) :
    (∑ b : Base, ∑ c : Base,
      ((1/4 : ℝ) * probability
        ((clockSurvival t : ℝ)*(clockSurvival t : ℝ)) b c) *
        character k b * character k c) = Real.exp (-((8/3 : ℝ)*t)) := by
  rw [pair_fourier, if_neg hk]
  change Real.exp (-((4/3 : ℝ)*t)) * Real.exp (-((4/3 : ℝ)*t)) = _
  rw [← Real.exp_add]
  congr 1
  ring

theorem pair_time_decoder (t : ℝ≥0) :
    -((3/8 : ℝ)) * Real.log (Real.exp (-((8/3 : ℝ)*t))) = t := by
  rw [Real.log_exp]
  ring

/-- This instantiates the accepted ACTUAL source merger/charge component on
the JC character group. It does not assume the complete JC source law. -/
theorem actual_jc_killed_rate_strict_merger
    {V E Copy X Site : Type*} [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
    [Fintype V] [Fintype E] [Fintype Copy] [Fintype X] [Fintype Site]
    (N : Nanuq.Source.RootedBinary V E X)
    {sample : Copy → X}
    (r : UnifiedLean.Source.NativePairClockLaw.PositivePairRates E)
    (characters : Copy → Site → Base)
    (s : UnifiedLean.Source.UniformizedSourceStep.Code N sample)
    (p : UnifiedLean.Source.UniformizedSourceStep.Choice N s) :
    ResearchCommons.MSCI.killedRate N r (4/3) characters
        (UnifiedLean.Source.UniformizedSourceStep.stepDestination N s (some p)) <
      ResearchCommons.MSCI.killedRate N r (4/3) characters s :=
  ResearchCommons.MSCI.actual_killedRate_strict_merger N r (4/3) (by norm_num)
    characters s p

end ResearchCommons.MSCI.JC69
