import G5FrozenTriplePolynomialKernel
import G5UnknownRateSupport

/-!
# Repeated-rate frozen triple germ and occupancy identification

Contributor: CLOUD-G5-20261007T155725Z, Codex, 2026-10-07.
Reuses Astra's polynomial kernel as corrected by Codex and dot's intrinsic
finite-exponential germ theorem. Compiler evidence is external to this source.
Internal Lean takeover derivative, 2026-10-07: repairs the actually recovered
Fin numeral and pinned Finsupp API elaboration errors; statements unchanged.

This module derives exponential substitution, positive-rate finite-mixture
limits and germ uniqueness between different finite hidden representations.
Rates may repeat and weights need not factor. The missing identity with the
actual conditional genealogy law is NOT a hypothesis hidden in a source type.
This is a frozen analytic bridge, not full original-network observability.
-/
namespace GProgram.G5.FrozenTripleAnalyticSupport
set_option backward.isDefEq.respectTransparency false
open Filter GProgram.G5.FrozenTriplePolynomialKernel GProgram.G5.ExponentialGerm
open scoped BigOperators Topology

noncomputable def expParameter (rate u : ℝ) : ℝ := Real.exp (-rate * u)

lemma exp_parameter_bounds {rate u : ℝ} (hr : 0 < rate) (hu : 0 ≤ u) :
    0 ≤ expParameter rate u ∧ expParameter rate u ≤ 1 := by
  refine ⟨(Real.exp_pos _).le, ?_⟩
  exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hr.le) hu)

lemma exp_parameter_decay {rate : ℝ} (hr : 0 < rate) :
    Tendsto (expParameter rate) atTop (𝓝 0) := by
  exact Real.tendsto_exp_atBot.comp
    ((tendsto_const_mul_atBot_of_neg (neg_neg_of_pos hr)).mpr tendsto_id)

noncomputable def linearCoefficient (occupancy gene : Fin 5) : ℝ :=
  if occupancy = 0 then 0
  else if occupancy = 4 then
    if gene = 0 then 0 else if gene = 4 then -(3 / 2) else 1 / 2
  else if gene = 0 then 1 else if gene = occupancy then -1 else 0

noncomputable def cubicCoefficient (occupancy gene : Fin 5) : ℝ :=
  if occupancy = 4 then
    if gene = 0 then 1 else if gene = 4 then 1 / 2 else -(1 / 2)
  else 0

lemma row_polynomial (q : ℝ) (occupancy gene : Fin 5) :
    row q occupancy gene = row 0 occupancy gene +
      linearCoefficient occupancy gene * q + cubicCoefficient occupancy gene * q ^ 3 := by
  fin_cases occupancy <;> fin_cases gene <;>
    norm_num [row, linearCoefficient, cubicCoefficient, discrete3, pair3, together3,
      Fin.ext_iff] <;> ring

/-- A real exponent map gathers repeated rates and repeated cross-seed
exponents intrinsically. No injective hidden-rate presentation is required. -/
noncomputable def rowCoefficients (rate : ℝ) (occupancy gene : Fin 5) : ℝ →₀ ℝ :=
  Finsupp.single 0 (row 0 occupancy gene) +
    Finsupp.single (-rate) (linearCoefficient occupancy gene) +
    Finsupp.single (-3 * rate) (cubicCoefficient occupancy gene)

lemma row_coefficients_evaluation (rate u : ℝ) (occupancy gene : Fin 5) :
    finiteExpSum (rowCoefficients rate occupancy gene) u =
      row (expParameter rate u) occupancy gene := by
  have hc : (Real.exp (-rate * u)) ^ 3 = Real.exp ((-3 * rate) * u) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [row_polynomial]
  unfold rowCoefficients finiteExpSum expParameter
  simp only [Finsupp.sum_add_index' (h := fun (exponent coeff : ℝ) => coeff * Real.exp (exponent * u))
      (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _),
    Finsupp.sum_single_index (h := fun (exponent coeff : ℝ) => coeff * Real.exp (exponent * u))
      (zero_mul _),
    zero_mul, Real.exp_zero, mul_one, hc]

section FiniteMixture
variable {Seed : Type*} [Fintype Seed]

noncomputable def frozenMixture (weight rate : Seed → ℝ) (occupancy : Seed → Fin 5)
    (u : ℝ) (gene : Fin 5) : ℝ :=
  mixture weight occupancy (fun a => expParameter (rate a) u) gene

/-- Use scalar multiplication on coefficient values, not multiplication of
finitely-supported maps. This preserves the real exponent carrier. -/
noncomputable def frozenCoefficients (weight rate : Seed → ℝ)
    (occupancy : Seed → Fin 5) (gene : Fin 5) : ℝ →₀ ℝ :=
  ∑ a, weight a • rowCoefficients (rate a) (occupancy a) gene

lemma frozen_coefficients_evaluation (weight rate : Seed → ℝ)
    (occupancy : Seed → Fin 5) (u : ℝ) (gene : Fin 5) :
    finiteExpSum (frozenCoefficients weight rate occupancy gene) u =
      frozenMixture weight rate occupancy u gene := by
  classical
  unfold frozenCoefficients frozenMixture mixture finiteExpSum
  rw [← Finsupp.sum_finsetSum_index (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finsupp.sum_smul_index (fun _ => zero_mul _)]
  change (rowCoefficients (rate a) (occupancy a) gene).sum
    (fun exponent coeff => (weight a * coeff) * Real.exp (exponent * u)) = _
  simp_rw [mul_assoc]
  rw [← Finsupp.mul_sum]
  exact congrArg (fun x => weight a * x)
    (row_coefficients_evaluation (rate a) u (occupancy a) gene)

lemma frozen_mixture_limit (weight rate : Seed → ℝ) (occupancy : Seed → Fin 5)
    (hr : ∀ a, 0 < rate a) (gene : Fin 5) :
    Tendsto (fun u => frozenMixture weight rate occupancy u gene) atTop
      (𝓝 (occupancyMass weight occupancy gene)) := by
  classical
  have h : Tendsto (fun u => ∑ a, weight a * row (expParameter (rate a) u) (occupancy a) gene)
      atTop (𝓝 (∑ a, weight a * row 0 (occupancy a) gene)) := by
    apply tendsto_finsetSum
    intro a _
    exact tendsto_const_nhds.mul
      (((row_continuous (occupancy a) gene).tendsto 0).comp (exp_parameter_decay (hr a)))
  simpa [frozenMixture, mixture, occupancyMass, row_endpoint, eq_comm] using h

end FiniteMixture

/-- The finite seed carriers, weights, rates and occupancy presentations on
the two sides may differ. Their observed right germs uniquely fix the frozen
continuation. This statement assumes equality of FROZEN germs only. -/
theorem frozen_mixtures_eq_of_right_germ
    {A B : Type*} [Fintype A] [Fintype B]
    (w r : A → ℝ) (p : A → Fin 5) (v s : B → ℝ) (q : B → Fin 5)
    {ε : ℝ} (hε : 0 < ε)
    (hg : ∀ gene u, 0 ≤ u → u < ε →
      frozenMixture w r p u gene = frozenMixture v s q u gene) :
    ∀ gene u, frozenMixture w r p u gene = frozenMixture v s q u gene := by
  intro gene u
  have hc := finite_coefficients_eq_of_right_germ
    (frozenCoefficients w r p gene) (frozenCoefficients v s q gene) hε
    (fun u hu hlt => by simpa only [frozen_coefficients_evaluation] using hg gene u hu hlt)
  rw [← frozen_coefficients_evaluation, hc, frozen_coefficients_evaluation]

theorem occupancy_masses_eq_of_right_germ
    {A B : Type*} [Fintype A] [Fintype B]
    (w r : A → ℝ) (p : A → Fin 5) (v s : B → ℝ) (q : B → Fin 5)
    (hr : ∀ a, 0 < r a) (hs : ∀ b, 0 < s b)
    {ε : ℝ} (hε : 0 < ε)
    (hg : ∀ gene u, 0 ≤ u → u < ε →
      frozenMixture w r p u gene = frozenMixture v s q u gene) :
    ∀ gene, occupancyMass w p gene = occupancyMass v q gene := by
  intro gene
  have heq := frozen_mixtures_eq_of_right_germ w r p v s q hε hg gene
  have hfun : (fun u => frozenMixture w r p u gene) =
      (fun u => frozenMixture v s q u gene) := funext heq
  have hleft := frozen_mixture_limit w r p hr gene
  rw [hfun] at hleft
  exact tendsto_nhds_unique hleft (frozen_mixture_limit v s q hs gene)

theorem occupancy_support_eq_of_right_germ
    {A B : Type*} [Fintype A] [Fintype B]
    (w r : A → ℝ) (p : A → Fin 5) (v s : B → ℝ) (q : B → Fin 5)
    (hw : ∀ a, 0 < w a) (hv : ∀ b, 0 < v b)
    (hr : ∀ a, 0 < r a) (hs : ∀ b, 0 < s b)
    {ε : ℝ} (hε : 0 < ε)
    (hg : ∀ gene u, 0 ≤ u → u < ε →
      frozenMixture w r p u gene = frozenMixture v s q u gene) :
    ∀ gene, (∃ a, p a = gene) ↔ ∃ b, q b = gene := by
  intro gene
  rw [← occupancy_mass_positive_iff w p hw, ← occupancy_mass_positive_iff v q hv,
    occupancy_masses_eq_of_right_germ w r p v s q hr hs hε hg gene]

#print axioms exp_parameter_bounds
#print axioms exp_parameter_decay
#print axioms row_polynomial
#print axioms row_coefficients_evaluation
#print axioms frozen_coefficients_evaluation
#print axioms frozen_mixture_limit
#print axioms frozen_mixtures_eq_of_right_germ
#print axioms occupancy_masses_eq_of_right_germ
#print axioms occupancy_support_eq_of_right_germ
end GProgram.G5.FrozenTripleAnalyticSupport

