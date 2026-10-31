import ResearchCommons.MSCI.JC69CanonicalWeightedSum
import Mathlib.Data.List.GetD

/-! Query-independent actual path-position indices and replicated-character
holding rates. UNCOMPILED candidate, dot (OpenAI), 31 October 2026.
Original copies and the actual initial Code stay fixed. This is not the
common-denominator polynomial theorem or whole-calendar representation. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69CommonCountIndex
open MeasureTheory Set Nanuq.Source
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69Occupation ResearchCommons.MSCI.JC69WeightedTrace
open ResearchCommons.MSCI.JC69EndpointWeight ResearchCommons.MSCI.JC69ResolvedRealVolterra
open ResearchCommons.MSCI.JC69OrderedPathExpansion ResearchCommons.MSCI.JC69CanonicalPathCount
open ResearchCommons.MSCI.JC69CanonicalWeightedSum
open scoped Classical BigOperators NNReal ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- No rate, site count, character or horizon occurs in this index type. -/
abbrev CommonTermIndex {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (fuel : ℕ) (s : Code N sample) :=
  Σ h : CanonicalPath e N fuel s, Fin (pathLength N fuel s h.val + 1)

def commonTermEquiv {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (fuel : ℕ) (s : Code N sample) :
    CommonTermIndex e N fuel s ≃ CanonicalTermIndex e N r L q fuel s :=
  Equiv.sigmaCongrRight (fun h => finCongr (pathTerms_size N r L q fuel s h.val).symm)

def commonRate {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (fuel : ℕ) (s : Code N sample) (i : CommonTermIndex e N fuel s) : ℝ :=
  termRate e N r L q fuel s (commonTermEquiv e N r L q fuel s i)

def commonCoefficient {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (fuel : ℕ) (s : Code N sample) (target : BlockPopulationObservation Copy V E)
    (i : CommonTermIndex e N fuel s) : ℝ :=
  termCoefficient e N r L q fuel s target (commonTermEquiv e N r L q fuel s i)

theorem actual_common_index_expansion {n : ℕ} (e : Copy ≃ Fin n)
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (L : ℕ) (q : Fin L → Copy → Base) (fuel : ℕ) (s : Code N sample)
    (T : ℝ≥0) (target : BlockPopulationObservation Copy V E) :
    (actualResolvedWeight N r L q fuel s T target).toReal =
      ∑ i : CommonTermIndex e N fuel s,
        commonCoefficient e N r L q fuel s target i *
          Real.exp (-commonRate e N r L q fuel s i*(T:ℝ)) := by
  rw [actual_resolved_canonical_exponential_sum e]
  exact ((commonTermEquiv e N r L q fuel s).sum_comp
    (fun i => termCoefficient e N r L q fuel s target i *
      Real.exp (-termRate e N r L q fuel s i*(T:ℝ)))).symm

theorem actual_common_index_card_le [Nonempty Copy]
    (e : Copy ≃ Fin (Fintype.card Copy)) (N : RootedBinary V E X)
    {sample : Copy → X} (fuel : ℕ) (s : Code N sample) :
    Fintype.card (CommonTermIndex e N fuel s) ≤
      Fintype.card Copy * ∑ k ∈ Finset.range (Fintype.card Copy), ((Fintype.card Copy).choose 2)^k := by
  simp only [CommonTermIndex,Fintype.card_sigma,Fintype.card_fin]
  calc
    (∑ h : CanonicalPath e N fuel s, (pathLength N fuel s h.val + 1)) ≤
        ∑ _h : CanonicalPath e N fuel s, Fintype.card Copy :=
      Finset.sum_le_sum (fun h _ => pathLength_lt_original_copies N fuel s h.val)
    _ = Fintype.card (CanonicalPath e N fuel s) * Fintype.card Copy := by simp; rfl
    _ ≤ (∑ k ∈ Finset.range (Fintype.card Copy), ((Fintype.card Copy).choose 2)^k) * Fintype.card Copy :=
      Nat.mul_le_mul_right _ (actual_canonical_path_card_le e N fuel s)
    _ = _ := Nat.mul_comm _ _

/-- Actual states along the ordered path, including its initial and final states.
The list is independent of every query parameter and of the rate bank. -/
def pathStates (N : RootedBinary V E X) {sample : Copy → X} :
    (fuel : ℕ) → (s : Code N sample) → OrderedPath N fuel s → List (Code N sample)
  | 0, s, _ => [s]
  | _+1, s, .inl _ => [s]
  | fuel+1, s, .inr ⟨p,h⟩ => s :: pathStates N fuel (stepDestination N s (some p)) h

lemma pathStates_length (N : RootedBinary V E X) {sample : Copy → X}
    (fuel : ℕ) (s : Code N sample) (h : OrderedPath N fuel s) :
    (pathStates N fuel s h).length = pathLength N fuel s h + 1 := by
  induction fuel generalizing s with
  | zero => rfl
  | succ fuel ih =>
    cases h with
    | inl h => rfl
    | inr h => obtain ⟨p,h⟩ := h; simp [pathStates,pathLength,ih,Nat.add_comm,Nat.add_assoc]

lemma actual_path_rate_list (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (fuel : ℕ) (s : Code N sample) (h : OrderedPath N fuel s) :
    List.ofFn (pathTerms N r L q fuel s h).rate =
      (pathStates N fuel s h).map (holdingRate N r L q) := by
  induction fuel generalizing s with
  | zero => simp [pathTerms,singletonTerms,pathStates,List.ofFn_succ]
  | succ fuel ih =>
    cases h with
    | inl h => simp [pathTerms,singletonTerms,pathStates,List.ofFn_succ]
    | inr h =>
      obtain ⟨p,h⟩ := h
      simp [pathTerms,prependTerms,pathStates,List.ofFn_succ,ih]

/-- The default is never read at a CommonTermIndex position. -/
def commonState {n : ℕ} (e : Copy ≃ Fin n) (N : RootedBinary V E X)
    {sample : Copy → X} (fuel : ℕ) (s : Code N sample)
    (i : CommonTermIndex e N fuel s) : Code N sample :=
  (pathStates N fuel s i.1.val).getD i.2.val s

theorem actual_common_rate_state {n : ℕ} (e : Copy ≃ Fin n)
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (L : ℕ) (q : Fin L → Copy → Base) (fuel : ℕ) (s : Code N sample)
    (i : CommonTermIndex e N fuel s) :
    commonRate e N r L q fuel s i = holdingRate N r L q (commonState e N fuel s i) := by
  have hi : i.2.val < (pathTerms N r L q fuel s i.1.val).size := by
    rw [pathTerms_size]; exact i.2.isLt
  have he := congrArg (fun xs : List ℝ => xs.getD i.2.val (holdingRate N r L q s))
    (actual_path_rate_list N r L q fuel s i.1.val)
  rw [List.getD_map] at he
  simpa [commonRate,termRate,commonTermEquiv,Equiv.sigmaCongrRight,commonState,
    List.getD_eq_getElem?_getD,List.getElem?_ofFn,hi] using he

variable {A : Type*} [Fintype A]

/-- Replicate SITES of each original-copy character, never copies or lineages. -/
abbrev ReplicaSites (v : A → ℕ) := Σ a : A, Fin (v a)

def replicaEquiv (v : A → ℕ) : Fin (∑ a, v a) ≃ ReplicaSites v :=
  (finCongr (by simp [ReplicaSites] : (∑ a, v a) = Fintype.card (ReplicaSites v))).trans
    (Fintype.equivFin (ReplicaSites v)).symm

def replicatedQ (v : A → ℕ) (chi : A → Copy → Base) : Fin (∑ a, v a) → Copy → Base :=
  fun j => chi ((replicaEquiv v j).1)

theorem actual_replicated_locusKill (N : RootedBinary V E X) {sample : Copy → X}
    (v : A → ℕ) (chi : A → Copy → Base) (s : Code N sample) :
    locusKill N (∑ a, v a) (replicatedQ v chi) s =
      (4/3:ℝ) * ∑ a, (v a:ℝ) * codeCharge N (chi a) s := by
  unfold locusKill replicatedQ
  rw [(replicaEquiv v).sum_comp (fun j => codeCharge N (chi j.1) s)]
  simp [ReplicaSites,Fintype.sum_sigma]

theorem actual_replicated_common_rate {n : ℕ} (e : Copy ≃ Fin n)
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (v : A → ℕ) (chi : A → Copy → Base) (fuel : ℕ) (s : Code N sample)
    (i : CommonTermIndex e N fuel s) :
    commonRate e N r (∑ a, v a) (replicatedQ v chi) fuel s i =
      (totalRate N r (commonState e N fuel s i) : ℝ) +
        (4/3:ℝ) * ∑ a, (v a:ℝ) * codeCharge N (chi a) (commonState e N fuel s i) := by
  rw [actual_common_rate_state,holdingRate,actual_replicated_locusKill]

/-- A fixed actual path-position has positive multiplicative bases, even
when rates/bases coincide across other paths or some counts vanish. -/
theorem actual_replicated_exponential {n : ℕ} (e : Copy ≃ Fin n)
    (N : RootedBinary V E X) {sample : Copy → X} (r : PositivePairRates E)
    (v : A → ℕ) (chi : A → Copy → Base) (fuel : ℕ) (s : Code N sample)
    (i : CommonTermIndex e N fuel s) (T : ℝ) :
    Real.exp (-commonRate e N r (∑ a, v a) (replicatedQ v chi) fuel s i*T) =
      Real.exp (-(totalRate N r (commonState e N fuel s i):ℝ)*T) *
        ∏ a, (Real.exp (-((4/3:ℝ)*codeCharge N (chi a) (commonState e N fuel s i))*T))^(v a) := by
  rw [actual_replicated_common_rate]
  have halg : -((totalRate N r (commonState e N fuel s i):ℝ) +
      (4/3:ℝ)*∑ a, (v a:ℝ)*codeCharge N (chi a) (commonState e N fuel s i))*T =
      -(totalRate N r (commonState e N fuel s i):ℝ)*T +
        ∑ a, (v a:ℝ)*(-((4/3:ℝ)*codeCharge N (chi a) (commonState e N fuel s i))*T) := by
    rw [neg_add, add_mul]
    congr 1
    rw [neg_mul, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    ring
  rw [halg,Real.exp_add,Real.exp_sum]
  congr 1
  apply Finset.prod_congr rfl
  intro a _
  rw [Real.exp_nat_mul]

#print axioms actual_common_index_expansion
#print axioms actual_common_index_card_le
#print axioms actual_common_rate_state
#print axioms actual_replicated_locusKill
#print axioms actual_replicated_common_rate
#print axioms actual_replicated_exponential
end ResearchCommons.MSCI.JC69CommonCountIndex
