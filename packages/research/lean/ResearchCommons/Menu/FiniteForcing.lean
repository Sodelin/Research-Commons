import Mathlib.RingTheory.Polynomial.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-!
Algebraic finite-selection step of the accepted qualified-menu extension.
The original finite actual-rival size certificate and actual same-tuple shape
compiler must supply coverage. This module does not construct those suppliers,
claim an observation-only stopping algorithm, or add unauthorized test rows.
The selected polynomials are indexed by original legal observation coordinates.
-/
namespace ResearchCommons.Menu
set_option backward.isDefEq.respectTransparency false

/-- A polynomial family in one finite variable bank has a finite subset of its
ORIGINAL indices with the same simultaneous real zero set. -/
theorem finite_original_polynomial_equations
    {Query Variable : Type*} [Finite Variable]
    (equation : Query → MvPolynomial Variable ℝ) :
    ∃ selected : Finset Query, ∀ point : Variable → ℝ,
      (∀ q ∈ selected, MvPolynomial.eval point (equation q) = 0) →
      ∀ q, MvPolynomial.eval point (equation q) = 0 := by
  classical
  let P := MvPolynomial Variable ℝ
  have finite_span : (Submodule.span P (Set.range equation)).FG :=
    IsNoetherian.noetherian _
  obtain ⟨basis, in_range, same_span⟩ :=
    (Submodule.fg_span_iff_fg_span_finset_subset (R := P) (Set.range equation)).mp finite_span
  choose original index_exact using fun p : basis => in_range p.property
  let selected := basis.attach.image original
  refine ⟨selected, ?_⟩
  intro point agrees q
  let evaluate : P →+* ℝ := MvPolynomial.eval point
  have killed : Submodule.span P (Set.range equation) ≤
      (RingHom.ker evaluate : Submodule P P) := by
    rw [same_span]
    apply Submodule.span_le.mpr
    intro polynomial member
    change evaluate polynomial = 0
    calc
      evaluate polynomial = evaluate (equation (original ⟨polynomial, member⟩)) :=
        congrArg evaluate (index_exact ⟨polynomial, member⟩).symm
      _ = 0 := agrees _ (Finset.mem_image.mpr ⟨⟨polynomial, member⟩, by simp, rfl⟩)
  exact killed (Submodule.subset_span (Set.mem_range_self q))

/-- The same finite ORIGINAL coordinate subset forces an entire polynomial
response family to agree with one fixed target response, on any physical
parameter subset. No semialgebraicity of that subset is required. -/
theorem finite_original_polynomial_responses
    {Query Variable : Type*} [Finite Variable]
    (response : Query → MvPolynomial Variable ℝ) (target : Query → ℝ) :
    ∃ selected : Finset Query, ∀ point : Variable → ℝ,
      (∀ q ∈ selected, MvPolynomial.eval point (response q) = target q) →
      ∀ q, MvPolynomial.eval point (response q) = target q := by
  classical
  obtain ⟨selected, determines⟩ := finite_original_polynomial_equations
    (fun q => response q - MvPolynomial.C (target q))
  refine ⟨selected, ?_⟩
  intro point agrees q
  have difference := determines point (by
    intro i hi
    simp only [map_sub, MvPolynomial.eval_C, sub_eq_zero]
    exact agrees i hi) q
  simpa only [map_sub, MvPolynomial.eval_C, sub_eq_zero] using difference

/-- Qualified menu extension. The seed's ACTUAL matching rivals must all have
a chart from this finite shape family, and ONE point must represent ALL legal
responses of that rival. The conclusion selects only original menu indices.
Coverage is the original size/shape/compiler implication, not a desired
target-law equality. This is semantic finite existence, not effective stopping.
-/
theorem finite_qualified_menu_extension
    {Source Query Shape : Type*} [Fintype Shape]
    (Variable : Shape → Type*) [∀ shape, Finite (Variable shape)]
    (compiled : ∀ shape, Query → MvPolynomial (Variable shape) ℝ)
    (actual : Source → Query → ℝ) (target : Source) (admitted : Source → Prop)
    (seed : Finset Query)
    (coverage : ∀ source, admitted source →
      (∀ q ∈ seed, actual source q = actual target q) →
      ∃ shape, ∃ point : Variable shape → ℝ,
        ∀ q, actual source q = MvPolynomial.eval point (compiled shape q)) :
    ∃ certificate : Finset Query, seed ⊆ certificate ∧
      ∀ source, admitted source →
        (∀ q ∈ certificate, actual source q = actual target q) →
        ∀ q, actual source q = actual target q := by
  classical
  choose selected determines using fun shape =>
    finite_original_polynomial_responses (compiled shape) (actual target)
  refine ⟨seed ∪ Finset.univ.biUnion selected, Finset.subset_union_left, ?_⟩
  intro source valid agrees
  obtain ⟨shape, point, represented⟩ := coverage source valid
    (fun q hq => agrees q (Finset.mem_union_left _ hq))
  intro q
  rw [represented q]
  apply determines shape point _ q
  intro i hi
  have selected_in : i ∈ seed ∪ Finset.univ.biUnion selected :=
    Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨shape, Finset.mem_univ _, hi⟩)
  simpa only [represented i] using agrees i selected_in

end ResearchCommons.Menu
