import G7SparseRowProducts
import G7OriginalBoundaryPolynomial

/-!
# Sparse coefficients for actual conditional original boundaries

Contributor: Codex / lean_reuse_successor, 2026-10-10.
Reuses the actual inherited pulse/constant polynomial and boundary kernels.
The executable bodies retain literal admitted Code witnesses and enumerate only
CURRENT live owners at the supplied actual hybrid. True means parent1, with
one original gamma coordinate; a COMMON pulse uses the entering stored bit.
No new register is drawn and no complete Code carrier is enumerated.
Draft pending fresh kernel check, full audit and native fixture execution.
-/
namespace GProgram.G7.EffectiveBoundaryCoefficients
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceFiniteProjection
open GProgram.G7.EffectiveSourceEnumeration GProgram.G7.EffectivePopulationCoefficients
open GProgram.G7.EffectiveFullEpochCoefficients
open GProgram.G7.PopulationSelectedSupport GProgram.G7.SparseRowProducts
open GProgram.G7.OriginalBoundaryPolynomial
open scoped BigOperators NNReal

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

instance ownerEnumeration (s : State V E Copy) (v : V) : FinEnum (AtNode s v) := by
  unfold AtNode
  infer_instance

def pulseStateEffective {N : RootedBinary V E X} (H : GProgram.G2.OriginalHybridParents N)
    (s : State V E Copy) (coin : AtNode s H.hybrid → Bool) : State V E Copy :=
  let coins : Copy → Option Bool := fun l =>
    if h : l ∈ s.live ∧ s.location l = .node H.hybrid then some (coin ⟨l,h⟩) else none
  transport s (fun l =>
    if h : l ∈ s.live ∧ s.location l = .node H.hybrid then .edge (H.parent (coin ⟨l,h⟩))
    else s.location l) (.parentPulse H.hybrid coins)

lemma pulseStateEffective_eq {N : RootedBinary V E X} (H : GProgram.G2.OriginalHybridParents N)
    (s : State V E Copy) (coin : AtNode s H.hybrid → Bool) :
    pulseStateEffective H s coin = pulse H s coin := by
  unfold pulseStateEffective pulse
  apply congrArg₂ (transport s)
  · funext l
    by_cases h : l ∈ s.live ∧ s.location l = .node H.hybrid
    · simp only [dif_pos h]
    · simp only [dif_neg h]
  · apply congrArg (SourceEvent.parentPulse H.hybrid)
    funext l
    by_cases h : l ∈ s.live ∧ s.location l = .node H.hybrid
    · simp only [dif_pos h]
    · simp only [dif_neg h]

def pulseCodeEffective {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample)
    (coin : AtNode (sourceState s) H.hybrid → Bool) : Code N sample :=
  encodeActual N sample (pulseStateEffective H (sourceState s) coin) (by
    rw [pulseStateEffective_eq]
    exact pulse_source_valid H sample (state s) s.property coin)

lemma pulseCodeEffective_eq {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample)
    (coin : AtNode (sourceState s) H.hybrid → Bool) :
    pulseCodeEffective H s coin = pulseCode H s coin := by
  let left : {t : State V E Copy // SourceValid N sample t} :=
    ⟨pulseStateEffective H (sourceState s) coin,by
      rw [pulseStateEffective_eq]
      exact pulse_source_valid H sample (state s) s.property coin⟩
  let right : {t : State V E Copy // SourceValid N sample t} :=
    ⟨pulse H (state s) coin,pulse_source_valid H sample (state s) s.property coin⟩
  have h : left = right := Subtype.ext (pulseStateEffective_eq H (sourceState s) coin)
  exact congrArg (fun t : {s : State V E Copy // SourceValid N sample s} =>
    encodeActual N sample t.val t.property) h

def exitCodeEffective (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e : E) : Code N sample :=
  encodeActual N sample (exitEdge N (sourceState s) e)
    (exitEdge_source_valid N sample (state s) s.property e)

def ordinaryCodeEffective (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e : E) : Code N sample :=
  encodeActual N sample (enterEdge N (sourceState s) e)
    (enterEdge_source_valid N sample (state s) s.property e)

def rootCodeEffective (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : Code N sample :=
  encodeActual N sample (enterRoot N (sourceState s))
    (enterRoot_source_valid N sample (state s) s.property)

lemma exitCodeEffective_eq (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e : E) : exitCodeEffective N s e = exitCode N s e := rfl
lemma ordinaryCodeEffective_eq (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e : E) : ordinaryCodeEffective N s e = ordinaryCode N s e := rfl
lemma rootCodeEffective_eq (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : rootCodeEffective N s = rootCode N s := rfl

def bitSparse {I : Type*} (i : I) (bit : Bool) : Sparse I :=
  if bit then [([(i,1)],1)] else [([],1),([(i,1)],-1)]

lemma polynomial_bitSparse {I : Type*} (i : I) (bit : Bool) :
    polynomial (bitSparse i bit) = if bit then MvPolynomial.X i else 1-MvPolynomial.X i := by
  cases bit <;> simp [bitSparse,polynomial] <;> ring

def coinSparseList {I Site : Type*} (i : I) (coin : Site → Bool) : List Site → Sparse I
  | [] => single 1
  | owner::owners => product (bitSparse i (coin owner)) (coinSparseList i coin owners)

lemma polynomial_coinSparseList {I Site : Type*} (i : I) (coin : Site → Bool) (owners : List Site) :
    polynomial (coinSparseList i coin owners) =
      (owners.map fun owner => if coin owner then MvPolynomial.X i else 1-MvPolynomial.X i).prod := by
  induction owners with
  | nil => simp [coinSparseList,single,polynomial]
  | cons owner owners ih =>
      simp only [coinSparseList,polynomial_product,polynomial_bitSparse,ih,
        List.map_cons,List.prod_cons]

def coinSparse {I Site : Type*} [FinEnum Site] (i : I) (coin : Site → Bool) : Sparse I :=
  coinSparseList i coin (FinEnum.toList Site)

lemma embedAt_eq_eval₂ {I : Type*} (i : I) (p : Polynomial ℚ) :
    embedAt i p = Polynomial.eval₂ MvPolynomial.C (MvPolynomial.X i) p := by
  rw [Polynomial.eval₂_eq_sum]
  rfl

lemma polynomial_coinSparse {I Site : Type*} [Fintype Site] [FinEnum Site]
    (i : I) (coin : Site → Bool) :
    polynomial (coinSparse i coin) = embedAt i (coinPolynomial coin) := by
  classical
  rw [coinSparse,polynomial_coinSparseList]
  rw [((enumeration_perm Site).map
    (fun owner => if coin owner then MvPolynomial.X i else 1-MvPolynomial.X i)).prod_eq]
  rw [Finset.prod_map_toList,embedAt_eq_eval₂,coinPolynomial,Polynomial.eval₂_finsetProd]
  apply Finset.prod_congr rfl
  intro owner _
  cases coin owner <;> simp

def pulseRows {I : Type*} (i : I) {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample) : Rows I (Code N sample) :=
  (FinEnum.toList (AtNode (sourceState s) H.hybrid → Bool)).map fun coin =>
    (pulseCodeEffective H s coin,coinSparse i coin)

/-- The entire rational polynomial agrees with the actual inherited current-
owner pulse readout. Equal selected keys contribute their full literal sum. -/
theorem polynomial_pulseRows {I : Type*} (i : I)
    {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample)
    (a : SelectedIndex N sample Finset.univ) :
    polynomial (readRows (project N Finset.univ) (pulseRows i H s) a) =
      embedAt i (pulsePolynomial H s (project N Finset.univ) a) := by
  classical
  rw [pulseRows,readRows_map,polynomial_enumerate,embedAt_eq_eval₂,
    pulsePolynomial,Polynomial.eval₂_finsetSum]
  apply Finset.sum_congr rfl
  intro coin _
  rw [pulseCodeEffective_eq]
  by_cases h : project N Finset.univ (pulseCode H s coin) = a
  · rw [if_pos h,if_pos h,polynomial_coinSparse,embedAt_eq_eval₂]
    rfl
  · rw [if_neg h,if_neg h]
    simp [polynomial]

def pureRows {I A : Type*} (a : A) : Rows I A := [(a,single 1)]

lemma polynomial_pureRows {I A K : Type*} [DecidableEq K] (key : A → K)
    (a : A) (target : K) :
    polynomial (readRows key (pureRows (I := I) a) target) =
      constantPolynomial key a target := by
  classical
  by_cases h : key a = target <;> simp [pureRows,readRows,polynomial,single,constantPolynomial,h]

def commonRows {I : Type*} {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample) : Rows I (Code N sample) :=
  pureRows (pulseCodeEffective H s (fun _ => (sourceState s).register H.hybrid))

theorem polynomial_commonRows {I : Type*}
    {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample)
    (a : SelectedIndex N sample Finset.univ) :
    polynomial (readRows (project N Finset.univ) (commonRows (I := I) H s) a) =
      constantPolynomial (project N Finset.univ)
        (pulseCode H s (fun _ => (state s).register H.hybrid)) a := by
  rw [commonRows,polynomial_pureRows,pulseCodeEffective_eq]
  rfl

theorem pulseRows_register {I : Type*} (i : I)
    {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample)
    (row : Code N sample × Sparse I) (hrow : row ∈ pulseRows i H s) :
    row.1.val.register = s.val.register := by
  rcases List.mem_map.mp hrow with ⟨coin,_,he⟩
  rw [← he]
  rfl

theorem pulseRows_actual {I : Type*} (i : I)
    {N : RootedBinary V E X} {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample)
    (a : SelectedIndex N sample Finset.univ) (x : I → ℝ) (gamma : unitInterval)
    (hx : x i = (gamma : ℝ)) :
    value (readRows (project N Finset.univ) (pulseRows i H s) a) x =
      (((independentPulseKernel H gamma s).map (projection N Finset.univ)) a).toReal := by
  rw [← eval_polynomial,polynomial_pulseRows,embedAt_eval,hx]
  have h := actual_pulse_polynomial H s (project N Finset.univ) a gamma
  rw [show (project N Finset.univ : Code N sample → SelectedIndex N sample Finset.univ) =
      projection N Finset.univ from funext (project_eq N Finset.univ)] at h
  exact h

#print axioms pulseCodeEffective_eq
#print axioms polynomial_pulseRows
#print axioms polynomial_commonRows
#print axioms pulseRows_register
#print axioms pulseRows_actual
end GProgram.G7.EffectiveBoundaryCoefficients
