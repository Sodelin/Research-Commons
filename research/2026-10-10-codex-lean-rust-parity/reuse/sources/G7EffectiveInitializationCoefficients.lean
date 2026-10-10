import G7EffectiveBoundaryCoefficients
import G7OriginalInitializationPolynomial
import Mathlib.Algebra.MvPolynomial.Rename

/-!
# Executable once-drawn original-register initialization

Contributor: Codex / lean_reuse_successor, 2026-10-10.
Reuses the unchanged actual initial State, encodeActual and original register
polynomial. The complete original hybrid carrier is enumerated once, including
when Copy is empty. Nonhybrid register positions are false, and true has the
original parent1 probability. No Code or selected-index universe is scanned.
This is a new executable composition, not a new initialization law theorem.
Draft pending fresh kernel checking and complete audit by the sole scheduler.
-/
namespace GProgram.G7.EffectiveInitializationCoefficients
open Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceNaturalInitialization
open GProgram.G7.EffectiveSourceEnumeration GProgram.G7.EffectivePopulationCoefficients
open GProgram.G7.EffectiveFullEpochCoefficients
open GProgram.G7.SparseRowProducts GProgram.G7.EffectiveBoundaryCoefficients
open GProgram.G7.OriginalInitializationPolynomial
open scoped BigOperators

variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype V] [Fintype E] [Fintype Copy] [Fintype X]
variable [FinEnum V] [FinEnum E] [FinEnum Copy]

def hybridDecidable (N : RootedBinary V E X) (v : V) : Decidable (N.graph.IsHybrid v) := by
  unfold EdgeGraph.IsHybrid
  infer_instance

instance hybridEnumeration (N : RootedBinary V E X) : FinEnum (Hybrid N) := by
  letI : DecidablePred N.graph.IsHybrid := hybridDecidable N
  exact inferInstanceAs (FinEnum {v : V // N.graph.IsHybrid v})

def originalRegisterEffective (N : RootedBinary V E X) (coin : Hybrid N → Bool) : V → Bool :=
  letI : DecidablePred N.graph.IsHybrid := hybridDecidable N
  fun v => if h : N.graph.IsHybrid v then coin ⟨v,h⟩ else false

lemma originalRegisterEffective_eq (N : RootedBinary V E X) (coin : Hybrid N → Bool) :
    originalRegisterEffective N coin = originalRegister N coin := by
  classical
  funext v
  by_cases h : N.graph.IsHybrid v
  · simp only [originalRegisterEffective,originalRegister,dif_pos h]
  · simp only [originalRegisterEffective,originalRegister,dif_neg h]

def initialCodeEffective (N : RootedBinary V E X) (sample : Copy → X)
    (register : V → Bool) : Code N sample :=
  encodeActual N sample (initial N sample register) (initial_source_valid N sample register)

lemma initialCodeEffective_eq (N : RootedBinary V E X) (sample : Copy → X)
    (register : V → Bool) : initialCodeEffective N sample register = initialCode N sample register := by
  apply Subtype.ext
  rfl

def registerSparseList {I Site : Type*} (i : Site → I) (coin : Site → Bool) :
    List Site → Sparse I
  | [] => single 1
  | h::hs => product (bitSparse (i h) (coin h)) (registerSparseList i coin hs)

lemma polynomial_registerSparseList {I Site : Type*} (i : Site → I) (coin : Site → Bool)
    (sites : List Site) :
    polynomial (registerSparseList i coin sites) =
      (sites.map fun h => if coin h then MvPolynomial.X (i h) else 1-MvPolynomial.X (i h)).prod := by
  induction sites with
  | nil => simp [registerSparseList,single,polynomial]
  | cons h hs ih =>
      simp only [registerSparseList,polynomial_product,polynomial_bitSparse,ih,
        List.map_cons,List.prod_cons]

def registerSparse {I : Type*} (N : RootedBinary V E X) (i : Hybrid N → I)
    (coin : Hybrid N → Bool) : Sparse I :=
  registerSparseList i coin (FinEnum.toList (Hybrid N))

lemma polynomial_registerSparse {I : Type*} (N : RootedBinary V E X)
    (i : Hybrid N → I) (coin : Hybrid N → Bool) :
    polynomial (registerSparse N i coin) = MvPolynomial.rename i (registerPolynomial N coin) := by
  classical
  rw [registerSparse,polynomial_registerSparseList]
  rw [((enumeration_perm (Hybrid N)).map
    (fun h => if coin h then MvPolynomial.X (i h) else 1-MvPolynomial.X (i h))).prod_eq]
  rw [Finset.prod_map_toList,registerPolynomial,map_prod]
  apply Finset.prod_congr rfl
  intro h _
  cases coin h <;> simp

def initialRows {I : Type*} (N : RootedBinary V E X) (sample : Copy → X)
    (i : Hybrid N → I) : Rows I (Code N sample) :=
  (FinEnum.toList (Hybrid N → Bool)).map fun coin =>
    (initialCodeEffective N sample (originalRegisterEffective N coin),registerSparse N i coin)

/-- Exact coefficient identity with the unchanged original initialization
polynomial. A shared variable embedding is explicit and need not be injective.
Equal destination keys contribute their complete literal fibre sum. -/
theorem polynomial_initialRows {I : Type*} (N : RootedBinary V E X) (sample : Copy → X)
    (i : Hybrid N → I) (a : SelectedIndex N sample Finset.univ) :
    polynomial (readRows (project N Finset.univ) (initialRows N sample i) a) =
      MvPolynomial.rename i (initialPolynomial N sample a) := by
  classical
  rw [initialRows,readRows_map,polynomial_enumerate,initialPolynomial,map_sum]
  apply Finset.sum_congr rfl
  intro coin _
  rw [initialCodeEffective_eq,originalRegisterEffective_eq,project_eq]
  by_cases h : projection N Finset.univ (initialCode N sample (originalRegister N coin)) = a
  · rw [if_pos h,if_pos h]
    exact polynomial_registerSparse N i coin
  · rw [if_neg h,if_neg h]
    simp [polynomial]

theorem initialRows_actual {I : Type*} (N : RootedBinary V E X) (sample : Copy → X)
    (i : Hybrid N → I) (p : HybridProbabilities N)
    (a : SelectedIndex N sample Finset.univ) (x : I → ℝ)
    (hx : ∀ h, x (i h) = p.gamma h) :
    value (readRows (project N Finset.univ) (initialRows N sample i) a) x =
      ((((originalRegisterPMF N p).map (initialCode N sample)).map
        (projection N Finset.univ)) a).toReal := by
  rw [← eval_polynomial,polynomial_initialRows,MvPolynomial.eval₂_rename]
  rw [show (fun h => x (i h)) = p.gamma from funext hx]
  exact actual_original_initial_polynomial N sample p a

#print axioms originalRegisterEffective_eq
#print axioms initialCodeEffective_eq
#print axioms polynomial_initialRows
#print axioms initialRows_actual
end GProgram.G7.EffectiveInitializationCoefficients
