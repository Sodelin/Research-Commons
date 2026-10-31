import ActualFiniteDistinctMean
import Mathlib.Data.Fintype.Perm
import Mathlib.Tactic.FinCases

/-! UNCOMPILED exact four-coordinate permutation identities. The two
membership predicates are INDEPENDENT: duplicated labels may lie on both
edge sides. Finite checks request kernel reduction, never native_decide. -/
set_option debug.skipKernelTC false
set_option maxRecDepth 10000
namespace Nanuq.ActualFinite
open Nanuq.AdjacentCertificate

def coordinateQuartet (v : Fin 4 → Nat) : Quartet := ⟨v 0,v 1,v 2,v 3⟩

def indexSide (r : Fin 3) (i : Fin 4) : Bool :=
  (coordinateQuartet Fin.val).side r.val i.val

def indexCut (r : Fin 3) (L R : Fin 4 → Bool) : Bool :=
  if r.val=0 then (L 0 && L 1 && R 2 && R 3) || (R 0 && R 1 && L 2 && L 3)
  else if r.val=1 then (L 0 && L 2 && R 1 && R 3) || (R 0 && R 2 && L 1 && L 3)
  else (L 0 && L 3 && R 1 && R 2) || (R 0 && R 3 && L 1 && L 2)

def reindexResolution (σ : Equiv.Perm (Fin 4)) (r : Fin 3) : Fin 3 :=
  if indexSide r (σ.symm 0)==indexSide r (σ.symm 1) then 0
  else if indexSide r (σ.symm 0)==indexSide r (σ.symm 2) then 1 else 2

theorem reindexResolution_bijective :
    ∀ σ : Equiv.Perm (Fin 4), Function.Bijective (reindexResolution σ) := by
  letI : Fintype (Equiv.Perm (Fin 4)) := fintypePerm
  decide +kernel

theorem reindexResolution_sides :
    ∀ (σ : Equiv.Perm (Fin 4)) (r : Fin 3) (i j : Fin 4),
      (indexSide r i == indexSide r j)=
        (indexSide (reindexResolution σ r) (σ i) == indexSide (reindexResolution σ r) (σ j)) := by
  letI : Fintype (Equiv.Perm (Fin 4)) := fintypePerm
  decide +kernel

theorem reindexResolution_cut :
    ∀ (σ : Equiv.Perm (Fin 4)) (r : Fin 3) (L R : Fin 4 → Bool),
      indexCut r (fun i => L (σ i)) (fun i => R (σ i))=
        indexCut (reindexResolution σ r) L R := by
  letI : Fintype (Equiv.Perm (Fin 4)) := fintypePerm
  decide +kernel

theorem coordinate_edgeWitness (tips : List Nat) (lo len : Nat)
    (v : Fin 4 → Nat) (r : Fin 3) :
    edgeWitness tips lo len (coordinateQuartet v) r.val =
      indexCut r (fun i => ((tips.drop lo).take len).contains (v i))
        (fun i => (tips.take lo++tips.drop (lo+len)).contains (v i)) := by
  fin_cases r <;> rfl

theorem edgeWitness_coordinate_permutation (tips : List Nat) (lo len : Nat)
    (v : Fin 4 → Nat) (σ : Equiv.Perm (Fin 4)) (r : Fin 3) :
    edgeWitness tips lo len (coordinateQuartet (fun i => v (σ i))) r.val=
      edgeWitness tips lo len (coordinateQuartet v) (reindexResolution σ r).val := by
  rw [coordinate_edgeWitness,coordinate_edgeWitness]
  exact reindexResolution_cut σ r _ _

theorem coordinate_side (v : Fin 4 ↪ Nat) (r : Fin 3) (i : Fin 4) :
    (coordinateQuartet v).side r.val (v i)=indexSide r i := by
  have he (i j : Fin 4) : (v i==v j)=(i==j) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq]
    exact v.injective.eq_iff
  fin_cases r <;> fin_cases i <;> simp [coordinateQuartet,Quartet.side,indexSide,he]

#print axioms reindexResolution_cut
#print axioms edgeWitness_coordinate_permutation
end Nanuq.ActualFinite
