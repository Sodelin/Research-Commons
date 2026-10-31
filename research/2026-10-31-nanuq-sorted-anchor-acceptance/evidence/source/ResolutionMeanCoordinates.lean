import ResolutionCoordinates

/-! UNCOMPILED exact DISTINCT-set mean reindexing. Finite Boolean identities
are kernel-reduction requests; no frequency-weighted substitution occurs. -/
set_option debug.skipKernelTC false
set_option maxRecDepth 10000
namespace Nanuq.ActualFinite
open Nanuq.AdjacentCertificate Nanuq.Quartet

local instance meanCoordinatePermFintype : Fintype (Equiv.Perm (Fin 4)) := fintypePerm

def resolutionFin (r : Resolution) : Fin 3 :=
  ⟨resolutionIndex r,by cases r <;> decide⟩

def presentIndices (g : Fin 3 → Bool) : List (Fin 3) := ([0,1,2] : List (Fin 3)).filter g

def indexedMean (g : Fin 3 → Bool) : ℚ :=
  ((presentIndices g).filter (fun r => r != 0)).length / ((presentIndices g).length : ℚ)

def indexedPairMean (g : Fin 3 → Bool) (i j : Fin 4) : ℚ :=
  ((presentIndices g).filter (fun r => indexSide r i != indexSide r j)).length /
    ((presentIndices g).length : ℚ)

theorem mask_distinctMean_exact : ∀ g : Fin 3 → Bool,
    distinctMean (({.xy_zw,.xz_yw,.xw_yz} : Finset Resolution).filter
      (fun r => g (resolutionFin r)=true))=indexedMean g := by
  decide +kernel

theorem indexedMean_permutation : ∀ (σ : Equiv.Perm (Fin 4)) (g : Fin 3 → Bool),
    indexedMean (fun r => g (reindexResolution σ r))=indexedPairMean g (σ 0) (σ 1) := by
  decide +kernel

def finiteWitnessMask (T : Tree) (tips : List Nat) (v : Fin 4 → Nat) (r : Fin 3) : Bool :=
  (T.internalIntervals 1).any (fun e => edgeWitness tips e.1 e.2 (coordinateQuartet v) r.val)

theorem finiteWitnessMask_iff (T : Tree) (tips : List Nat) (v : Fin 4 → Nat) (r : Fin 3) :
    finiteWitnessMask T tips v r=true ↔
      ∃ e∈T.internalIntervals 1, edgeWitness tips e.1 e.2 (coordinateQuartet v) r.val=true := by
  exact List.any_eq_true

theorem finiteResolutionSet_mean (T : Tree) (tips : List Nat) (v : Fin 4 → Nat) :
    distinctMean (finiteResolutionSet T tips (coordinateQuartet v))=
      indexedMean (finiteWitnessMask T tips v) := by
  have hs : finiteResolutionSet T tips (coordinateQuartet v)=
      ({.xy_zw,.xz_yw,.xw_yz} : Finset Resolution).filter
        (fun r => finiteWitnessMask T tips v (resolutionFin r)=true) := by
    ext r
    rw [mem_finiteResolutionSet,Finset.mem_filter,finiteWitnessMask_iff]
    cases r <;> simp [resolutionFin,resolutionIndex]
  rw [hs,mask_distinctMean_exact]

theorem finiteWitnessMask_permutation (T : Tree) (tips : List Nat) (v : Fin 4 → Nat)
    (σ : Equiv.Perm (Fin 4)) (r : Fin 3) :
    finiteWitnessMask T tips (fun i => v (σ i)) r=
      finiteWitnessMask T tips v (reindexResolution σ r) := by
  simp only [finiteWitnessMask,edgeWitness_coordinate_permutation]

theorem finite_distinctMean_permutation (T : Tree) (tips : List Nat) (v : Fin 4 → Nat)
    (σ : Equiv.Perm (Fin 4)) :
    distinctMean (finiteResolutionSet T tips (coordinateQuartet (fun i => v (σ i))))=
      indexedPairMean (finiteWitnessMask T tips v) (σ 0) (σ 1) := by
  rw [finiteResolutionSet_mean]
  have hm : finiteWitnessMask T tips (fun i => v (σ i))=
      fun r => finiteWitnessMask T tips v (reindexResolution σ r) := by
    funext r
    exact finiteWitnessMask_permutation T tips v σ r
  rw [hm,indexedMean_permutation]

#print axioms indexedMean_permutation
#print axioms finite_distinctMean_permutation
end Nanuq.ActualFinite
