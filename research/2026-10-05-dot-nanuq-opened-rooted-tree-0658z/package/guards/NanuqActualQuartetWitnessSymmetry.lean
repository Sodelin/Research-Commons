import guards.NanuqActualWeightedAnchorComposition

set_option debug.skipKernelTC false

/-! Witness exchange preserves the actual DISTINCT quartet mean. The two
crossing resolution labels are exchanged bijectively; neither multiplicities
nor an independent quartet symmetry assumption are used. -/
namespace Nanuq.Quartet
open scoped Classical

def swapWitnessResolution : Resolution → Resolution
  | .xy_zw => .xy_zw
  | .xz_yw => .xw_yz
  | .xw_yz => .xz_yw

theorem swapWitnessResolution_involutive : Function.Involutive swapWitnessResolution := by
  intro r;cases r <;> rfl

theorem swapWitness_separates (r : Resolution) :
    separatesFirstPair (swapWitnessResolution r) = separatesFirstPair r := by
  cases r <;> rfl

theorem distinctMean_swapWitness (s : Finset Resolution) :
    distinctMean (s.image swapWitnessResolution) = distinctMean s := by
  have hi := swapWitnessResolution_involutive.injective
  unfold distinctMean
  rw [Finset.sum_image (fun a _ b _ h => hi h)]
  simp_rw [swapWitness_separates]
  rw [Finset.card_image_of_injective s hi]

theorem sourceMean_swapWitness {S : Type*} [Fintype S] (f : S → Resolution) :
    sourceMean (swapWitnessResolution ∘ f) = sourceMean f := by
  unfold sourceMean displayed
  rw [← Finset.image_image]
  exact distinctMean_swapWitness _
end Nanuq.Quartet

namespace Nanuq.Source.RootedBinary
open scoped Classical
open Nanuq.Quartet
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

noncomputable def swapQuartetWitness (q : Fin 4 ↪ X) : Fin 4 ↪ X :=
  (Equiv.swap (2 : Fin 4) 3).toEmbedding.trans q

namespace Switching
variable {N} (S : N.Switching)

theorem resolve_swap_witness (q : Fin 4 ↪ X) :
    S.resolve (swapQuartetWitness q) = swapWitnessResolution (S.resolve q) := by
  apply Eq.symm
  apply (S.resolves_iff_eq_resolve (swapQuartetWitness q) _).mp
  have h := S.resolve_spec q
  cases hr : S.resolve q
  · rw [hr] at h
    exact S.graph.hasQuartet_swap_right h
  · rw [hr] at h
    exact h
  · rw [hr] at h
    exact h
end Switching

theorem rawQuartetMean_swap_witness (q : Fin 4 ↪ X) :
    N.rawQuartetMean (swapQuartetWitness q) = N.rawQuartetMean q := by
  unfold rawQuartetMean
  have he : (fun S : N.Switching => S.resolve (swapQuartetWitness q)) =
      swapWitnessResolution ∘ (fun S : N.Switching => S.resolve q) := by
    funext S;exact S.resolve_swap_witness q
  rw [he,sourceMean_swapWitness]

theorem actualTupleMean_witness_swap (x y p q : X) :
    N.actualTupleMean ![x,y,p,q] = N.actualTupleMean ![x,y,q,p] := by
  let e := Equiv.swap (2 : Fin 4) 3
  have hf : ![x,y,q,p] = ![x,y,p,q] ∘ e := by
    funext i;fin_cases i <;> rfl
  have hg : ![x,y,p,q] = ![x,y,q,p] ∘ e := by
    funext i;fin_cases i <;> rfl
  by_cases hi : Function.Injective ![x,y,p,q]
  · have hj : Function.Injective ![x,y,q,p] := by rw [hf];exact hi.comp e.injective
    have he : swapQuartetWitness ⟨![x,y,p,q],hi⟩ = (⟨![x,y,q,p],hj⟩ : Fin 4 ↪ X) := by
      ext i;fin_cases i <;> rfl
    simp only [actualTupleMean,dif_pos hi,dif_pos hj]
    rw [← he]
    exact (N.rawQuartetMean_swap_witness _).symm
  · have hj : ¬ Function.Injective ![x,y,q,p] := by
      intro h
      apply hi
      rw [hg]
      exact h.comp e.injective
    simp [actualTupleMean,hi,hj]
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.rawQuartetMean_swap_witness
