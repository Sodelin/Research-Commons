import ActualCrossingCuts
import ConvexBoundarySplit

/-! UNCOMPILED source-cut rank convexity, with the zero/complement choice
explicit. No convexity or circularity assumption is made on the network. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualCutClusters
open Nanuq.Source Nanuq.Quartet Nanuq.ActualFinite Nanuq.AdjacentCertificate
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]

/-- If both possible alternating descendant patterns are excluded on every
sorted source quartet, either orientation of an actual cut avoiding rank0
has no hole. The bounded predicate is a source descendant set or its complement. -/
theorem actual_ranked_cut_no_hole (N : RootedBinary V E X)
    (n mask : Nat) (rank : X ≃ Fin n) (T : Tree)
    (hs : T.size=(occurrenceLabels n mask).length-1)
    (hsets : ∀ q : Fin 4 ↪ X,
      N.rawDisplayedQuartets q=finiteResolutionSet T (occurrenceLabels n mask)
        ⟨(rank (q 0)).val,(rank (q 1)).val,(rank (q 2)).val,(rank (q 3)).val⟩)
    (S : N.Switching) (e : S.Edge) (A : Finset Nat)
    (hbound : ∀ a ∈ A, a<n) (hz : 0 ∉ A)
    (horient :
      (∀ a : Fin n, a.val ∈ A ↔ S.graph.DReach (S.graph.target e) (N.leaf (rank.symm a))) ∨
      (∀ a : Fin n, a.val ∈ A ↔ ¬S.graph.DReach (S.graph.target e) (N.leaf (rank.symm a)))) :
    ∀ x y z : Nat, x ∈ A → z ∈ A → x≤y → y≤z → y∈A := by
  apply convex_of_no_zero_crossing A hz
  intro x y z hx0 hxy hyz hx hy hza
  have hzn := hbound z hza
  let v : Fin 4 → Fin n := ![⟨0,by omega⟩,⟨x,by omega⟩,⟨y,by omega⟩,⟨z,hzn⟩]
  have hv : Function.Injective v := by
    intro i j hij
    have he := congrArg Fin.val hij
    fin_cases i <;> fin_cases j <;> simp [v] at he ⊢ <;> omega
  let q : Fin 4 ↪ X := ⟨fun i => rank.symm (v i),fun i j h => hv (rank.symm.injective h)⟩
  have hr (i : Fin 4) : rank (q i)=v i := rank.apply_symm_apply (v i)
  have hnon := actual_sorted_crossing_absent N n mask rank T hs hsets q
    (by simp [hr,v]; omega) (by simp [hr,v]; omega) (by simp [hr,v]; omega)
  apply hnon
  apply actual_crossing_of_descendants N S e q
  have hzero : (v 0).val ∉ A := by simpa [v] using hz
  have hfirst : (v 1).val ∈ A := by simpa [v] using hx
  have hmiddle : (v 2).val ∉ A := by simpa [v] using hy
  have hlast : (v 3).val ∈ A := by simpa [v] using hza
  rcases horient with h | h
  · exact Or.inl ⟨fun ht => hzero ((h (v 0)).mpr ht),
      fun ht => hmiddle ((h (v 2)).mpr ht),
      (h (v 1)).mp hfirst,(h (v 3)).mp hlast⟩
  · exact Or.inr ⟨by by_contra ht; exact hzero ((h (v 0)).mpr ht),
      by by_contra ht; exact hmiddle ((h (v 2)).mpr ht),
      (h (v 1)).mp hfirst,(h (v 3)).mp hlast⟩

end Nanuq.ActualCutClusters
