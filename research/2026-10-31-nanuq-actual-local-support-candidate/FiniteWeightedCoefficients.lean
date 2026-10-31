import AnchorSymmetry
import CircularDecomposition

/-! UNCOMPILED algebraic part of one actual-source support receiver.
The finite matrix below is an intermediate expression to be identified with
actualWeightedAnchorDistance at the same canonical rank, not a substitute
observation model or supplied circularity certificate. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.ActualFinite
open Nanuq.AdjacentCertificate Nanuq.Restriction Nanuq.Weighted Nanuq.Reconstruction
open scoped BigOperators

/-- The original unordered anchor sum in the qualified finite coordinates. -/
def finiteWeightedMatrix (n mask : Nat) (T : Tree) (m : Fin n → ℚ) : Matrix n :=
  fun x y => ∑ pq ∈ upperPairs n, m pq.1*m pq.2 *
    (anchor (quartets n) (codedPattern T (occurrenceLabels n mask) n)
      pq.1.val pq.2.val x.val y.val : ℚ)

theorem finiteWeightedMatrix_symmetric (n mask : Nat) (T : Tree)
    (m : Fin n → ℚ) (x y : Fin n) :
    finiteWeightedMatrix n mask T m x y=finiteWeightedMatrix n mask T m y x := by
  unfold finiteWeightedMatrix
  apply Finset.sum_congr rfl
  intro pq _
  rw [anchor_query_swap]

theorem finiteWeightedMatrix_diagonal (n mask : Nat) (T : Tree)
    (m : Fin n → ℚ) (x : Fin n) : finiteWeightedMatrix n mask T m x x=0 := by
  simp [finiteWeightedMatrix,anchor]

theorem finiteWeightedMatrix_alpha (n mask : Nat) (T : Tree)
    (m : Fin n → ℚ) (i j : Fin n) :
    circularAlpha (finiteWeightedMatrix n mask T m) i j =
      ∑ pq ∈ upperPairs n, m pq.1*m pq.2 *
        (alpha n (quartets n) (codedPattern T (occurrenceLabels n mask) n)
          pq.1.val pq.2.val i.val j.val : ℚ) := by
  simp only [circularAlpha,finiteWeightedMatrix,alpha,cyclicNext,
    Int.cast_add,Int.cast_sub,mul_add,mul_sub,Finset.sum_add_distrib,Finset.sum_sub_distrib]

theorem finiteWeightedMatrix_alpha_nonnegative (n mask : Nat) (T : Tree)
    (hn : 3≤n) (hs : T.size=(occurrenceLabels n mask).length-1)
    (m : Fin n → ℚ) (hm : ∀ p, 0≤m p) (i j : Fin n) (hij : i<j) :
    0≤circularAlpha (finiteWeightedMatrix n mask T m) i j := by
  rw [finiteWeightedMatrix_alpha]
  apply Finset.sum_nonneg
  intro pq hpq
  apply mul_nonneg (mul_nonneg (hm _) (hm _))
  exact_mod_cast all_size_anchor_nonnegative n mask T hn hs
    pq.1.val pq.2.val i.val j.val pq.1.isLt pq.2.isLt i.isLt j.isLt
    ((mem_upperPairs _ _).mp hpq) hij

theorem finiteWeightedMatrix_circular (n mask : Nat) (T : Tree)
    (hn : 3≤n) (hs : T.size=(occurrenceLabels n mask).length-1)
    (m : Fin n → ℚ) (hm : ∀ p, 0≤m p) :
    CircularDecomposable (finiteWeightedMatrix n mask T m) := by
  exact circular_decomposable_of_coefficients _
    (finiteWeightedMatrix_symmetric n mask T m)
    (finiteWeightedMatrix_diagonal n mask T m)
    (finiteWeightedMatrix_alpha_nonnegative n mask T hn hs m hm)

theorem finiteWeightedMatrix_absent_zero (n mask : Nat) (T : Tree)
    (hn : 3≤n) (hs : T.size=(occurrenceLabels n mask).length-1)
    (m : Fin n → ℚ) (i j : Fin n) (hij : i<j)
    (nonadj : i.val+1<j.val ∧ ¬(i.val=0 ∧ j.val+1=n))
    (absent : displayedPair (quartets n) (codedPattern T (occurrenceLabels n mask) n)
      ((i.val+1)%n) j.val i.val ((j.val+1)%n)=false) :
    circularAlpha (finiteWeightedMatrix n mask T m) i j=0 := by
  rw [finiteWeightedMatrix_alpha]
  apply Finset.sum_eq_zero
  intro pq hpq
  rw [all_size_absent_boundary_zero n mask T hn hs pq.1.val pq.2.val
    i.val j.val pq.1.isLt pq.2.isLt i.isLt j.isLt
    ((mem_upperPairs _ _).mp hpq) hij nonadj absent]
  simp

theorem finiteWeightedMatrix_positive_anchor (n mask : Nat) (T : Tree)
    (hn : 3≤n) (hs : T.size=(occurrenceLabels n mask).length-1)
    (m : Fin n → ℚ) (hm : ∀ p, 0<m p) (i j : Fin n) (hij : i<j)
    (p q : Fin n) (hpq : p≠q)
    (ha : 0<alpha n (quartets n) (codedPattern T (occurrenceLabels n mask) n)
      p.val q.val i.val j.val) :
    0<circularAlpha (finiteWeightedMatrix n mask T m) i j := by
  obtain ⟨p',q',hpq',ha'⟩ : ∃ p' q' : Fin n, p'<q' ∧
      0<alpha n (quartets n) (codedPattern T (occurrenceLabels n mask) n)
        p'.val q'.val i.val j.val := by
    rcases lt_or_gt_of_ne hpq with h | h
    · exact ⟨p,q,h,ha⟩
    · refine ⟨q,p,h,?_⟩
      rw [alpha_anchor_swap _ _ _ q.val p.val]
      exact ha
  rw [finiteWeightedMatrix_alpha]
  have ht : 0 < m p'*m q' *
      (alpha n (quartets n) (codedPattern T (occurrenceLabels n mask) n)
        p'.val q'.val i.val j.val : ℚ) := by
    apply mul_pos (mul_pos (hm _) (hm _))
    exact_mod_cast ha'
  apply lt_of_lt_of_le ht
  apply Finset.single_le_sum (a := (p',q'))
  · intro pq hpq''
    apply mul_nonneg (le_of_lt (mul_pos (hm _) (hm _)))
    exact_mod_cast all_size_anchor_nonnegative n mask T hn hs
      pq.1.val pq.2.val i.val j.val pq.1.isLt pq.2.isLt i.isLt j.isLt
      ((mem_upperPairs _ _).mp hpq'') hij
  · exact (mem_upperPairs _ _).mpr hpq'

theorem finiteWeightedMatrix_nontrivial_support (n mask : Nat) (T : Tree)
    (hn : 3≤n) (hs : T.size=(occurrenceLabels n mask).length-1)
    (m : Fin n → ℚ) (hm : ∀ p, 0<m p) (i j : Fin n) (hij : i<j)
    (nonadj : i.val+1<j.val ∧ ¬(i.val=0 ∧ j.val+1=n)) :
    0<circularAlpha (finiteWeightedMatrix n mask T m) i j ↔
      displayedPair (quartets n) (codedPattern T (occurrenceLabels n mask) n)
        ((i.val+1)%n) j.val i.val ((j.val+1)%n)=true := by
  constructor
  · intro hp
    by_contra hh
    have hz : displayedPair (quartets n) (codedPattern T (occurrenceLabels n mask) n)
        ((i.val+1)%n) j.val i.val ((j.val+1)%n)=false := by
      cases he : displayedPair (quartets n) (codedPattern T (occurrenceLabels n mask) n)
        ((i.val+1)%n) j.val i.val ((j.val+1)%n) <;> simp_all
    rw [finiteWeightedMatrix_absent_zero n mask T hn hs m i j hij nonadj hz] at hp
    exact (lt_irrefl 0) hp
  · intro hd
    have ha := (all_size_boundary_anchor_positive n mask T hn hs
      i.val j.val i.isLt j.isLt hij nonadj).mpr hd
    apply finiteWeightedMatrix_positive_anchor n mask T hn hs m hm i j hij i (cyclicNext j) _ ha
    intro he
    have hv := congrArg Fin.val he
    change i.val=(j.val+1)%n at hv
    by_cases hj : j.val+1=n
    · simp only [hj,Nat.mod_self] at hv
      exact nonadj.2 ⟨hv,hj⟩
    · rw [Nat.mod_eq_of_lt (by omega)] at hv
      have hi := i.isLt
      omega

theorem finiteWeightedMatrix_pendant_positive (n mask : Nat) (T : Tree)
    (hn : 3≤n) (hs : T.size=(occurrenceLabels n mask).length-1)
    (m : Fin n → ℚ) (hm : ∀ p, 0<m p) (i j : Fin n) (hij : i<j)
    (hadj : j=cyclicNext i ∨ i=cyclicNext j) :
    0<circularAlpha (finiteWeightedMatrix n mask T m) i j := by
  rcases hadj with hadj | hadj
  · have hα := cyclic_pendant_anchor_two n (quartets n)
      (codedPattern T (occurrenceLabels n mask) n) i.val hn i.isLt
    have hj : j.val=(i.val+1)%n := congrArg Fin.val hadj
    have ha : 0<alpha n (quartets n) (codedPattern T (occurrenceLabels n mask) n)
        i.val (cyclicNext j).val i.val j.val := by
      change 0<alpha n _ _ i.val ((j.val+1)%n) i.val j.val
      rw [hj,hα]
      norm_num
    apply finiteWeightedMatrix_positive_anchor n mask T hn hs m hm i j hij i (cyclicNext j) _ ha
    intro he
    have hv := congrArg Fin.val he
    change i.val=(j.val+1)%n at hv
    rw [hj] at hv
    exact (next_next_ne n i.val hn i.isLt) hv.symm
  · have hα := cyclic_pendant_anchor_two n (quartets n)
      (codedPattern T (occurrenceLabels n mask) n) j.val hn j.isLt
    have hi : i.val=(j.val+1)%n := congrArg Fin.val hadj
    have ha : 0<alpha n (quartets n) (codedPattern T (occurrenceLabels n mask) n)
        j.val (cyclicNext i).val i.val j.val := by
      rw [alpha_gap_swap]
      change 0<alpha n _ _ j.val ((i.val+1)%n) j.val i.val
      rw [hi,hα]
      norm_num
    apply finiteWeightedMatrix_positive_anchor n mask T hn hs m hm i j hij j (cyclicNext i) _ ha
    intro he
    have hv := congrArg Fin.val he
    change j.val=(i.val+1)%n at hv
    rw [hi] at hv
    exact (next_next_ne n j.val hn j.isLt) hv.symm

end Nanuq.ActualFinite
