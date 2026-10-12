import G4WeightedOrdinaryTreeLaw
import G4ActualPositiveGridUniqueness
import G7SinglePopulationPolynomialKernel
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# Whole-profile finite determination for the original COMMON branch

Contributor: dot (OpenAI), 12 October 2026. WORKING / UNCOMPILED.
Formal composition of the accepted October 8 whole-COMMON proof, §§5–7,
with its details supplement and mandatory COMMON-only correction. The
asymptotic-ratio criterion is classical Teicher–Chandra mixture theory.
This file is one unfinished consumer, not a collection of accepted endpoints.
The final profile bound, catalogue completeness, and finite-menu connection
remain pending until their actual proofs are present and checked.
-/
namespace DotG4.WholeProfileDetermination
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5 GProgram.G5.Normalization
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeCommonPairGerm
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.FiniteGenealogyEncoding
open DotG4.WeightedOrdinaryTreeLaw DotG4.ActualSelectedPathExposure
open G1ActualDisplayedTreeFamily G1UnrankedTreeClusterUniqueness
open scoped Classical BigOperators NNReal

section Coordinates
variable {X : Type*} [Fintype X] [DecidableEq X]

/-- Positive binary stem-free tree domain, with the entire hierarchy retained.
The weights are independent of sampling and the full clade is zero. -/
def PositiveTreeWeights (w : CladeWeights X) : Prop :=
  w ∅ = 0 ∧ w Finset.univ = 0 ∧
  ∃ T : Genealogy X, T.WellLabelled ∧ T.leaves = Finset.univ ∧
    ∀ A : Finset X, A ≠ ∅ → A ≠ Finset.univ →
      (0 < w A ↔ A ∈ treeClusters T)

noncomputable def directedExposure (w : CladeWeights X) (i j : X) : ℝ :=
  ∑ A : Finset X, if i ∈ A ∧ j ∉ A then (w A : ℝ) else 0

noncomputable def rootExposure (w : CladeWeights X) (i : X) : ℝ :=
  ∑ A : Finset X, if i ∈ A then (w A : ℝ) else 0

noncomputable def sharedExposure (w : CladeWeights X) (i j : X) : ℝ :=
  ∑ A : Finset X, if i ∈ A ∧ j ∈ A then (w A : ℝ) else 0

noncomputable def directedSurvival (w : CladeWeights X) (i j : X) : ℝ :=
  Real.exp (-directedExposure w i j)

lemma directedExposure_nonnegative (w : CladeWeights X) (i j : X) :
    0 ≤ directedExposure w i j := by
  apply Finset.sum_nonneg
  intro A _
  split_ifs <;> positivity

@[simp] lemma directedExposure_self (w : CladeWeights X) (i : X) :
    directedExposure w i i = 0 := by simp [directedExposure]

lemma sharedExposure_comm (w : CladeWeights X) (i j : X) :
    sharedExposure w i j = sharedExposure w j i := by
  unfold sharedExposure
  apply Finset.sum_congr rfl
  intro A _
  simp only [and_comm]

lemma directedExposure_eq_root_sub_shared (w : CladeWeights X) (i j : X) :
    directedExposure w i j = rootExposure w i - sharedExposure w i j := by
  unfold directedExposure rootExposure sharedExposure
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro A _
  by_cases hi : i ∈ A <;> by_cases hj : j ∈ A <;> simp [hi,hj]

lemma directedSurvival_positive (w : CladeWeights X) (i j : X) :
    0 < directedSurvival w i j := Real.exp_pos _

lemma directedSurvival_le_one (w : CladeWeights X) (i j : X) :
    directedSurvival w i j ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact neg_nonpos.mpr (directedExposure_nonnegative w i j)

/-- Quadratic rate coordinate of the actual proper-clade exposure evaluator. -/
noncomputable def quadraticExposure (w : CladeWeights X) (v : X → ℝ) : ℝ :=
  ∑ A : Finset X, (w A : ℝ) * (∑ i ∈ A, v i)^2

noncomputable def linearExposure (w : CladeWeights X) (v : X → ℝ) : ℝ :=
  ∑ A : Finset X, (w A : ℝ) * (∑ i ∈ A, v i)

lemma quadraticExposure_nonnegative (w : CladeWeights X) (v : X → ℝ) :
    0 ≤ quadraticExposure w v := by
  apply Finset.sum_nonneg
  intro A _
  positivity


/-- Positive support is laminar; zero coordinates have no scheduling effect. -/
def LaminarWeights (w : CladeWeights X) : Prop :=
  w ∅ = 0 ∧ w Finset.univ = 0 ∧
  ∀ A B : Finset X, 0 < w A → 0 < w B →
    A ⊆ B ∨ B ⊆ A ∨ Disjoint A B

lemma treeClusters_laminar (T : Genealogy X) (hT : T.WellLabelled)
    (A B : Finset X) (hA : A ∈ treeClusters T) (hB : B ∈ treeClusters T) :
    A ⊆ B ∨ B ⊆ A ∨ Disjoint A B := by
  induction T generalizing A B with
  | leaf x =>
    have ha : A = {x} := by simpa [treeClusters] using hA
    have hb : B = {x} := by simpa [treeClusters] using hB
    exact Or.inl (by rw [ha,hb])
  | graft l r ihl ihr =>
    rcases Finset.mem_insert.mp hA with ha | ha
    · subst A
      exact Or.inr (Or.inl (tree_cluster_subset_leaves (.graft l r) hB))
    · rcases Finset.mem_insert.mp hB with hb | hb
      · subst B
        exact Or.inl (tree_cluster_subset_leaves (.graft l r)
          (Finset.mem_insert_of_mem ha))
      · rcases Finset.mem_union.mp ha with ha | ha <;>
          rcases Finset.mem_union.mp hb with hb | hb
        · exact ihl hT.1 A B ha hb
        · exact Or.inr (Or.inr (hT.2.2.mono
            (tree_cluster_subset_leaves l ha) (tree_cluster_subset_leaves r hb)))
        · exact Or.inr (Or.inr (hT.2.2.symm.mono
            (tree_cluster_subset_leaves r ha) (tree_cluster_subset_leaves l hb)))
        · exact ihr hT.2.1 A B ha hb

lemma positiveTreeWeights_laminar (w : CladeWeights X) (hw : PositiveTreeWeights w) :
    LaminarWeights w := by
  refine ⟨hw.1,hw.2.1,?_⟩
  obtain ⟨T,hT,_,hs⟩ := hw.2.2
  intro A B ha hb
  have hae : A ≠ ∅ := by intro h; simpa [h,hw.1] using ha
  have hau : A ≠ Finset.univ := by intro h; simpa [h,hw.2.1] using ha
  have hbe : B ≠ ∅ := by intro h; simpa [h,hw.1] using hb
  have hbu : B ≠ Finset.univ := by intro h; simpa [h,hw.2.1] using hb
  exact treeClusters_laminar T hT A B ((hs A hae hau).mp ha) ((hs B hbe hbu).mp hb)

noncomputable def ancestorExposure (w : CladeWeights X) (A : Finset X) : ℝ :=
  ∑ B : Finset X, if A ⊆ B then (w B : ℝ) else 0

noncomputable def covarianceThreshold (w : CladeWeights X) (i : X) (h : ℝ) : Finset X :=
  Finset.univ.filter (fun j => h ≤ sharedExposure w i j)

lemma weight_le_ancestorExposure (w : CladeWeights X) (A : Finset X) :
    (w A : ℝ) ≤ ancestorExposure w A := by
  have h := Finset.single_le_sum
    (s := (Finset.univ : Finset (Finset X)))
    (f := fun B => if A ⊆ B then (w B : ℝ) else 0)
    (fun B _ => by split_ifs <;> positivity) (Finset.mem_univ A)
  simpa [ancestorExposure] using h

lemma ancestorExposure_le_shared (w : CladeWeights X) (A : Finset X)
    {i j : X} (hi : i ∈ A) (hj : j ∈ A) :
    ancestorExposure w A ≤ sharedExposure w i j := by
  apply Finset.sum_le_sum
  intro B _
  by_cases h : A ⊆ B
  · simp [h,h hi,h hj]
  · simp only [h,if_false]
    split_ifs <;> positivity

lemma shared_outside_add_weight_le_ancestor (w : CladeWeights X)
    (hw : LaminarWeights w) (A : Finset X) (ha : 0 < w A)
    {i j : X} (hi : i ∈ A) (hj : j ∉ A) :
    sharedExposure w i j + (w A : ℝ) ≤ ancestorExposure w A := by
  have hs : (w A : ℝ) = ∑ B : Finset X, if B = A then (w B : ℝ) else 0 := by simp
  rw [hs,sharedExposure,← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro B _
  by_cases hBA : B = A
  · subst B
    simp [hi,hj]
  · by_cases hB : 0 < w B
    · by_cases hij : i ∈ B ∧ j ∈ B
      · have hab : A ⊆ B := by
          rcases hw.2.2 A B ha hB with h | h | h
          · exact h
          · exact False.elim (hj (h hij.2))
          · exact False.elim (Finset.disjoint_left.mp h hi hij.1)
        simp [hBA,hij,hab]
      · simp only [hBA,hij,if_false,zero_add]
        split_ifs <;> positivity
    · have hz : w B = 0 := le_antisymm (le_of_not_gt hB) (zero_le _)
      simp [hz]

lemma positive_clade_is_covariance_threshold (w : CladeWeights X)
    (hw : LaminarWeights w) (A : Finset X) (ha : 0 < w A)
    {i : X} (hi : i ∈ A) :
    covarianceThreshold w i (ancestorExposure w A) = A := by
  ext j
  simp only [covarianceThreshold,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · intro hj
    by_contra hja
    have h := shared_outside_add_weight_le_ancestor w hw A ha hi hja
    have hp : 0 < (w A : ℝ) := ha
    linarith
  · exact ancestorExposure_le_shared w A hi

lemma sharedExposure_nonnegative (w : CladeWeights X) (i j : X) :
    0 ≤ sharedExposure w i j := by
  apply Finset.sum_nonneg
  intro A _
  split_ifs <;> positivity

lemma sharedExposure_positive_iff (w : CladeWeights X) (i j : X) :
    0 < sharedExposure w i j ↔ ∃ A : Finset X, 0 < w A ∧ i ∈ A ∧ j ∈ A := by
  rw [sharedExposure,Finset.sum_pos_iff_of_nonneg (by
    intro A _; split_ifs <;> positivity)]
  constructor
  · rintro ⟨A,_,hA⟩
    by_cases hij : i ∈ A ∧ j ∈ A
    · exact ⟨A,by simpa [hij] using hA,hij⟩
    · simp [hij] at hA
  · rintro ⟨A,hA,hij⟩
    exact ⟨A,Finset.mem_univ _,by simpa [hij] using hA⟩

/-- A positive covariance is the cumulative height of its smallest positive
common clade. This uses a finite inclusion chain, not a binary-shape oracle. -/
lemma sharedExposure_eq_ancestor_of_minimal (w : CladeWeights X)
    (hw : LaminarWeights w) (i j : X) (hp : 0 < sharedExposure w i j) :
    ∃ A : Finset X, 0 < w A ∧ i ∈ A ∧ j ∈ A ∧
      sharedExposure w i j = ancestorExposure w A := by
  let S : Finset (Finset X) := Finset.univ.filter (fun A => 0 < w A ∧ i ∈ A ∧ j ∈ A)
  obtain ⟨B,hB,hi,hj⟩ := (sharedExposure_positive_iff w i j).mp hp
  have hS : S.Nonempty := ⟨B,by simp [S,hB,hi,hj]⟩
  obtain ⟨A,hA,hmin⟩ := Finset.exists_min_image S Finset.card hS
  have hA' : 0 < w A ∧ i ∈ A ∧ j ∈ A := (Finset.mem_filter.mp hA).2
  refine ⟨A,hA'.1,hA'.2.1,hA'.2.2,?_⟩
  apply Finset.sum_congr rfl
  intro D _
  by_cases hd : 0 < w D
  · have he : (i ∈ D ∧ j ∈ D) ↔ A ⊆ D := by
      constructor
      · intro hij
        rcases hw.2.2 A D hA'.1 hd with h | h | h
        · exact h
        · have hm := hmin D (by simp [S,hd,hij])
          have eq : D = A := Finset.eq_of_subset_of_card_le h hm
          exact eq ▸ Finset.Subset.refl A
        · exact False.elim (Finset.disjoint_left.mp h hA'.2.1 hij.1)
      · intro h
        exact ⟨h hA'.2.1,h hA'.2.2⟩
    simp only [he]
  · have hz : w D = 0 := le_antisymm (le_of_not_gt hd) (zero_le _)
    simp [hz]

lemma nonempty_positive_threshold_is_clade (w : CladeWeights X)
    (hw : LaminarWeights w) (i : X) (h : ℝ) (hh : 0 < h)
    (hne : (covarianceThreshold w i h).Nonempty) :
    0 < w (covarianceThreshold w i h) := by
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image (covarianceThreshold w i h)
    (fun j => sharedExposure w i j) hne
  have hj' : h ≤ sharedExposure w i j := (Finset.mem_filter.mp hj).2
  obtain ⟨A,ha,hi,hja,he⟩ := sharedExposure_eq_ancestor_of_minimal w hw i j
    (lt_of_lt_of_le hh hj')
  have hset : covarianceThreshold w i h = A := by
    ext k
    constructor
    · intro hk
      by_contra hka
      have hless := shared_outside_add_weight_le_ancestor w hw A ha hi hka
      have hm := hmin k hk
      have hap : 0 < (w A : ℝ) := ha
      rw [← he] at hless
      linarith
    · intro hk
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
        le_trans (he ▸ hj') (ancestorExposure_le_shared w A hi hk)⟩
  simpa [hset] using ha

lemma covariance_eq_positive_support (w w' : CladeWeights X)
    (hw : LaminarWeights w) (hw' : LaminarWeights w')
    (he : ∀ i j, sharedExposure w i j = sharedExposure w' i j)
    (A : Finset X) : 0 < w A ↔ 0 < w' A := by
  have one_way (u u' : CladeWeights X) (hu : LaminarWeights u) (hu' : LaminarWeights u')
      (he : ∀ i j, sharedExposure u i j = sharedExposure u' i j)
      (hp : 0 < u A) : 0 < u' A := by
    have hne : A.Nonempty := by
      apply Finset.nonempty_iff_ne_empty.mpr
      intro hz
      simpa [hz,hu.1] using hp
    obtain ⟨i,hi⟩ := hne
    have hh : 0 < ancestorExposure u A :=
      lt_of_lt_of_le (show 0 < (u A : ℝ) from hp) (weight_le_ancestorExposure u A)
    have ht : covarianceThreshold u' i (ancestorExposure u A) = A := by
      calc
        _ = covarianceThreshold u i (ancestorExposure u A) := by
          ext j
          simp only [covarianceThreshold,Finset.mem_filter,Finset.mem_univ,true_and,he]
        _ = A := positive_clade_is_covariance_threshold u hu A hp hi
    have h := nonempty_positive_threshold_is_clade u' hu' i (ancestorExposure u A) hh
      (ht.symm ▸ hne)
    simpa only [ht] using h
  exact ⟨one_way w w' hw hw' he,one_way w' w hw' hw (fun i j => (he i j).symm)⟩

lemma positive_clade_attains_ancestor (w : CladeWeights X) (hw : LaminarWeights w)
    (A : Finset X) (ha : 0 < w A) :
    ∃ i ∈ A, ∃ j ∈ A, sharedExposure w i j = ancestorExposure w A := by
  have hne : A.Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    simpa [h,hw.1] using ha
  obtain ⟨i,hi⟩ := hne
  obtain ⟨j,hj,hmin⟩ := Finset.exists_min_image A (fun j => sharedExposure w i j) hne
  have hp : 0 < sharedExposure w i j :=
    lt_of_lt_of_le (lt_of_lt_of_le (show 0 < (w A : ℝ) from ha)
      (weight_le_ancestorExposure w A)) (ancestorExposure_le_shared w A hi hj)
  obtain ⟨B,hb,hib,hjb,he⟩ := sharedExposure_eq_ancestor_of_minimal w hw i j hp
  have hAB : A = B := by
    apply Finset.Subset.antisymm
    · intro k hk
      by_contra hkb
      have h := shared_outside_add_weight_le_ancestor w hw B hb hib hkb
      have hm := hmin k hk
      have hbp : 0 < (w B : ℝ) := hb
      rw [← he] at h
      linarith
    · intro k hk
      have ht := ancestorExposure_le_shared w B hib hk
      have hij := ancestorExposure_le_shared w A hi hj
      rw [← he] at ht
      have hmem : k ∈ covarianceThreshold w i (ancestorExposure w A) :=
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,le_trans hij ht⟩
      simpa only [positive_clade_is_covariance_threshold w hw A ha hi] using hmem
  exact ⟨i,hi,j,hj,hAB ▸ he⟩

lemma covariance_eq_ancestor (w w' : CladeWeights X)
    (hw : LaminarWeights w) (hw' : LaminarWeights w')
    (he : ∀ i j, sharedExposure w i j = sharedExposure w' i j)
    (A : Finset X) (ha : 0 < w A) :
    ancestorExposure w A = ancestorExposure w' A := by
  have ha' := (covariance_eq_positive_support w w' hw hw' he A).mp ha
  obtain ⟨i,hi,j,hj,hij⟩ := positive_clade_attains_ancestor w hw A ha
  obtain ⟨i',hi',j',hj',hij'⟩ := positive_clade_attains_ancestor w' hw' A ha'
  apply le_antisymm
  · have h := ancestorExposure_le_shared w A hi' hj'
    rwa [he i' j',hij'] at h
  · have h := ancestorExposure_le_shared w' A hi hj
    rwa [← he i j,hij] at h

lemma covariance_injective_on_laminar (w w' : CladeWeights X)
    (hw : LaminarWeights w) (hw' : LaminarWeights w')
    (he : ∀ i j, sharedExposure w i j = sharedExposure w' i j) : w = w' := by
  funext A
  generalize hn : Fintype.card X - A.card = n
  induction n using Nat.strong_induction_on generalizing A with
  | h n ih =>
    by_cases ha : 0 < w A
    · have hh := covariance_eq_ancestor w w' hw hw' he A ha
      have hrest :
          (∑ B ∈ (Finset.univ : Finset (Finset X)).erase A,
            if A ⊆ B then (w B : ℝ) else 0) =
          ∑ B ∈ (Finset.univ : Finset (Finset X)).erase A,
            if A ⊆ B then (w' B : ℝ) else 0 := by
        apply Finset.sum_congr rfl
        intro B hB
        by_cases hab : A ⊆ B
        · have hne : B ≠ A := (Finset.mem_erase.mp hB).1
          have hlt : A.card < B.card := Finset.card_lt_card
            (Finset.ssubset_iff_subset_ne.mpr ⟨hab,Ne.symm hne⟩)
          have hbnd := Finset.card_le_univ B
          have hm : Fintype.card X - B.card < n := by omega
          rw [ih _ hm B rfl]
        · simp [hab]
      have split (u : CladeWeights X) : ancestorExposure u A =
          (∑ B ∈ (Finset.univ : Finset (Finset X)).erase A,
            if A ⊆ B then (u B : ℝ) else 0) + (u A : ℝ) := by
        simpa [ancestorExposure] using
          (Finset.sum_erase_add (Finset.univ : Finset (Finset X))
            (fun B => if A ⊆ B then (u B : ℝ) else 0) (Finset.mem_univ A)).symm
      rw [split w,split w',hrest] at hh
      exact NNReal.coe_injective (add_left_cancel hh)
    · have ha' : ¬ 0 < w' A := fun h => ha
        ((covariance_eq_positive_support w w' hw hw' he A).mpr h)
      exact (le_antisymm (le_of_not_gt ha) (zero_le _)).trans
        (le_antisymm (le_of_not_gt ha') (zero_le _)).symm

/-- Every row has a zero shared-height entry outside its maximal positive
proper clade. No common-stem parameter survives in this normalized carrier. -/
lemma exists_zero_shared (w : CladeWeights X) (hw : LaminarWeights w)
    [Nontrivial X] (i : X) : ∃ j : X, i ≠ j ∧ sharedExposure w i j = 0 := by
  let S : Finset (Finset X) := Finset.univ.filter (fun A => 0 < w A ∧ i ∈ A)
  by_cases hS : S.Nonempty
  · obtain ⟨A,hA,hmax⟩ := Finset.exists_max_image S Finset.card hS
    have ha : 0 < w A ∧ i ∈ A := (Finset.mem_filter.mp hA).2
    have hproper : A ≠ Finset.univ := by intro h; simpa [h,hw.2.1] using ha.1
    have hout : ∃ j : X, j ∉ A := by
      by_contra h
      push_neg at h
      exact hproper (Finset.eq_univ_iff_forall.mpr h)
    obtain ⟨j,hj⟩ := hout
    refine ⟨j,(by intro h; subst j; exact hj ha.2),?_⟩
    apply le_antisymm _ (sharedExposure_nonnegative w i j)
    apply le_of_not_gt
    intro hp
    obtain ⟨B,hb,hib,hjb⟩ := (sharedExposure_positive_iff w i j).mp hp
    have hB : B ∈ S := by simp [S,hb,hib]
    rcases hw.2.2 A B ha.1 hb with h | h | h
    · have eq : A = B := Finset.eq_of_subset_of_card_le h (hmax B hB)
      exact hj (eq.symm ▸ hjb)
    · exact hj (h hjb)
    · exact Finset.disjoint_left.mp h ha.2 hib
  · obtain ⟨j,hj⟩ := exists_ne i
    refine ⟨j,Ne.symm hj,?_⟩
    apply le_antisymm _ (sharedExposure_nonnegative w i j)
    apply le_of_not_gt
    intro hp
    obtain ⟨A,ha,hia,_⟩ := (sharedExposure_positive_iff w i j).mp hp
    exact hS ⟨A,by simp [S,ha,hia]⟩

lemma directed_eq_rootExposure (w w' : CladeWeights X)
    (hw : LaminarWeights w) (hw' : LaminarWeights w') [Nontrivial X]
    (he : ∀ i j, directedExposure w i j = directedExposure w' i j)
    (i : X) : rootExposure w i = rootExposure w' i := by
  obtain ⟨j,_,hj⟩ := exists_zero_shared w hw i
  obtain ⟨j',_,hj'⟩ := exists_zero_shared w' hw' i
  have he1 := he i j
  have he2 := he i j'
  rw [directedExposure_eq_root_sub_shared,directedExposure_eq_root_sub_shared,hj] at he1
  rw [directedExposure_eq_root_sub_shared,directedExposure_eq_root_sub_shared,hj'] at he2
  have h1 := sharedExposure_nonnegative w' i j
  have h2 := sharedExposure_nonnegative w i j'
  linarith

lemma directedExposure_injective_on_laminar (w w' : CladeWeights X)
    (hw : LaminarWeights w) (hw' : LaminarWeights w') [Nontrivial X]
    (he : ∀ i j, directedExposure w i j = directedExposure w' i j) : w = w' := by
  apply covariance_injective_on_laminar w w' hw hw'
  intro i j
  have h := he i j
  rw [directedExposure_eq_root_sub_shared,directedExposure_eq_root_sub_shared,
    directed_eq_rootExposure w w' hw hw' he i] at h
  linarith

lemma directedSurvival_injective_on_laminar (w w' : CladeWeights X)
    (hw : LaminarWeights w) (hw' : LaminarWeights w') [Nontrivial X]
    (he : ∀ i j, directedSurvival w i j = directedSurvival w' i j) : w = w' := by
  apply directedExposure_injective_on_laminar w w' hw hw'
  intro i j
  exact neg_injective (Real.exp_injective (he i j))

/-- A finite conservative catalogue. Zero-weight resolutions are represented
only once by their weight function; no source-size bound is involved. -/
def InDirectedGrid (grid : X × X → Finset ℝ) (w : CladeWeights X) : Prop :=
  LaminarWeights w ∧ ∀ i j, directedSurvival w i j ∈ grid (i,j)

lemma finite_directed_grid_catalogue [Nontrivial X] (grid : X × X → Finset ℝ) :
    Set.Finite {w : CladeWeights X | InDirectedGrid grid w} := by
  let D := {w : CladeWeights X // InDirectedGrid grid w}
  let f : D → ((ij : X × X) → {x : ℝ // x ∈ grid ij}) :=
    fun w ij => ⟨directedSurvival w.val ij.1 ij.2,w.property.2 ij.1 ij.2⟩
  have hf : Function.Injective f := by
    intro w w' he
    apply Subtype.ext
    apply directedSurvival_injective_on_laminar w.val w'.val w.property.1 w'.property.1
    intro i j
    exact congrArg Subtype.val (congrFun he (i,j))
  letI : Finite D := Finite.of_injective f hf
  exact Set.toFinite _

lemma rootExposure_eq_shared_self (w : CladeWeights X) (i : X) :
    rootExposure w i = sharedExposure w i i := by
  simp only [rootExposure,sharedExposure,and_self]

lemma quadraticExposure_single (w : CladeWeights X) (i : X) :
    quadraticExposure w (fun x => if x = i then 1 else 0) = rootExposure w i := by
  unfold quadraticExposure rootExposure
  apply Finset.sum_congr rfl
  intro A _
  simp only [Finset.sum_ite_eq',one_pow]
  by_cases hi : i ∈ A <;> simp [hi]

lemma quadraticExposure_pair (w : CladeWeights X) (i j : X) :
    quadraticExposure w (fun x => (if x = i then 1 else 0) + (if x = j then 1 else 0)) =
      rootExposure w i + rootExposure w j + 2 * sharedExposure w i j := by
  unfold quadraticExposure rootExposure sharedExposure
  rw [Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A _
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq']
  by_cases hi : i ∈ A <;> by_cases hj : j ∈ A <;> simp [hi,hj] <;> ring

lemma quadraticExposure_injective_on_laminar (w w' : CladeWeights X)
    (hw : LaminarWeights w) (hw' : LaminarWeights w')
    (he : ∀ v : X → ℝ, quadraticExposure w v = quadraticExposure w' v) : w = w' := by
  have hroot (i : X) : rootExposure w i = rootExposure w' i := by
    simpa only [quadraticExposure_single] using he (fun x => if x = i then 1 else 0)
  apply covariance_injective_on_laminar w w' hw hw'
  intro i j
  have hp := he (fun x => (if x = i then 1 else 0) + (if x = j then 1 else 0))
  simp only [quadraticExposure_pair,hroot] at hp
  linarith

noncomputable def quadraticPolynomial (w : CladeWeights X) : MvPolynomial X ℝ :=
  ∑ A : Finset X, MvPolynomial.C (w A : ℝ) * (∑ i ∈ A, MvPolynomial.X i)^2

lemma quadraticPolynomial_eval (w : CladeWeights X) (v : X → ℝ) :
    MvPolynomial.eval v (quadraticPolynomial w) = quadraticExposure w v := by
  simp [quadraticPolynomial,quadraticExposure]

lemma quadraticPolynomial_injective_on_laminar (w w' : CladeWeights X)
    (hw : LaminarWeights w) (hw' : LaminarWeights w')
    (he : quadraticPolynomial w = quadraticPolynomial w') : w = w' := by
  apply quadraticExposure_injective_on_laminar w w' hw hw'
  intro v
  simpa only [quadraticPolynomial_eval] using congrArg (MvPolynomial.eval v) he

/-- The separating allocation depends on a finite catalogue, never on a
hypothetical global ordering of the continuum of possible weighted trees. -/
lemma finite_catalogue_integer_quadratic_separation (H : Finset (CladeWeights X))
    (hH : ∀ w ∈ H, LaminarWeights w) :
    ∃ v : X → Nat, (∀ i, 0 < v i) ∧
      Set.InjOn (fun w => quadraticExposure w (fun i => (v i : ℝ))) (H : Set (CladeWeights X)) := by
  let P : MvPolynomial X ℝ :=
    ∏ ab ∈ H.offDiag, quadraticPolynomial ab.1 - quadraticPolynomial ab.2
  have hp : P ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro ab hab
    have hm := Finset.mem_offDiag.mp hab
    apply sub_ne_zero.mpr
    intro he
    exact hm.2.2 (quadraticPolynomial_injective_on_laminar ab.1 ab.2
      (hH ab.1 hm.1) (hH ab.2 hm.2.1) he)
  let S : Set ℝ := Set.range (fun n : Nat => ((n+1 : Nat) : ℝ))
  have hs : S.Infinite := by
    apply Set.infinite_range_of_injective
    intro a b he
    exact Nat.add_right_cancel (Nat.cast_injective he)
  have hex : ∃ x : X → ℝ, x ∈ Set.pi Set.univ (fun _ => S) ∧ MvPolynomial.eval x P ≠ 0 := by
    by_contra h
    push_neg at h
    apply hp
    apply MvPolynomial.funext_set (fun _ : X => S) (fun _ => hs)
    intro x hx
    simpa using h x hx
  obtain ⟨x,hx,hpx⟩ := hex
  have hx' (i : X) : ∃ n : Nat, ((n+1 : Nat) : ℝ) = x i := hx i (Set.mem_univ i)
  choose v hv using hx'
  refine ⟨fun i => v i+1,(fun i => Nat.succ_pos _),?_⟩
  intro w hw w' hw' he
  by_contra hne
  have hab : (w,w') ∈ H.offDiag := Finset.mem_offDiag.mpr ⟨hw,hw',hne⟩
  have hprod : (∏ ab ∈ H.offDiag,
      MvPolynomial.eval x (quadraticPolynomial ab.1 - quadraticPolynomial ab.2)) ≠ 0 := by
    simpa only [P,map_prod] using hpx
  have hfactor := (Finset.prod_ne_zero_iff.mp hprod) (w,w') hab
  apply hfactor
  simp only [map_sub,quadraticPolynomial_eval]
  have hxv : x = fun i => ((v i+1 : Nat) : ℝ) := funext (fun i => (hv i).symm)
  rw [hxv,he,sub_self]

end Coordinates

section PoissonPlacement

/-- Placement of s genuine compatible steps among n padded ticks. The factor
1/Λ is the sum of the two ordered half-rate orientations, not a quotient step. -/
noncomputable def placementTerm (Λ t q : ℝ) (s n : Nat) : ℝ :=
  Real.exp (-(Λ*t)) * (Λ*t)^n / (n.factorial : ℝ) *
    (n.choose s : ℝ) * q^(n-s) * Λ⁻¹^s

lemma placementTerm_nonnegative (Λ t q : ℝ) (hΛ : 0 ≤ Λ) (ht : 0 ≤ t)
    (hq : 0 ≤ q) (s n : Nat) : 0 ≤ placementTerm Λ t q s n := by
  unfold placementTerm
  positivity

lemma choose_div_factorial (n s : Nat) :
    ((n+s).choose s : ℝ) / ((n+s).factorial : ℝ) =
      1 / ((n.factorial : ℝ) * (s.factorial : ℝ)) := by
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hs : (s.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero s
  have hns : ((n+s).factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero (n+s)
  have h : ((n+s).choose s : ℝ) * (n.factorial : ℝ) * (s.factorial : ℝ) =
      ((n+s).factorial : ℝ) := by exact_mod_cast Nat.add_choose_mul_factorial_mul_factorial n s
  field_simp
  nlinarith

lemma placementTerm_shift (Λ t q : ℝ) (hΛ : Λ ≠ 0) (s n : Nat) :
    placementTerm Λ t q s (n+s) =
      (Real.exp (-(Λ*t)) * t^s / (s.factorial : ℝ)) *
        ((Λ*t*q)^n / (n.factorial : ℝ)) := by
  have hn : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero n
  have hs : (s.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero s
  unfold placementTerm
  rw [Nat.add_sub_cancel_right,pow_add]
  have hc := choose_div_factorial n s
  calc
    _ = Real.exp (-(Λ*t)) * (Λ*t)^n * (Λ*t)^s *
        (((n+s).choose s : ℝ) / ((n+s).factorial : ℝ)) * q^n * Λ⁻¹^s := by ring
    _ = _ := by rw [hc]; simp only [mul_pow,inv_pow]; field_simp; ring

/-- Exact cancellation of the padded clock; the upper bound therefore has
no growing carrier-cardinality constant hidden in it. -/
lemma placementTerm_hasSum (Λ t q : ℝ) (hΛ : Λ ≠ 0) (s : Nat) :
    HasSum (placementTerm Λ t q s)
      (Real.exp (-(Λ*t)) * t^s / (s.factorial : ℝ) * Real.exp (Λ*t*q)) := by
  have hs := (NormedSpace.expSeries_div_hasSum_exp (Λ*t*q)).mul_left
    (Real.exp (-(Λ*t)) * t^s / (s.factorial : ℝ))
  have hshift : HasSum (fun n => placementTerm Λ t q s (n+s))
      (Real.exp (-(Λ*t)) * t^s / (s.factorial : ℝ) * Real.exp (Λ*t*q)) := by
    simpa only [placementTerm_shift Λ t q hΛ s] using hs
  have hz : ∑ n ∈ Finset.range s, placementTerm Λ t q s n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    simp only [placementTerm,Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hn),Nat.cast_zero,mul_zero,zero_mul]
  simpa only [hz,add_zero] using (hasSum_nat_add_iff s).mp hshift

lemma poisson_compatible_step_sum (Λ t r : ℝ) (hΛ : 0 < Λ) (s : Nat) :
    (∑' n : Nat, placementTerm Λ t (1-r/Λ) s n) =
      (t^s / (s.factorial : ℝ)) * Real.exp (-r*t) := by
  rw [(placementTerm_hasSum Λ t (1-r/Λ) (ne_of_gt hΛ) s).tsum_eq]
  have he : -(Λ*t) + Λ*t*(1-r/Λ) = -r*t := by field_simp; ring
  calc
    _ = (t^s / (s.factorial : ℝ)) *
        (Real.exp (-(Λ*t)) * Real.exp (Λ*t*(1-r/Λ))) := by ring
    _ = _ := by rw [← Real.exp_add,he]

end PoissonPlacement

section KilledKernel
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourcePoissonExponential
variable {S : Type*} [Fintype S] [DecidableEq S]

noncomputable def goodMass (p : PMF S) (good : S → Prop) : ℝ :=
  ((p.map (fun s => decide (good s))) true).toReal

lemma goodMass_nonnegative (p : PMF S) (good : S → Prop) : 0 ≤ goodMass p good :=
  ENNReal.toReal_nonneg

lemma goodMass_pure (s : S) (good : S → Prop) :
    goodMass (PMF.pure s) good = if good s then 1 else 0 := by
  by_cases h : good s <;> simp [goodMass,h]

lemma goodMass_bind {A : Type*} (p : PMF A) (K : A → PMF S) (good : S → Prop) :
    goodMass (p.bind K) good = ∑' a, (p a).toReal * goodMass (K a) good := by
  unfold goodMass
  rw [PMF.map_bind,bind_probability_real]

noncomputable def kernelIteration (K : S → PMF S) : Nat → S → PMF S
  | 0,s => PMF.pure s
  | n+1,s => (K s).bind (kernelIteration K n)

/-- A sub-Markov row estimate on the proved reachable carrier propagates
through padded iterations. R is not an input to the eventual source theorem;
its invariance and the one-compatible-pair row bound are proved at use. -/
lemma killed_iteration_bound (K : S → PMF S) (R good : S → Prop)
    (q : ℝ) (hq : 0 ≤ q)
    (hR : ∀ s, R s → ∀ d ∈ (K s).support, R d)
    (hrow : ∀ s, R s → goodMass (K s) good ≤ q * (if good s then 1 else 0))
    (n : Nat) (s : S) (hs : R s) :
    goodMass (kernelIteration K n s) good ≤ q^n * (if good s then 1 else 0) := by
  induction n generalizing s with
  | zero => simp only [kernelIteration,goodMass_pure,pow_zero,one_mul,le_refl]
  | succ n ih =>
    rw [kernelIteration,goodMass_bind,tsum_fintype]
    calc
      _ ≤ ∑ d : S, (K s d).toReal * (q^n * (if good d then 1 else 0)) := by
        apply Finset.sum_le_sum
        intro d _
        by_cases hd : K s d = 0
        · simp only [hd,ENNReal.toReal_zero,zero_mul,le_refl]
        · apply mul_le_mul_of_nonneg_left (ih d (hR s hs d ((PMF.mem_support_iff _ _).mpr hd)))
          exact ENNReal.toReal_nonneg
      _ = q^n * goodMass (K s) good := by
        rw [goodMass,PMF.map,bind_probability_real,tsum_fintype,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro d _
        by_cases hg : good d <;> simp [hg,mul_assoc,mul_left_comm,mul_comm]
      _ ≤ q^n * (q * (if good s then 1 else 0)) :=
        mul_le_mul_of_nonneg_left (hrow s hs) (pow_nonneg hq n)
      _ = _ := by rw [pow_succ]; ring

lemma poisson_power_hasSum (a : ℝ≥0) (q : ℝ) :
    HasSum (fun n : Nat => (countPMF a n).toReal * q^n)
      (Real.exp ((a : ℝ)*(q-1))) := by
  have h := (NormedSpace.expSeries_div_hasSum_exp ((a : ℝ)*q)).mul_left
    (Real.exp (-(a : ℝ)))
  have he : Real.exp (-(a : ℝ)) * Real.exp ((a : ℝ)*q) =
      Real.exp ((a : ℝ)*(q-1)) := by rw [← Real.exp_add]; congr 1; ring
  simpa only [countPMF_real,mul_pow,he,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm]
    using h

lemma killed_poisson_bound (K : S → PMF S) (R good : S → Prop)
    (q : ℝ) (hq : 0 ≤ q)
    (hR : ∀ s, R s → ∀ d ∈ (K s).support, R d)
    (hrow : ∀ s, R s → goodMass (K s) good ≤ q * (if good s then 1 else 0))
    (a : ℝ≥0) (s : S) (hs : R s) (hgood : good s) :
    goodMass ((countPMF a).bind (fun n => kernelIteration K n s)) good ≤
      Real.exp ((a : ℝ)*(q-1)) := by
  rw [goodMass_bind]
  have hbound (n : Nat) :
      (countPMF a n).toReal * goodMass (kernelIteration K n s) good ≤
        (countPMF a n).toReal * q^n := by
    apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
    simpa only [hgood,if_true,mul_one] using killed_iteration_bound K R good q hq hR hrow n s hs
  have hup := poisson_power_hasSum a q
  have hlow : Summable (fun n => (countPMF a n).toReal * goodMass (kernelIteration K n s) good) :=
    Summable.of_nonneg_of_le (fun n => mul_nonneg ENNReal.toReal_nonneg (goodMass_nonnegative _ _))
      hbound hup.summable
  exact (tsum_le_tsum hbound hlow hup.summable).trans_eq hup.tsum_eq

end KilledKernel

section ForestRepresentation
variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]

/-- An anchor is chosen inside each actual whole tree, so this is total even
when Copy is empty: then no WellLabelledTree Copy exists. -/
noncomputable def treeAnchor (t : WellLabelledTree Copy) : Copy :=
  Classical.choose (UnifiedLean.Source.SourceForestSilentPruning.genealogy_leaves_nonempty t.val)

lemma treeAnchor_mem (t : WellLabelledTree Copy) : treeAnchor t ∈ t.val.leaves :=
  Classical.choose_spec (UnifiedLean.Source.SourceForestSilentPruning.genealogy_leaves_nonempty t.val)

noncomputable def forestOwner (F : Forest Copy) (hF : Partition F) (x : Copy) :
    WellLabelledTree Copy := Classical.choose (hF.2 x)

lemma forestOwner_mem (F : Forest Copy) (hF : Partition F) (x : Copy) :
    forestOwner F hF x ∈ F := (Classical.choose_spec (hF.2 x)).1

lemma forestOwner_contains (F : Forest Copy) (hF : Partition F) (x : Copy) :
    x ∈ (forestOwner F hF x).val.leaves := (Classical.choose_spec (hF.2 x)).2

lemma forestOwner_eq (F : Forest Copy) (hF : Partition F)
    (t : WellLabelledTree Copy) (ht : t ∈ F) (x : Copy) (hx : x ∈ t.val.leaves) :
    forestOwner F hF x = t := by
  by_contra h
  exact Finset.disjoint_left.mp
    (hF.1 _ (forestOwner_mem F hF x) t ht h) (forestOwner_contains F hF x) hx

lemma treeAnchor_injective_on (F : Forest Copy) (hF : Partition F)
    {t u : WellLabelledTree Copy} (ht : t ∈ F) (hu : u ∈ F)
    (he : treeAnchor t = treeAnchor u) : t = u := by
  by_contra h
  exact Finset.disjoint_left.mp (hF.1 t ht u hu h)
    (treeAnchor_mem t) (he.symm ▸ treeAnchor_mem u)

@[simp] lemma forestOwner_anchor (F : Forest Copy) (hF : Partition F)
    (t : WellLabelledTree Copy) (ht : t ∈ F) :
    forestOwner F hF (treeAnchor t) = t :=
  forestOwner_eq F hF t ht _ (treeAnchor_mem t)

noncomputable def forestRootState {V E : Type*} (root : V)
    (register : V → Bool) (F : Forest Copy) (hF : Partition F) : State V E Copy where
  live := F.image treeAnchor
  ancestor x := treeAnchor (forestOwner F hF x)
  genealogy x := (forestOwner F hF x).val
  location _ := .rootPopulation root
  register := register
  history := []

lemma forestRootState_valid {V E : Type*} (root : V) (register : V → Bool)
    (F : Forest Copy) (hF : Partition F) : Valid (forestRootState (E := E) root register F hF) := by
  constructor
  · intro x
    exact Finset.mem_image.mpr ⟨forestOwner F hF x,forestOwner_mem F hF x,rfl⟩
  · intro l hl
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hl
    simp only [forestRootState,forestOwner_anchor F hF t ht]
  · intro l hl x
    obtain ⟨t,ht,rfl⟩ := Finset.mem_image.mp hl
    simp only [forestRootState,forestOwner_anchor F hF t ht]
    constructor
    · intro hx
      rw [forestOwner_eq F hF t ht x hx]
    · intro he
      have ho := treeAnchor_injective_on F hF (forestOwner_mem F hF x) ht he
      simpa only [ho] using forestOwner_contains F hF x
  · intro l hl
    exact (forestOwner F hF l).property

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

lemma forestRootState_sourceValid (N : RootedBinary V E X) (sample : Copy → X)
    (register : V → Bool) (F : Forest Copy) (hF : Partition F) :
    SourceValid N sample (forestRootState N.root register F hF) := by
  refine ⟨forestRootState_valid N.root register F hF,?_⟩
  intro x
  exact ⟨rfl,N.rooted _⟩

/-- A concrete proof transport into the existing admitted original source
carrier. It neither changes the evaluator nor assumes its completion law. -/
noncomputable def forestRootCode (N : RootedBinary V E X) (sample : Copy → X)
    (register : V → Bool) (F : Forest Copy) (hF : Partition F) :
    UnifiedLean.Source.UniformizedSourceStep.Code N sample :=
  UnifiedLean.Source.FiniteSourceSnapshot.admittedCode N sample
    (forestRootState N.root register F hF) (forestRootState_sourceValid N sample register F hF)

lemma forestRootCode_ancestral (N : RootedBinary V E X) (sample : Copy → X)
    (register : V → Bool) (F : Forest Copy) (hF : Partition F) :
    UnifiedLean.Source.SourceAncestralCompletion.AncestralRoot N
      (forestRootCode N sample register F hF) := by
  intro x
  exact UnifiedLean.Source.FiniteSourceSnapshot.decode_encode_copyLocation N.root
    (forestRootState N.root register F hF) (forestRootState_valid N.root register F hF) x

lemma forestRootCode_live (N : RootedBinary V E X) (sample : Copy → X)
    (register : V → Bool) (F : Forest Copy) (hF : Partition F) :
    (UnifiedLean.Source.UniformizedSourceStep.state (forestRootCode N sample register F hF)).live =
      F.image treeAnchor := rfl

lemma forestRootCode_ancestor (N : RootedBinary V E X) (sample : Copy → X)
    (register : V → Bool) (F : Forest Copy) (hF : Partition F) (x : Copy) :
    (UnifiedLean.Source.UniformizedSourceStep.state (forestRootCode N sample register F hF)).ancestor x =
      treeAnchor (forestOwner F hF x) := rfl

lemma forestRootCode_genealogy_anchor (N : RootedBinary V E X) (sample : Copy → X)
    (register : V → Bool) (F : Forest Copy) (hF : Partition F)
    (t : WellLabelledTree Copy) (ht : t ∈ F) :
    (UnifiedLean.Source.UniformizedSourceStep.state (forestRootCode N sample register F hF)).genealogy
      (treeAnchor t) = t.val := by
  have hl : treeAnchor t ∈ (forestRootState (E := E) N.root register F hF).live :=
    Finset.mem_image.mpr ⟨t,ht,rfl⟩
  rw [UnifiedLean.Source.FiniteSourceSnapshot.decode_encode_live_genealogy N.root
    (forestRootState N.root register F hF) (forestRootState_valid N.root register F hF) hl]
  simp only [forestRootState,forestOwner_anchor F hF t ht]

lemma forestRootCode_forest (N : RootedBinary V E X) (sample : Copy → X)
    (register : V → Bool) (F : Forest Copy) (hF : Partition F) :
    forestCode N (forestRootCode N sample register F hF) = F := by
  ext t
  rw [forestCode,mem_actualForest]
  constructor
  · rintro ⟨l,hl,he⟩
    rw [forestRootCode_live] at hl
    obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hl
    rw [forestRootCode_genealogy_anchor N sample register F hF u hu] at he
    exact (Subtype.ext he) ▸ hu
  · intro ht
    exact ⟨treeAnchor t,Finset.mem_image.mpr ⟨t,ht,rfl⟩,
      forestRootCode_genealogy_anchor N sample register F hF t ht⟩

/-- Completion coefficient and opacity suppliers may now be reused on every
independent partition forest, with the same allocation and genuine root state. -/
lemma ordinaryCompletion_eq_source_root (N : RootedBinary V E X) (sample : Copy → X)
    (r : PositivePairRates E) (register : V → Bool) (F : Forest Copy) (hF : Partition F) :
    (ordinaryCompletion F).map forestObservation =
      (UnifiedLean.Source.SourceAncestralCompletion.ancestralCompletion N r (Fintype.card Copy)
        (forestRootCode N sample register F hF)).map
        (fun d => UnifiedLean.Source.UnrankedGenealogyObservation.sourceUnrankedForest
          (UnifiedLean.Source.UniformizedSourceStep.state d) Finset.univ) := by
  rw [actual_ordinary_completed_observation N r _
    (forestRootCode_ancestral N sample register F hF),forestRootCode_forest]

end ForestRepresentation

section IndependentCombReader
variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
open DotG34.SpecifiedCombEvent DotG34.SpecifiedCombSelectedObservation
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceCompletionHarmonic

/-- A whole prefix tree and the remaining singletons, with all original copy
labels covered. Child order is retained in F and compared by the accepted
child-swap quotient only in the prescribed prefix. -/
structure ForestFrontier (F : Forest Copy) (t : Genealogy Copy) (rest : List Copy) : Prop where
  prefix : ∃ g ∈ F, UnorderedEquiv g.val t
  singleton : ∀ a ∈ rest, treeLeaf a ∈ F
  cover : ∀ x, x ∈ t.leaves ∨ x ∈ rest
  disjoint : ∀ a ∈ rest, a ∉ t.leaves
  nodup : rest.Nodup

lemma forestRootCode_frontier (N : RootedBinary V E X) (sample : Copy → X)
    (register : V → Bool) (F : Forest Copy) (hF : Partition F)
    (t : Genealogy Copy) (rest : List Copy) (h : ForestFrontier F t rest) :
    ∃ pref : Copy, CombFrontier (state (forestRootCode N sample register F hF)) t pref rest := by
  obtain ⟨g,hg,hgt⟩ := h.prefix
  refine ⟨treeAnchor g,?_,?_,?_,h.cover,h.disjoint,h.nodup⟩
  · exact Finset.mem_image.mpr ⟨g,hg,rfl⟩
  · simpa only [forestRootCode_genealogy_anchor N sample register F hF g hg] using hgt
  · intro a ha
    have hm := h.singleton a ha
    have ho : forestOwner F hF a = treeLeaf a :=
      forestOwner_eq F hF (treeLeaf a) hm a (Finset.mem_singleton_self a)
    rw [forestRootCode_ancestor,ho,
      forestRootCode_genealogy_anchor N sample register F hF (treeLeaf a) hm]
    rfl

noncomputable def completionCombMass (F : Forest Copy) (target : Genealogy Copy) : ℝ≥0∞ :=
  ((ordinaryCompletion F).map forestObservation) {toUnranked target}

lemma completionCombMass_source_reader (N : RootedBinary V E X) (sample : Copy → X)
    (r : PositivePairRates E) (register : V → Bool) (F : Forest Copy) (hF : Partition F)
    (b : Copy) (target : Genealogy Copy) :
    completionCombMass F target = completionTreeLaw N r b
      (forestRootCode N sample register F hF) (toUnranked target) := by
  unfold completionCombMass
  rw [ordinaryCompletion_eq_source_root N sample r register F hF]
  exact actual_completed_forest_singleton_mass N r _
    (forestRootCode_ancestral N sample register F hF) b _

/-- Exact inherited coefficient, now on the independent forest carrier. -/
lemma forestFrontier_completion_probability (N : RootedBinary V E X) (sample : Copy → X)
    (r : PositivePairRates E) (register : V → Bool) (F : Forest Copy) (hF : Partition F)
    (b : Copy) (t : Genealogy Copy) (rest : List Copy)
    (h : ForestFrontier F t rest) (hb : b ∈ t.leaves) :
    completionCombMass F (rest.foldl (fun u a => .graft u (.leaf a)) t) =
      ENNReal.ofReal (2^rest.length /
        ((Nat.factorial (rest.length+1) : ℝ) * (Nat.factorial rest.length : ℝ))) := by
  obtain ⟨pref,hpref⟩ := forestRootCode_frontier N sample register F hF t rest h
  rw [completionCombMass_source_reader N sample r register F hF b]
  exact actual_frontier_comb_closed_form N r b rest _ t pref
    (forestRootCode_ancestral N sample register F hF) hpref hb

lemma independent_wrong_clade_completion_zero (N : RootedBinary V E X) (sample : Copy → X)
    (r : PositivePairRates E) (register : V → Bool) (F : Forest Copy) (hF : Partition F)
    (b : Copy) (target : Genealogy Copy) (g : WellLabelledTree Copy) (hg : g ∈ F)
    (A : Finset Copy) (hA : A ∈ internalClades g.val)
    (hwrong : A ∉ internalClades target) : completionCombMass F target = 0 := by
  rw [completionCombMass_source_reader N sample r register F hF b]
  apply (PMF.apply_eq_zero_iff _ _).mpr
  intro hevent
  obtain ⟨d,hd,he⟩ := (PMF.mem_support_map_iff _ _ _).mp hevent
  have hc : codeClade N A (treeAnchor g) (forestRootCode N sample register F hF) := by
    have ho := forestOwner_anchor F hF g hg
    simpa only [codeClade,forestRootCode_ancestor,ho,
      forestRootCode_genealogy_anchor N sample register F hF g hg] using hA
  exact actual_completion_excludes_wrong_tree N r b (treeAnchor g) target _ d
    (forestRootCode_ancestral N sample register F hF) A hc hwrong hd he

end IndependentCombReader

section ForestOpacity
variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
open DotG34.SpecifiedCombEvent

lemma partition_trees_equal_of_overlap (F : Forest Copy) (hF : Partition F)
    (g h : WellLabelledTree Copy) (hg : g ∈ F) (hh : h ∈ F)
    (x : Copy) (hxg : x ∈ g.val.leaves) (hxh : x ∈ h.val.leaves) : g = h := by
  by_contra hne
  exact Finset.disjoint_left.mp (hF.1 g hg h hh hne) hxg hxh

lemma forestFrontier_exact (F : Forest Copy) (hF : Partition F)
    (t : Genealogy Copy) (rest : List Copy) (h : ForestFrontier F t rest)
    (g : WellLabelledTree Copy) (hg : g ∈ F) (hgt : UnorderedEquiv g.val t) :
    F = insert g (rest.toFinset.image treeLeaf) := by
  ext u
  constructor
  · intro hu
    obtain ⟨x,hx⟩ := UnifiedLean.Source.SourceForestSilentPruning.genealogy_leaves_nonempty u.val
    rcases h.cover x with hxt | hxr
    · have hxg : x ∈ g.val.leaves := by rwa [unordered_leaves hgt]
      have he := partition_trees_equal_of_overlap F hF u g hu hg x hx hxg
      exact Finset.mem_insert.mpr (Or.inl he)
    · have hxleaf : x ∈ (treeLeaf x : WellLabelledTree Copy).val.leaves := Finset.mem_singleton_self x
      have he := partition_trees_equal_of_overlap F hF u (treeLeaf x) hu
        (h.singleton x hxr) x hx hxleaf
      exact Finset.mem_insert.mpr (Or.inr
        (Finset.mem_image.mpr ⟨x,List.mem_toFinset.mpr hxr,he.symm⟩))
  · intro hu
    rcases Finset.mem_insert.mp hu with rfl | hu
    · exact hg
    · obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hu
      exact h.singleton a (List.mem_toFinset.mp ha)

lemma treeLeaf_injective : Function.Injective (treeLeaf (Copy := Copy)) := by
  intro a b he
  exact Genealogy.leaf.inj (congrArg Subtype.val he)

lemma forestFrontier_card (F : Forest Copy) (hF : Partition F)
    (t : Genealogy Copy) (rest : List Copy) (h : ForestFrontier F t rest) :
    F.card = rest.length+1 := by
  obtain ⟨g,hg,hgt⟩ := h.prefix
  have hnot : g ∉ rest.toFinset.image treeLeaf := by
    rintro hm
    obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hm
    have hat : a ∈ t.leaves := by
      rw [← unordered_leaves hgt,← he]
      exact Finset.mem_singleton_self a
    exact h.disjoint a (List.mem_toFinset.mp ha) hat
  rw [forestFrontier_exact F hF t rest h g hg hgt,
    Finset.card_insert_of_notMem hnot,Finset.card_image_of_injective _ treeLeaf_injective,
    List.toFinset_card_of_nodup h.nodup]

/-- A forbidden opaque clade is a permanent property of a whole carried tree. -/
def ForestHasClade (F : Forest Copy) (A : Finset Copy) : Prop :=
  ∃ g ∈ F, A ∈ internalClades g.val

lemma mergeForest_preserves_clade (F : Forest Copy) (A : Finset Copy)
    (a b : WellLabelledTree Copy) (hd : Disjoint a.val.leaves b.val.leaves)
    (h : ForestHasClade F A) : ForestHasClade (mergeForest F a b hd) A := by
  obtain ⟨g,hg,hA⟩ := h
  by_cases hga : g = a
  · subst g
    refine ⟨treeGraft a b hd,Finset.mem_insert_self _ _,?_⟩
    exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hA)
  · by_cases hgb : g = b
    · subst g
      refine ⟨treeGraft a b hd,Finset.mem_insert_self _ _,?_⟩
      exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hA)
    · exact ⟨g,Finset.mem_insert_of_mem
        (Finset.mem_erase.mpr ⟨hgb,Finset.mem_erase.mpr ⟨hga,hg⟩⟩),hA⟩

lemma pairAction_preserves_clade (F : Forest Copy) (A B : Finset Copy)
    (p : WellLabelledTree Copy × WellLabelledTree Copy) (h : ForestHasClade F B) :
    ForestHasClade (pairAction F A p) B := by
  unfold pairAction
  split_ifs with hp
  · exact mergeForest_preserves_clade F B p.1 p.2 _ h
  · exact h

lemma cladeStep_preserves_clade (F : Forest Copy) (A B : Finset Copy)
    (h : ForestHasClade F B) {G : Forest Copy} (hG : G ∈ (cladeStep A F).support) :
    ForestHasClade G B := by
  obtain ⟨p,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hG
  cases p with
  | none => exact h
  | some p => exact pairAction_preserves_clade F A B p h

lemma cladeIteration_preserves_clade (F : Forest Copy) (A B : Finset Copy)
    (h : ForestHasClade F B) (n : Nat) {G : Forest Copy}
    (hG : G ∈ (cladeIteration A n F).support) : ForestHasClade G B := by
  induction n generalizing F with
  | zero =>
    have he : G = F := by simpa only [cladeIteration,PMF.mem_support_pure_iff] using hG
    simpa only [he] using h
  | succ n ih =>
    obtain ⟨M,hM,hG⟩ := (PMF.mem_support_bind_iff _ _ _).mp hG
    exact ih M (cladeStep_preserves_clade F A B h hM) hG

lemma cladeKernel_preserves_clade (F : Forest Copy) (A B : Finset Copy)
    (h : ForestHasClade F B) (t : ℝ≥0) {G : Forest Copy}
    (hG : G ∈ (cladeKernel A t F).support) : ForestHasClade G B := by
  obtain ⟨n,_,hG⟩ := (PMF.mem_support_bind_iff _ _ _).mp hG
  exact cladeIteration_preserves_clade F A B h n hG

lemma forestProgram_preserves_clade (ops : List (Finset Copy × ℝ≥0))
    (F : Forest Copy) (A : Finset Copy) (h : ForestHasClade F A) {G : Forest Copy}
    (hG : G ∈ (forestProgram ops F).support) : ForestHasClade G A := by
  induction ops generalizing F with
  | nil =>
    have he : G = F := by simpa only [forestProgram,PMF.mem_support_pure_iff] using hG
    simpa only [he] using h
  | cons op ops ih =>
    obtain ⟨M,hM,hG⟩ := (PMF.mem_support_bind_iff _ _ _).mp hG
    exact ih M (cladeKernel_preserves_clade F op.1 A h op.2 hM) hG

end ForestOpacity

section ActiveRootCounting
variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]

noncomputable def activeForest (F : Forest Copy) (A : Finset Copy) : Forest Copy :=
  F.filter (fun t => t.val.leaves ⊆ A)

lemma partition_unique_leaf_sum (F : Forest Copy) (hF : Partition F) (x : Copy) :
    (∑ t ∈ F, if x ∈ t.val.leaves then (1 : Nat) else 0) = 1 := by
  rw [Finset.sum_eq_single (forestOwner F hF x)]
  · simp [forestOwner_contains F hF x]
  · intro t ht hne
    have hn : x ∉ t.val.leaves := by
      intro hx
      exact hne (forestOwner_eq F hF t ht x hx).symm
    simp [hn]
  · intro hn
    exact False.elim (hn (forestOwner_mem F hF x))

lemma partition_intersection_card (F : Forest Copy) (hF : Partition F) (A : Finset Copy) :
    (∑ t ∈ F, (t.val.leaves ∩ A).card) = A.card := by
  have hterm (t : WellLabelledTree Copy) :
      (t.val.leaves ∩ A).card = ∑ x ∈ A, if x ∈ t.val.leaves then (1 : Nat) else 0 := by
    simp [Finset.sum_boole,Finset.filter_mem_eq_inter,Finset.inter_comm]
  simp_rw [hterm]
  rw [Finset.sum_comm]
  simp only [partition_unique_leaf_sum F hF,Finset.sum_const,smul_eq_mul,mul_one]

lemma partition_total_leaf_card (F : Forest Copy) (hF : Partition F) :
    (∑ t ∈ F, t.val.leaves.card) = Fintype.card Copy := by
  simpa only [Finset.inter_univ,Finset.card_univ] using partition_intersection_card F hF Finset.univ

lemma partition_merger_loss_sum (F : Forest Copy) (hF : Partition F) :
    (∑ t ∈ F, (t.val.leaves.card-1)) + F.card = Fintype.card Copy := by
  calc
    _ = ∑ t ∈ F, ((t.val.leaves.card-1)+1) := by
      rw [Finset.sum_add_distrib]
      simp
    _ = ∑ t ∈ F, t.val.leaves.card := by
      apply Finset.sum_congr rfl
      intro t _
      have hp := Finset.card_pos.mpr
        (UnifiedLean.Source.SourceForestSilentPruning.genealogy_leaves_nonempty t.val)
      omega
    _ = _ := partition_total_leaf_card F hF

/-- Straddling trees are charged to the GLOBAL merger loss. This bound does
not assume that every live tree is contained in or disjoint from A. -/
lemma active_count_add_loss_bound (F : Forest Copy) (hF : Partition F) (A : Finset Copy) :
    A.card ≤ (Fintype.card Copy-F.card) + (activeForest F A).card := by
  have hterm (t : WellLabelledTree Copy) :
      (t.val.leaves ∩ A).card ≤ (t.val.leaves.card-1) +
        (if t.val.leaves ⊆ A then 1 else 0) := by
    have hp := Finset.card_pos.mpr
      (UnifiedLean.Source.SourceForestSilentPruning.genealogy_leaves_nonempty t.val)
    by_cases ht : t.val.leaves ⊆ A
    · rw [Finset.inter_eq_left.mpr ht,if_pos ht]
      omega
    · have hss : t.val.leaves ∩ A ⊂ t.val.leaves := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨Finset.inter_subset_left,?_⟩
        intro he
        exact ht (he ▸ Finset.inter_subset_right)
      have hc := Finset.card_lt_card hss
      simp only [ht,if_false,add_zero]
      omega
  have hsum := Finset.sum_le_sum (s := F) (fun t _ => hterm t)
  rw [partition_intersection_card F hF,Finset.sum_add_distrib] at hsum
  have hcount : (∑ t ∈ F, if t.val.leaves ⊆ A then (1 : Nat) else 0) =
      (activeForest F A).card := by simp [activeForest,Finset.sum_boole]
  rw [hcount] at hsum
  have hloss := partition_merger_loss_sum F hF
  have he : (∑ t ∈ F, (t.val.leaves.card-1)) = Fintype.card Copy-F.card := by omega
  simpa only [he] using hsum

lemma active_count_lower (F : Forest Copy) (hF : Partition F) (A : Finset Copy)
    (s : Nat) (hloss : Fintype.card Copy-F.card ≤ s) :
    A.card-s ≤ (activeForest F A).card := by
  have h := active_count_add_loss_bound F hF A
  omega

end ActiveRootCounting

section SourceChoiceReuse
variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
open DotG34.SpecifiedCombEvent
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceAncestralCompletion

noncomputable def forbiddenForest (target : Genealogy Copy) (F : Forest Copy) : Prop :=
  ∃ A : Finset Copy, ForestHasClade F A ∧ A ∉ internalClades target

lemma source_codeClade_forest (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (A : Finset Copy) (x : Copy) (h : codeClade N A x s) :
    ForestHasClade (forestCode N s) A := by
  let l := (state s).ancestor x
  have hl : l ∈ (state s).live := s.property.forest.ancestor_live x
  let t : WellLabelledTree Copy := ⟨(state s).genealogy l,s.property.forest.wellLabelled l hl⟩
  refine ⟨t,(mem_actualForest (state s) (code_forest_valid N s) t).mpr ⟨l,hl,rfl⟩,h⟩

lemma source_frontier_forest (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (t : Genealogy Copy) (pref : Copy) (rest : List Copy)
    (h : CombFrontier (state s) t pref rest) : ForestFrontier (forestCode N s) t rest := by
  refine ⟨?_,?_,h.cover,h.disjoint,h.nodup⟩
  · let g : WellLabelledTree Copy :=
      ⟨(state s).genealogy pref,s.property.forest.wellLabelled pref h.prefix_live⟩
    exact ⟨g,(mem_actualForest (state s) (code_forest_valid N s) g).mpr
      ⟨pref,h.prefix_live,rfl⟩,h.prefix_tree⟩
  · intro a ha
    apply (mem_actualForest (state s) (code_forest_valid N s) (treeLeaf a)).mpr
    exact ⟨(state s).ancestor a,s.property.forest.ancestor_live a,h.singleton a ha⟩

lemma root_pair_frontier_or_forbidden (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (t : Genealogy Copy) (pref next b : Copy) (rest : List Copy)
    (hroot : AncestralRoot N s) (h : CombFrontier (state s) t pref (next::rest))
    (hb : b ∈ t.leaves) (q : Choice N s) :
    ForestFrontier (forestCode N (stepDestination N s (some q))) (.graft t (.leaf next)) rest ∨
      forbiddenForest ((next::rest).foldl (fun u a => .graft u (.leaf a)) t)
        (forestCode N (stepDestination N s (some q))) := by
  by_cases hq : (q.2.val.1 = pref ∧ q.2.val.2 = next) ∨
      (q.2.val.1 = next ∧ q.2.val.2 = pref)
  · exact Or.inl (source_frontier_forest N _ _ _ _ (actual_correct_choice_frontier N s t pref next rest h q hq))
  · obtain ⟨A,hA,hnot⟩ := actual_wrong_choice_clade N s t pref next b rest h hb q hq
    exact Or.inr ⟨A,source_codeClade_forest N _ A q.2.val.1 hA,hnot⟩

lemma nonforbidden_root_pair_count (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (t : Genealogy Copy) (pref next b : Copy) (rest : List Copy)
    (hroot : AncestralRoot N s) (h : CombFrontier (state s) t pref (next::rest))
    (hb : b ∈ t.leaves) :
    ((rootPairs (forestCode N s)).filter (fun p =>
      ¬ forbiddenForest ((next::rest).foldl (fun u a => .graft u (.leaf a)) t)
        (pairAction (forestCode N s) Finset.univ p))).card ≤ 2 := by
  let E := rootForestChoices N s hroot
  let chosen := prescribedChoices N s hroot t pref next rest h
  have hsub :
      (rootPairs (forestCode N s)).filter (fun p =>
        ¬ forbiddenForest ((next::rest).foldl (fun u a => .graft u (.leaf a)) t)
          (pairAction (forestCode N s) Finset.univ p)) ⊆
        chosen.image (fun q => (rootForestChoice N s hroot q).val) := by
    intro p hp
    have hp' := Finset.mem_filter.mp hp
    let q : Choice N s := E.symm ⟨p,hp'.1⟩
    have he : (rootForestChoice N s hroot q).val = p :=
      congrArg Subtype.val (E.apply_symm_apply ⟨p,hp'.1⟩)
    have hq : q ∈ chosen := by
      apply (mem_prescribedChoices N s hroot t pref next rest h q).mpr
      by_contra hwrong
      obtain ⟨A,hA,hnot⟩ := actual_wrong_choice_clade N s t pref next b rest h hb q hwrong
      have hf : forbiddenForest ((next::rest).foldl (fun u a => .graft u (.leaf a)) t)
          (forestCode N (stepDestination N s (some q))) :=
        ⟨A,source_codeClade_forest N _ A q.2.val.1 hA,hnot⟩
      rw [rootForestChoice_destination N s hroot q,he] at hf
      exact hp'.2 hf
    exact Finset.mem_image.mpr ⟨q,hq,he⟩
  calc
    _ ≤ (chosen.image (fun q => (rootForestChoice N s hroot q).val)).card := Finset.card_le_card hsub
    _ ≤ chosen.card := Finset.card_image_le
    _ = 2 := prescribedChoices_card N s hroot t pref next rest h

end SourceChoiceReuse

section ProperTaxonForests
variable {X Copy : Type*} [Fintype X] [Fintype Copy]
variable [DecidableEq X] [DecidableEq Copy]
open DotG34.SpecifiedCombEvent

/-- Before root completion, no carried tree has already collected all original
 taxa. This follows from the actual proper-clade schedule, not compatibility. -/
def TaxonProperForest (sample : Copy → X) (F : Forest Copy) : Prop :=
  ∀ g ∈ F, g.val.leaves.image sample ≠ Finset.univ

lemma initialForest_taxonProper (sample : Copy → X) (hn : 2 ≤ Fintype.card X) :
    TaxonProperForest sample initialForest := by
  intro g hg
  obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hg
  intro he
  have hc := congrArg Finset.card he
  simp only [treeLeaf,Genealogy.leaves,Finset.image_singleton,Finset.card_singleton,
    Finset.card_univ] at hc
  omega

lemma pairAction_taxonProper (sample : Copy → X) (F : Forest Copy)
    (hF : TaxonProperForest sample F) (A : Finset X) (hA : A ≠ Finset.univ)
    (p : WellLabelledTree Copy × WellLabelledTree Copy) :
    TaxonProperForest sample (pairAction F (cladeCopySet sample A) p) := by
  unfold pairAction
  split_ifs with hp
  · intro g hg
    rcases Finset.mem_insert.mp hg with he | hg
    · subst g
      have hsub : (treeGraft p.1 p.2 hp.2.2.2.2.2).val.leaves.image sample ⊆ A := by
        intro y hy
        obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp hy
        rcases Finset.mem_union.mp hx with hx | hx
        · exact (Finset.mem_filter.mp (hp.2.2.2.1 hx)).2
        · exact (Finset.mem_filter.mp (hp.2.2.2.2.1 hx)).2
      intro he
      rw [he] at hsub
      exact hA (Finset.eq_univ_iff_forall.mpr (fun x => hsub (Finset.mem_univ x)))
    · exact hF g (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hg))
  · exact hF

lemma cladeStep_taxonProper (sample : Copy → X) (F : Forest Copy)
    (hF : TaxonProperForest sample F) (A : Finset X) (hA : A ≠ Finset.univ)
    {G : Forest Copy} (hG : G ∈ (cladeStep (cladeCopySet sample A) F).support) :
    TaxonProperForest sample G := by
  obtain ⟨p,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hG
  cases p with
  | none => exact hF
  | some p => exact pairAction_taxonProper sample F hF A hA p

lemma cladeIteration_taxonProper (sample : Copy → X) (A : Finset X)
    (hA : A ≠ Finset.univ) (k : Nat) (F : Forest Copy)
    (hF : TaxonProperForest sample F) {G : Forest Copy}
    (hG : G ∈ (cladeIteration (cladeCopySet sample A) k F).support) :
    TaxonProperForest sample G := by
  induction k generalizing F with
  | zero =>
      have he : G = F := by simpa only [cladeIteration,PMF.mem_support_pure_iff] using hG
      simpa only [he] using hF
  | succ k ih =>
      obtain ⟨M,hM,hG⟩ := (PMF.mem_support_bind_iff _ _ _).mp hG
      exact ih M (cladeStep_taxonProper sample F hF A hA hM) hG

lemma cladeKernel_taxonProper (sample : Copy → X) (A : Finset X)
    (hA : A ≠ Finset.univ) (t : ℝ≥0) (F : Forest Copy)
    (hF : TaxonProperForest sample F) {G : Forest Copy}
    (hG : G ∈ (cladeKernel (cladeCopySet sample A) t F).support) :
    TaxonProperForest sample G := by
  obtain ⟨k,_,hk⟩ := (PMF.mem_support_bind_iff _ _ _).mp hG
  exact cladeIteration_taxonProper sample A hA k F hF hk

lemma fold_comb_leaves (t : Genealogy Copy) (as : List Copy) :
    (as.foldl (fun u a => .graft u (.leaf a)) t).leaves = t.leaves ∪ as.toFinset := by
  induction as generalizing t with
  | nil => simp
  | cons a as ih =>
      rw [List.foldl_cons,ih]
      ext x
      simp only [Genealogy.leaves,List.toFinset_cons,Finset.mem_union,
        Finset.mem_singleton,Finset.mem_insert]
      tauto

lemma comb_leaves_eq (b : Copy) (as : List Copy) :
    (comb b as).leaves = insert b as.toFinset := by
  simpa only [comb,Genealogy.leaves,Finset.singleton_union] using fold_comb_leaves (.leaf b) as

/-- The first n distinct spine labels visit every taxon. Any compatible prefix
 still carried below the root therefore has fewer than n−1 genuine mergers. -/
lemma proper_frontier_prefix_length (sample : Copy → X) (F : Forest Copy)
    (hproper : TaxonProperForest sample F) (b : Copy) (as : List Copy) (n k : Nat)
    (hcover : (insert b (as.take (n-1)).toFinset).image sample = Finset.univ)
    (hfront : ForestFrontier F (comb b (as.take k)) (as.drop k)) : k < n-1 := by
  by_contra hlt
  have hnk : n-1 ≤ k := Nat.le_of_not_gt hlt
  obtain ⟨g,hg,hgt⟩ := hfront.prefix
  apply hproper g hg
  apply Finset.eq_univ_iff_forall.mpr
  intro x
  have hx : x ∈ (insert b (as.take (n-1)).toFinset).image sample := by
    rw [hcover]
    exact Finset.mem_univ x
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hx
  apply Finset.mem_image.mpr
  refine ⟨a,?_,rfl⟩
  rw [unordered_leaves hgt,comb_leaves_eq]
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    apply List.mem_toFinset.mpr
    exact (List.take_sublist_take_left hnk).subset (List.mem_toFinset.mp ha)

lemma proper_frontier_merger_loss (sample : Copy → X) (F : Forest Copy)
    (hF : Partition F) (hproper : TaxonProperForest sample F)
    (b : Copy) (as : List Copy) (n k : Nat) (hn : 2 ≤ n) (hk : k ≤ as.length)
    (hsize : Fintype.card Copy = as.length+1)
    (hcover : (insert b (as.take (n-1)).toFinset).image sample = Finset.univ)
    (hfront : ForestFrontier F (comb b (as.take k)) (as.drop k)) :
    Fintype.card Copy - F.card ≤ n-2 := by
  have hp := proper_frontier_prefix_length sample F hproper b as n k hcover hfront
  have hc := forestFrontier_card F hF _ _ hfront
  rw [List.length_drop] at hc
  omega

end ProperTaxonForests

section ActualCoordinates
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E] [DecidableEq X]

/-- The actual pruning tree supplies the whole positive hierarchy. No topology
or weighted-law equality is installed as an interface assumption. -/
lemma weightedNormalize_positiveTree_of_pruned
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E)
    (coin : CommonSeed N) (T : Genealogy X)
    (hT : PrunedAt N (commonSwitching N H coin) Finset.univ N.root (some T))
    (hwell : T.WellLabelled) (hleaves : T.leaves = Finset.univ) :
    PositiveTreeWeights (weightedNormalize N C H r coin) := by
  refine ⟨weightedNormalize_empty N C H r coin,
    weightedNormalize_univ N C H r coin,T,hwell,hleaves,?_⟩
  intro A ha hu
  exact weightedNormalize_actual_pruned_clades N C H r coin hT A ha hu

lemma weightedNormalize_positiveTree [Nonempty X]
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E)
    (coin : CommonSeed N) : PositiveTreeWeights (weightedNormalize N C H r coin) := by
  obtain ⟨T,hT,hw,hl⟩ := nonempty_root_pruning_tree_exists N C
    (commonSwitching N H coin) Finset.univ Finset.univ_nonempty
  exact weightedNormalize_positiveTree_of_pruned N C H r coin T hT hw hl

/-- Finite grouping only: the source clock/calendar identity is already checked
in actual_bank_cut_eq_selected_path. This lemma does not redo that telescope. -/
lemma weightedNormalize_directedExposure
    (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E)
    (coin : CommonSeed N) (i j : X) :
    directedExposure (weightedNormalize N C H r coin) i j =
      selectedDirectedExposure N C H r coin i j := by
  have hterm (A : Finset X) :
      (if i ∈ A ∧ j ∉ A then
        (weightedNormalize N C H r coin A : ℝ) else 0) =
      ∑ e : E, if edgeTaxa N C H coin e = A ∧ i ∈ A ∧ j ∉ A then
        (edgeExposure N C r e : ℝ) else 0 := by
    by_cases hij : i ∈ A ∧ j ∉ A
    · have ha : A ≠ ∅ := by intro h; simpa [h] using hij.1
      have hu : A ≠ Finset.univ := by intro h; simpa [h] using hij.2
      simp [hij,weightedNormalize,ha,hu]
    · simp [hij]
  unfold directedExposure
  simp_rw [hterm]
  rw [Finset.sum_comm]
  unfold selectedDirectedExposure
  apply Finset.sum_congr rfl
  intro e _
  rw [Finset.sum_eq_single (edgeTaxa N C H coin e)]
  · simp only [true_and,mem_edgeTaxa]
    split_ifs <;> rfl
  · intro A _ hA
    simp [Ne.symm hA]
  · simp

end ActualCoordinates
end DotG4.WholeProfileDetermination
