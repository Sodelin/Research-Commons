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
  simpa only [← Real.exp_eq_exp_ℝ,countPMF_real,mul_pow,he,div_eq_mul_inv,mul_assoc,mul_left_comm,mul_comm]
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
    A.card ≤ (Fintype.card Copy-F.card) + (activeTrees F A).card := by
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
      (activeTrees F A).card := by simp [activeTrees,Finset.sum_boole]
  rw [hcount] at hsum
  have hloss := partition_merger_loss_sum F hF
  have he : (∑ t ∈ F, (t.val.leaves.card-1)) = Fintype.card Copy-F.card := by omega
  simpa only [he] using hsum

lemma active_count_lower (F : Forest Copy) (hF : Partition F) (A : Finset Copy)
    (s : Nat) (hloss : Fintype.card Copy-F.card ≤ s) :
    A.card-s ≤ (activeTrees F A).card := by
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

lemma legal_pairAction_eq_full (F : Forest Copy) (A : Finset Copy)
    (p : WellLabelledTree Copy × WellLabelledTree Copy) (hp : LegalPair F A p) :
    pairAction F A p = pairAction F Finset.univ p := by
  have hu : LegalPair F Finset.univ p :=
    ⟨hp.1,hp.2.1,hp.2.2.1,Finset.subset_univ _,Finset.subset_univ _,hp.2.2.2.2.2⟩
  simp only [pairAction,dif_pos hp,dif_pos hu]

/-- The accepted source-choice classification is transported to the independent
forest carrier, rather than reproving comb attachment combinatorics. -/
lemma frontier_nonforbidden_active_pair_count (N : RootedBinary V E X)
    (sample : Copy → X) (register : V → Bool) (F : Forest Copy) (hF : Partition F)
    (t : Genealogy Copy) (next b : Copy) (rest : List Copy)
    (h : ForestFrontier F t (next::rest)) (hb : b ∈ t.leaves) (A : Finset Copy) :
    ((activeTrees F A).offDiag.filter (fun p =>
      ¬ forbiddenForest ((next::rest).foldl (fun u a => .graft u (.leaf a)) t)
        (pairAction F A p))).card ≤ 2 := by
  let s := forestRootCode N sample register F hF
  have hs : forestCode N s = F := forestRootCode_forest N sample register F hF
  have hr := forestRootCode_ancestral N sample register F hF
  obtain ⟨pref,hpref⟩ := forestRootCode_frontier N sample register F hF t (next::rest) h
  have hroot := nonforbidden_root_pair_count N s t pref next b rest hr hpref hb
  rw [hs] at hroot
  apply le_trans (Finset.card_le_card (show
      (activeTrees F A).offDiag.filter (fun p =>
        ¬ forbiddenForest ((next::rest).foldl (fun u a => .graft u (.leaf a)) t)
          (pairAction F A p)) ⊆
      (rootPairs F).filter (fun p =>
        ¬ forbiddenForest ((next::rest).foldl (fun u a => .graft u (.leaf a)) t)
          (pairAction F Finset.univ p)) from ?_)) hroot
  intro p hp
  obtain ⟨hp,hgood⟩ := Finset.mem_filter.mp hp
  have hl := (legalPair_iff_mem_active_offDiag F hF A p).mpr hp
  refine Finset.mem_filter.mpr ⟨?_,?_⟩
  · rw [rootPairs_eq_offDiag F hF]
    exact Finset.mem_offDiag.mpr ⟨hl.1,hl.2.1,hl.2.2.1⟩
  · rwa [← legal_pairAction_eq_full F A p hl]

lemma forest_legal_pair_frontier_or_forbidden (N : RootedBinary V E X)
    (sample : Copy → X) (register : V → Bool) (F : Forest Copy) (hF : Partition F)
    (t : Genealogy Copy) (next b : Copy) (rest : List Copy)
    (h : ForestFrontier F t (next::rest)) (hb : b ∈ t.leaves)
    (A : Finset Copy) (p : WellLabelledTree Copy × WellLabelledTree Copy)
    (hp : LegalPair F A p) :
    ForestFrontier (pairAction F A p) (.graft t (.leaf next)) rest ∨
      forbiddenForest ((next::rest).foldl (fun u a => .graft u (.leaf a)) t)
        (pairAction F A p) := by
  let s := forestRootCode N sample register F hF
  have hs : forestCode N s = F := forestRootCode_forest N sample register F hF
  have hr := forestRootCode_ancestral N sample register F hF
  obtain ⟨pref,hpref⟩ := forestRootCode_frontier N sample register F hF t (next::rest) h
  have hpu : p ∈ rootPairs (forestCode N s) := by
    rw [hs,rootPairs_eq_offDiag F hF]
    exact Finset.mem_offDiag.mpr ⟨hp.1,hp.2.1,hp.2.2.1⟩
  let q := (rootForestChoices N s hr).symm ⟨p,hpu⟩
  have he : (rootForestChoice N s hr q).val = p :=
    congrArg Subtype.val ((rootForestChoices N s hr).apply_symm_apply ⟨p,hpu⟩)
  have hout := root_pair_frontier_or_forbidden N s t pref next b rest hr hpref hb q
  rw [rootForestChoice_destination N s hr q,he,hs,
    ← legal_pairAction_eq_full F A p hp] at hout
  exact hout

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

section ReachableCombFrontiers
variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
open DotG34.SpecifiedCombEvent

/-- Each genuine merger either advances the one prescribed spine or creates
an opaque wrong clade which can never disappear. -/
def CombReachable (b : Copy) (as : List Copy) (F : Forest Copy) : Prop :=
  forbiddenForest (comb b as) F ∨
    ∃ pre rest : List Copy, as = pre ++ rest ∧ ForestFrontier F (comb b pre) rest

lemma comb_append (b : Copy) (pre rest : List Copy) :
    comb b (pre ++ rest) = rest.foldl (fun u a => .graft u (.leaf a)) (comb b pre) := by
  simp only [comb,List.foldl_append]

lemma initialForest_combReachable (b : Copy) (as : List Copy)
    (hcover : ∀ x, x = b ∨ x ∈ as) (hb : b ∉ as) (hn : as.Nodup) :
    CombReachable b as initialForest := by
  right
  refine ⟨[],as,rfl,?_,?_,?_,?_,hn⟩
  · exact ⟨treeLeaf b,Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩,
      UnorderedEquiv.refl _⟩
  · intro a _
    exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  · intro x
    simpa only [comb,List.foldl_nil,Genealogy.leaves,Finset.mem_singleton] using hcover x
  · intro a ha he
    have hab : a = b := Finset.mem_singleton.mp he
    exact hb (hab ▸ ha)

lemma pairAction_combReachable (N : RootedBinary V E X) (sample : Copy → X)
    (register : V → Bool) (b : Copy) (as : List Copy) (F : Forest Copy)
    (hF : Partition F) (h : CombReachable b as F) (A : Finset Copy)
    (p : WellLabelledTree Copy × WellLabelledTree Copy) :
    CombReachable b as (pairAction F A p) := by
  rcases h with hbad | ⟨pre,rest,has,hfront⟩
  · obtain ⟨B,hB,hnot⟩ := hbad
    exact Or.inl ⟨B,pairAction_preserves_clade F A B p hB,hnot⟩
  · by_cases hp : LegalPair F A p
    · cases rest with
      | nil =>
          have hc := forestFrontier_card F hF _ [] hfront
          have hpairs : 1 < F.card := Finset.one_lt_card.mpr
            ⟨p.1,hp.1,p.2,hp.2.1,hp.2.2.1⟩
          simp only [List.length_nil,zero_add] at hc
          omega
      | cons next rest =>
          have hb : b ∈ (comb b pre).leaves := by
            rw [comb_leaves_eq]
            exact Finset.mem_insert_self _ _
          rcases forest_legal_pair_frontier_or_forbidden N sample register F hF
            (comb b pre) next b rest hfront hb A p hp with hout | hout
          · right
            refine ⟨pre ++ [next],rest,?_,?_⟩
            · simpa only [List.append_assoc,List.singleton_append] using has
            · simpa only [comb_append,List.foldl_cons,List.foldl_nil] using hout
          · left
            simpa only [has,comb_append] using hout
    · have he : pairAction F A p = F := by simp only [pairAction,dif_neg hp]
      rw [he]
      exact Or.inr ⟨pre,rest,has,hfront⟩

lemma cladeStep_combReachable (N : RootedBinary V E X) (sample : Copy → X)
    (register : V → Bool) (b : Copy) (as : List Copy) (F : Forest Copy)
    (hF : Partition F) (h : CombReachable b as F) (A : Finset Copy)
    {G : Forest Copy} (hG : G ∈ (cladeStep A F).support) : CombReachable b as G := by
  obtain ⟨p,_,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hG
  cases p with
  | none => exact h
  | some p => exact pairAction_combReachable N sample register b as F hF h A p

lemma combReachable_good_frontier (b : Copy) (as : List Copy) (F : Forest Copy)
    (h : CombReachable b as F) (hgood : ¬ forbiddenForest (comb b as) F) :
    ∃ pre rest : List Copy, as = pre ++ rest ∧ ForestFrontier F (comb b pre) rest :=
  h.resolve_left hgood

end ReachableCombFrontiers

section ForestKilledRow
variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
open UnifiedLean.Source.SourcePoissonExponential

lemma goodMass_cladeStep (F : Forest Copy) (A : Finset Copy) (good : Forest Copy → Prop) :
    goodMass (cladeStep A F) good =
      (Fintype.card (PaddedChoice Copy) : ℝ)⁻¹ *
        ∑ p : PaddedChoice Copy, if good (paddedAction F A p) then 1 else 0 := by
  rw [goodMass,cladeStep,PMF.map_comp,PMF.map,bind_probability_real,tsum_fintype]
  simp only [Function.comp_apply,PMF.uniformOfFintype_apply,
    ENNReal.toReal_inv,ENNReal.toReal_natCast,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases hp : good (paddedAction F A p) <;> simp [hp,PMF.pure_apply]

/-- Only genuine legal choices change a bounded readout. The Option padding
contributes a self-loop and cancels from the generator correction. -/
lemma cladeStep_indicator_row (F : Forest Copy) (hF : Partition F)
    (A : Finset Copy) (good : Forest Copy → Prop) :
    goodMass (cladeStep A F) good = (if good F then 1 else 0) +
      (Fintype.card (PaddedChoice Copy) : ℝ)⁻¹ *
        ∑ p ∈ (activeTrees F A).offDiag,
          ((if good (pairAction F A p) then 1 else 0) - (if good F then 1 else 0)) := by
  let v : Forest Copy → ℝ := fun G => if good G then 1 else 0
  have hdiff : (∑ p : PaddedChoice Copy, (v (paddedAction F A p) - v F)) =
      ∑ p ∈ (activeTrees F A).offDiag, (v (pairAction F A p) - v F) := by
    rw [Fintype.sum_option]
    simp only [paddedAction,sub_self,zero_add]
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro p _ hp
    have hn : ¬ LegalPair F A p := by
      rwa [legalPair_iff_mem_active_offDiag F hF A p]
    simp only [pairAction,dif_neg hn,sub_self]
  have hc : (Fintype.card (PaddedChoice Copy) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos (α := PaddedChoice Copy)))
  rw [Finset.sum_sub_distrib] at hdiff
  simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul] at hdiff
  rw [goodMass_cladeStep]
  change _ = v F + _
  rw [← hdiff]
  field_simp
  ring

lemma cladeStep_good_row_bound (F : Forest Copy) (hF : Partition F)
    (A : Finset Copy) (good : Forest Copy → Prop) (hg : good F)
    (hcount : ((activeTrees F A).offDiag.filter
      (fun p => good (pairAction F A p))).card ≤ 2) :
    goodMass (cladeStep A F) good ≤
      1 - (((activeTrees F A).offDiag.card : ℝ) - 2) /
        (Fintype.card (PaddedChoice Copy) : ℝ) := by
  rw [cladeStep_indicator_row F hF A good]
  simp only [hg,ite_true,Finset.sum_sub_distrib,Finset.sum_const,
    nsmul_eq_mul,mul_one]
  have hs : (∑ p ∈ (activeTrees F A).offDiag,
      if good (pairAction F A p) then (1 : ℝ) else 0) ≤ 2 := by
    simpa only [Finset.sum_boole] using (show
      (((activeTrees F A).offDiag.filter (fun p => good (pairAction F A p))).card : ℝ) ≤ 2
      from by exact_mod_cast hcount)
  have hD : 0 ≤ (Fintype.card (PaddedChoice Copy) : ℝ)⁻¹ := by positivity
  have hm := mul_le_mul_of_nonneg_left
    (sub_le_sub_right hs ((activeTrees F A).offDiag.card : ℝ)) hD
  linarith [hm]

lemma active_offDiag_le_padding (F : Forest Copy) (A : Finset Copy) :
    (activeTrees F A).offDiag.card ≤ Fintype.card (PaddedChoice Copy) := by
  have h := Finset.card_le_univ ((activeTrees F A).offDiag)
  simpa only [PaddedChoice,Fintype.card_option] using
    h.trans (Nat.le_succ (Fintype.card (WellLabelledTree Copy × WellLabelledTree Copy)))

lemma killed_row_factor_range (F : Forest Copy) (A : Finset Copy) (rmin : ℝ)
    (hmin : 1 ≤ rmin) (hr : rmin ≤ ((activeTrees F A).offDiag.card : ℝ)/2) :
    0 ≤ 1 - (rmin-1)/(uniformizationRate (Copy := Copy) : ℝ) ∧
      1 - (rmin-1)/(uniformizationRate (Copy := Copy) : ℝ) ≤ 1 := by
  have hΛ := uniformizationRate_positive (Copy := Copy)
  have hΛr : 0 < (uniformizationRate (Copy := Copy) : ℝ) := hΛ
  have hc : ((activeTrees F A).offDiag.card : ℝ) ≤
      (Fintype.card (PaddedChoice Copy) : ℝ) := by exact_mod_cast active_offDiag_le_padding F A
  have he : (uniformizationRate (Copy := Copy) : ℝ) =
      (Fintype.card (PaddedChoice Copy) : ℝ)/2 := by
    simp only [uniformizationRate,NNReal.coe_div,NNReal.coe_natCast,NNReal.coe_ofNat]
  constructor
  · have hb : (rmin-1)/(uniformizationRate (Copy := Copy) : ℝ) ≤ 1 := by
      apply (div_le_one hΛr).mpr
      rw [he]
      linarith
    linarith
  · have hb : 0 ≤ (rmin-1)/(uniformizationRate (Copy := Copy) : ℝ) :=
      div_nonneg (sub_nonneg.mpr hmin) (le_of_lt hΛr)
    linarith

lemma cladeStep_good_row_rate_bound (F : Forest Copy) (hF : Partition F)
    (A : Finset Copy) (good : Forest Copy → Prop) (hg : good F) (rmin : ℝ)
    (hr : rmin ≤ ((activeTrees F A).offDiag.card : ℝ)/2)
    (hcount : ((activeTrees F A).offDiag.filter
      (fun p => good (pairAction F A p))).card ≤ 2) :
    goodMass (cladeStep A F) good ≤
      1 - (rmin-1)/(uniformizationRate (Copy := Copy) : ℝ) := by
  apply (cladeStep_good_row_bound F hF A good hg hcount).trans
  have hD : 0 < (Fintype.card (PaddedChoice Copy) : ℝ) := by
    exact_mod_cast Fintype.card_pos (α := PaddedChoice Copy)
  simp only [uniformizationRate,NNReal.coe_div,NNReal.coe_natCast,NNReal.coe_ofNat]
  apply sub_le_sub_left
  have he : (rmin-1) / ((Fintype.card (PaddedChoice Copy) : ℝ)/2) =
      (2*rmin-2)/(Fintype.card (PaddedChoice Copy) : ℝ) := by
    field_simp
    <;> ring
  rw [he]
  apply (div_le_div_iff_of_pos_right hD).mpr
  linarith

/-- Real polynomial form of the ordinary Kingman pair count. -/
def pairRatePolynomial (k : ℝ) : ℝ := k*(k-1)/2

lemma pairRatePolynomial_mono {a b : ℝ} (ha : 1 ≤ a) (hab : a ≤ b) :
    pairRatePolynomial a ≤ pairRatePolynomial b := by
  have hprod : 0 ≤ (b-a)*(a+b-1) := mul_nonneg (sub_nonneg.mpr hab) (by linarith)
  unfold pairRatePolynomial
  nlinarith

lemma active_offDiag_rate (F : Forest Copy) (A : Finset Copy) :
    ((activeTrees F A).offDiag.card : ℝ)/2 =
      pairRatePolynomial ((activeTrees F A).card : ℝ) := by
  let k := (activeTrees F A).card
  have hk : k ≤ k*k := by
    by_cases hz : k = 0
    · simp [hz]
    · have hp : 1 ≤ k := Nat.one_le_iff_ne_zero.mpr hz
      nlinarith
  rw [Finset.offDiag_card,Nat.cast_sub hk,Nat.cast_mul]
  unfold pairRatePolynomial
  ring

end ForestKilledRow


section ActualKilledEstimate
variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq X] [DecidableEq Copy]
open DotG34.SpecifiedCombEvent

lemma goodMass_zero_of_support {S : Type*} [Fintype S] [DecidableEq S]
    (p : PMF S) (good : S → Prop) (h : ∀ s ∈ p.support, ¬ good s) :
    goodMass p good = 0 := by
  unfold goodMass
  have hz : (p.map (fun s => decide (good s))) true = 0 := by
    apply (PMF.apply_eq_zero_iff _ _).mpr
    intro hm
    obtain ⟨s,hs,he⟩ := (PMF.mem_support_map_iff _ _ _).mp hm
    exact h s hs (of_decide_eq_true he)
  rw [hz,ENNReal.toReal_zero]

lemma combReachable_proper_loss (sample : Copy → X) (b : Copy) (as : List Copy)
    (n : Nat) (hn : 2 ≤ n) (F : Forest Copy) (hF : Partition F)
    (hproper : TaxonProperForest sample F) (hreach : CombReachable b as F)
    (hgood : ¬ forbiddenForest (comb b as) F)
    (hsize : Fintype.card Copy = as.length+1)
    (hcover : (insert b (as.take (n-1)).toFinset).image sample = Finset.univ) :
    Fintype.card Copy - F.card ≤ n-2 := by
  obtain ⟨pre,rest,has,hfront⟩ := combReachable_good_frontier b as F hreach hgood
  have hk : pre.length ≤ as.length := by simp only [has,List.length_append]; omega
  have hf : ForestFrontier F (comb b (as.take pre.length)) (as.drop pre.length) := by
    simpa only [has,List.take_append_length,List.drop_append_length] using hfront
  exact proper_frontier_merger_loss sample F hF hproper b as n pre.length hn hk hsize hcover hf

lemma combReachable_proper_pair_count (N : RootedBinary V E X)
    (sample : Copy → X) (register : V → Bool) (b : Copy) (as : List Copy)
    (n : Nat) (hlen : n-1 ≤ as.length) (F : Forest Copy) (hF : Partition F)
    (hproper : TaxonProperForest sample F) (hreach : CombReachable b as F)
    (hgood : ¬ forbiddenForest (comb b as) F)
    (hcover : (insert b (as.take (n-1)).toFinset).image sample = Finset.univ)
    (A : Finset Copy) :
    ((activeTrees F A).offDiag.filter
      (fun p => ¬ forbiddenForest (comb b as) (pairAction F A p))).card ≤ 2 := by
  obtain ⟨pre,rest,has,hfront⟩ := combReachable_good_frontier b as F hreach hgood
  have hf : ForestFrontier F (comb b (as.take pre.length)) (as.drop pre.length) := by
    simpa only [has,List.take_append_length,List.drop_append_length] using hfront
  have hp := proper_frontier_prefix_length sample F hproper b as n pre.length hcover hf
  cases rest with
  | nil => simp only [List.append_nil] at has; subst as; omega
  | cons next rest =>
      have hb : b ∈ (comb b pre).leaves := by
        rw [comb_leaves_eq]; exact Finset.mem_insert_self _ _
      simpa only [has,comb_append] using frontier_nonforbidden_active_pair_count
        N sample register F hF (comb b pre) next b rest hfront hb A

lemma cladeIteration_eq_kernelIteration (A : Finset Copy) (k : Nat) (F : Forest Copy) :
    cladeIteration A k F = kernelIteration (cladeStep A) k F := by
  induction k generalizing F with
  | zero => rfl
  | succ k ih =>
      simp only [cladeIteration,kernelIteration]
      congr 1
      funext G
      exact ih G

/-- A genuine source-derived compatible-history estimate. All combinatorial
row bounds are discharged here from the prescribed comb and proper-clade
support; the growing padded clock cancels exactly. -/
lemma actual_clade_compatible_mass_bound (N : RootedBinary V E X)
    (sample : Copy → X) (register : V → Bool) (b : Copy) (as : List Copy)
    (n : Nat) (hn : 2 ≤ n) (hlen : n-1 ≤ as.length)
    (hsize : Fintype.card Copy = as.length+1)
    (hcover : (insert b (as.take (n-1)).toFinset).image sample = Finset.univ)
    (A : Finset X) (hA : A ≠ Finset.univ) (t : ℝ≥0)
    (hK : n ≤ (cladeCopySet sample A).card)
    (F : Forest Copy) (hF : Partition F) (hproper : TaxonProperForest sample F)
    (hreach : CombReachable b as F) (hgood : ¬ forbiddenForest (comb b as) F) :
    goodMass (cladeKernel (cladeCopySet sample A) t F)
      (fun G => ¬ forbiddenForest (comb b as) G) ≤
      Real.exp (-(pairRatePolynomial (((cladeCopySet sample A).card : ℝ)-((n : ℝ)-2))) * t + t) := by
  let B := cladeCopySet sample A
  let good := fun G => ¬ forbiddenForest (comb b as) G
  let R := fun G => Partition G ∧ TaxonProperForest sample G ∧ CombReachable b as G
  let rmin := pairRatePolynomial ((B.card : ℝ)-((n : ℝ)-2))
  let Λ : ℝ := uniformizationRate (Copy := Copy)
  let q := 1-(rmin-1)/Λ
  have hrates (G : Forest Copy) (hG : R G) (hg : good G) :
      1 ≤ rmin ∧ rmin ≤ ((activeTrees G B).offDiag.card : ℝ)/2 := by
    have hloss := combReachable_proper_loss sample b as n hn G hG.1 hG.2.1 hG.2.2 hg hsize hcover
    have hactive := active_count_add_loss_bound G hG.1 B
    have hc : (B.card : ℝ) ≤ (n-2 : Nat) + ((activeTrees G B).card : ℝ) := by
      exact_mod_cast hactive.trans (Nat.add_le_add_right hloss _)
    have hnk : (n : ℝ) ≤ (B.card : ℝ) := by exact_mod_cast hK
    have hcast : ((n-2 : Nat) : ℝ) = (n : ℝ)-2 := by rw [Nat.cast_sub hn]; norm_num
    rw [hcast] at hc
    constructor
    · have h := pairRatePolynomial_mono (a := 2) (b := (B.card : ℝ)-((n : ℝ)-2)) (by norm_num) (by linarith)
      norm_num [pairRatePolynomial] at h ⊢
      exact h
    · rw [active_offDiag_rate]
      exact pairRatePolynomial_mono (by linarith) (by linarith)
  have hq : 0 ≤ q := (killed_row_factor_range F B rmin (hrates F ⟨hF,hproper,hreach⟩ hgood).1
    (hrates F ⟨hF,hproper,hreach⟩ hgood).2).1
  have hinv : ∀ G, R G → ∀ H ∈ (cladeStep B G).support, R H := by
    intro G hG H hH
    exact ⟨cladeStep_partition B G hG.1 hH,
      cladeStep_taxonProper sample G hG.2.1 A hA hH,
      cladeStep_combReachable N sample register b as G hG.1 hG.2.2 B hH⟩
  have hrow : ∀ G, R G → goodMass (cladeStep B G) good ≤ q * (if good G then 1 else 0) := by
    intro G hG
    by_cases hg : good G
    · simp only [hg,ite_true,mul_one]
      exact cladeStep_good_row_rate_bound G hG.1 B good hg rmin (hrates G hG hg).2
        (combReachable_proper_pair_count N sample register b as n hlen G hG.1 hG.2.1 hG.2.2 hg hcover B)
    · have hbad : forbiddenForest (comb b as) G := not_not.mp hg
      have hz : goodMass (cladeStep B G) good = 0 := by
        apply goodMass_zero_of_support
        intro H hH hgH
        obtain ⟨D,hD,hnot⟩ := hbad
        exact hgH ⟨D,cladeStep_preserves_clade G B D hD hH,hnot⟩
      simp only [hz,hg,ite_false,mul_zero,le_refl]
  have hbound := killed_poisson_bound (cladeStep B) R good q hq hinv hrow
    (uniformizationRate (Copy := Copy)*t) F ⟨hF,hproper,hreach⟩ hgood
  have hΛ : Λ ≠ 0 := ne_of_gt (show 0 < Λ from uniformizationRate_positive)
  have he : ((uniformizationRate (Copy := Copy)*t : ℝ≥0) : ℝ)*(q-1) = -rmin*t+t := by
    simp only [NNReal.coe_mul]
    dsimp [q,Λ]
    field_simp
    <;> ring
  simpa only [cladeKernel,cladeIteration_eq_kernelIteration,he] using hbound

end ActualKilledEstimate

section NoMergerLowerBound
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourcePoissonExponential
variable {S : Type*} [Fintype S] [DecidableEq S]

lemma pmf_real_le_one (p : PMF S) (s : S) : (p s).toReal ≤ 1 := by
  simpa only [ENNReal.toReal_one] using ENNReal.toReal_mono (by simp) (PMF.coe_le_one p s)

lemma kernelIteration_diagonal_lower (K : S → PMF S) (k : Nat) (s : S) :
    (K s s).toReal^k ≤ (kernelIteration K k s s).toReal := by
  induction k with
  | zero => simp [kernelIteration,PMF.pure_apply]
  | succ k ih =>
      rw [kernelIteration,bind_probability_real,tsum_fintype]
      calc
        _ = (K s s).toReal * (K s s).toReal^k := by rw [pow_succ'];
        _ ≤ (K s s).toReal * (kernelIteration K k s s).toReal :=
          mul_le_mul_of_nonneg_left ih ENNReal.toReal_nonneg
        _ ≤ ∑ d : S, (K s d).toReal * (kernelIteration K k d s).toReal :=
          Finset.single_le_sum (fun d _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
            (Finset.mem_univ s)

lemma poisson_diagonal_lower (K : S → PMF S) (a : ℝ≥0) (s : S) :
    Real.exp ((a : ℝ)*((K s s).toReal-1)) ≤
      (((countPMF a).bind (fun k => kernelIteration K k s)) s).toReal := by
  rw [bind_probability_real]
  have hl := poisson_power_hasSum a (K s s).toReal
  have hu := poisson_power_hasSum a 1
  have hsum : Summable (fun k => (countPMF a k).toReal * (kernelIteration K k s s).toReal) := by
    apply Summable.of_nonneg_of_le
      (fun k => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg) _ hu.summable
    intro k
    simpa only [one_pow,mul_one] using mul_le_mul_of_nonneg_left
      (pmf_real_le_one (kernelIteration K k s) s) (ENNReal.toReal_nonneg : 0 ≤ (countPMF a k).toReal)
  rw [← hl.tsum_eq]
  exact tsum_le_tsum (fun k => mul_le_mul_of_nonneg_left
    (kernelIteration_diagonal_lower K k s) ENNReal.toReal_nonneg) hl.summable hsum

end NoMergerLowerBound

section CladeNoMergerLowerBound
variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]

lemma goodMass_eq_point (p : PMF (Forest Copy)) (F : Forest Copy) :
    goodMass p (fun G => G = F) = (p F).toReal := by
  unfold goodMass
  congr 1
  rw [PMF.map_apply,tsum_fintype]
  simp

lemma legal_pairAction_ne (F : Forest Copy) (hF : Partition F) (A : Finset Copy)
    (p : WellLabelledTree Copy × WellLabelledTree Copy) (hp : LegalPair F A p) :
    pairAction F A p ≠ F := by
  intro he
  have hc := mergeForest_card F hF p.1 p.2 hp.1 hp.2.1 hp.2.2.1 hp.2.2.2.2.2
  have he' : mergeForest F p.1 p.2 hp.2.2.2.2.2 = F := by
    simpa only [pairAction,dif_pos hp] using he
  rw [he'] at hc
  omega

lemma cladeStep_diagonal (F : Forest Copy) (hF : Partition F) (A : Finset Copy) :
    (cladeStep A F F).toReal =
      1 - ((activeTrees F A).offDiag.card : ℝ) /
        (Fintype.card (PaddedChoice Copy) : ℝ) := by
  rw [← goodMass_eq_point,cladeStep_indicator_row F hF A (fun G => G = F)]
  simp only [ite_true]
  have hz : (∑ p ∈ (activeTrees F A).offDiag,
      ((if pairAction F A p = F then (1 : ℝ) else 0)-1)) =
      -((activeTrees F A).offDiag.card : ℝ) := by
    calc
      _ = ∑ _p ∈ (activeTrees F A).offDiag, (-1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [legal_pairAction_ne F hF A p
          ((legalPair_iff_mem_active_offDiag F hF A p).mpr hp),ite_false,zero_sub]
      _ = _ := by simp
  rw [hz]
  ring

lemma cladeKernel_diagonal_lower (F : Forest Copy) (hF : Partition F)
    (A : Finset Copy) (t : ℝ≥0) :
    Real.exp (-pairRatePolynomial ((activeTrees F A).card : ℝ)*t) ≤
      (cladeKernel A t F F).toReal := by
  have hb := poisson_diagonal_lower (cladeStep A)
    (uniformizationRate (Copy := Copy)*t) F
  rw [cladeStep_diagonal F hF A] at hb
  have hc : (Fintype.card (PaddedChoice Copy) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos (α := PaddedChoice Copy)))
  have he : ((uniformizationRate (Copy := Copy)*t : ℝ≥0) : ℝ)*
      ((1-((activeTrees F A).offDiag.card : ℝ)/(Fintype.card (PaddedChoice Copy) : ℝ))-1) =
      -pairRatePolynomial ((activeTrees F A).card : ℝ)*t := by
    rw [← active_offDiag_rate]
    simp only [NNReal.coe_mul,uniformizationRate,NNReal.coe_div,NNReal.coe_natCast,NNReal.coe_ofNat]
    field_simp
    <;> ring
  simpa only [he,cladeKernel,cladeIteration_eq_kernelIteration] using hb

end CladeNoMergerLowerBound

section ProgramNoMergerLowerBound
variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
open UnifiedLean.Source.SourcePoissonExponential

noncomputable def fixedForestHazard (F : Forest Copy) (ops : List (Finset Copy × ℝ≥0)) : ℝ :=
  (ops.map (fun op => pairRatePolynomial ((activeTrees F op.1).card : ℝ)*(op.2 : ℝ))).sum

lemma forestProgram_diagonal_lower (ops : List (Finset Copy × ℝ≥0))
    (F : Forest Copy) (hF : Partition F) :
    Real.exp (-fixedForestHazard F ops) ≤ (forestProgram ops F F).toReal := by
  induction ops with
  | nil => simp [fixedForestHazard,forestProgram,PMF.pure_apply]
  | cons op ops ih =>
      rw [forestProgram,bind_probability_real,tsum_fintype]
      have he : Real.exp (-fixedForestHazard F (op::ops)) =
          Real.exp (-pairRatePolynomial ((activeTrees F op.1).card : ℝ)*op.2) *
            Real.exp (-fixedForestHazard F ops) := by
        simp only [fixedForestHazard,List.map_cons,List.sum_cons,neg_add_rev]
        rw [Real.exp_add]
        ring
      rw [he]
      calc
        _ ≤ (cladeKernel op.1 op.2 F F).toReal * (forestProgram ops F F).toReal :=
          mul_le_mul (cladeKernel_diagonal_lower F hF op.1 op.2) ih
            (le_of_lt (Real.exp_pos _)) ENNReal.toReal_nonneg
        _ ≤ ∑ G : Forest Copy, (cladeKernel op.1 op.2 F G).toReal *
            (forestProgram ops G F).toReal :=
          Finset.single_le_sum (fun G _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
            (Finset.mem_univ F)

noncomputable def programCombMass (ops : List (Finset Copy × ℝ≥0))
    (F : Forest Copy) (target : Genealogy Copy) : ℝ :=
  (((forestProgram ops F).bind ordinaryCompletion).map forestObservation {toUnranked target}).toReal

lemma programCombMass_sum (ops : List (Finset Copy × ℝ≥0))
    (F : Forest Copy) (target : Genealogy Copy) :
    programCombMass ops F target =
      ∑ G : Forest Copy, (forestProgram ops F G).toReal * (completionCombMass G target).toReal := by
  rw [programCombMass,PMF.map_bind,bind_probability_real,tsum_fintype]
  rfl

lemma programCombMass_no_merger_lower (ops : List (Finset Copy × ℝ≥0))
    (F : Forest Copy) (hF : Partition F) (target : Genealogy Copy) :
    Real.exp (-fixedForestHazard F ops) * (completionCombMass F target).toReal ≤
      programCombMass ops F target := by
  rw [programCombMass_sum]
  exact (mul_le_mul_of_nonneg_right (forestProgram_diagonal_lower ops F hF)
    ENNReal.toReal_nonneg).trans
      (Finset.single_le_sum (fun G _ => mul_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
        (Finset.mem_univ F))

lemma initialForest_active_card (A : Finset Copy) :
    (activeTrees initialForest A).card = A.card := by
  have he : activeTrees initialForest A = A.image treeLeaf := by
    ext t
    constructor
    · intro ht
      obtain ⟨ht,hA⟩ := Finset.mem_filter.mp ht
      obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp ht
      exact Finset.mem_image.mpr ⟨x,hA (Finset.mem_singleton_self x),rfl⟩
    · rintro ht
      obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp ht
      exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩,
        Finset.singleton_subset_iff.mpr hx⟩
  rw [he,Finset.card_image_of_injective _ treeLeaf_injective]

end ProgramNoMergerLowerBound

section CombCoefficientBounds

noncomputable def combCoefficient (l : Nat) : ℝ :=
  2^l / ((Nat.factorial (l+1) : ℝ)*(Nat.factorial l : ℝ))

lemma combCoefficient_pos (l : Nat) : 0 < combCoefficient l := by
  unfold combCoefficient
  positivity

lemma combCoefficient_succ (l : Nat) :
    combCoefficient l = combCoefficient (l+1) * (((l+2 : Nat) : ℝ)*(l+1)/2) := by
  have hf : (l.factorial : ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero l
  have h1 : ((l+1 : Nat) : ℝ) ≠ 0 := by positivity
  have h2 : ((l+2 : Nat) : ℝ) ≠ 0 := by positivity
  unfold combCoefficient
  simp only [Nat.factorial_succ,Nat.cast_mul,Nat.cast_add,Nat.cast_one,pow_succ]
  field_simp
  <;> ring

/-- Losing at most s compatible root mergers changes the exact inherited
coefficient by at most the polynomial factor M^(2s). -/
lemma combCoefficient_shift_bound (l s : Nat) :
    combCoefficient l ≤ combCoefficient (l+s) * ((l+s+1 : Nat) : ℝ)^(2*s) := by
  induction s with
  | zero => simp
  | succ s ih =>
      have hstep : combCoefficient (l+s) ≤
          combCoefficient (l+(s+1)) * ((l+(s+1)+1 : Nat) : ℝ)^2 := by
        rw [combCoefficient_succ (l+s)]
        apply mul_le_mul_of_nonneg_left _ (le_of_lt (combCoefficient_pos _))
        push_cast
        have hl : (0 : ℝ) ≤ l := Nat.cast_nonneg _
        have hs : (0 : ℝ) ≤ s := Nat.cast_nonneg _
        nlinarith
      have hpow : ((l+s+1 : Nat) : ℝ)^(2*s) ≤ ((l+(s+1)+1 : Nat) : ℝ)^(2*s) := by
        gcongr
        omega
      calc
        _ ≤ combCoefficient (l+s) * ((l+s+1 : Nat) : ℝ)^(2*s) := ih
        _ ≤ (combCoefficient (l+(s+1)) * ((l+(s+1)+1 : Nat) : ℝ)^2) *
            ((l+(s+1)+1 : Nat) : ℝ)^(2*s) :=
          mul_le_mul hstep hpow (by positivity) (by positivity)
        _ = _ := by
          rw [show 2*(s+1) = 2+2*s by omega,pow_add]
          ring

lemma combCoefficient_loss_bound (l m s : Nat) (hlm : l ≤ m) (hloss : m-l ≤ s) :
    combCoefficient l ≤ combCoefficient m * ((m+1 : Nat) : ℝ)^(2*s) := by
  have h := combCoefficient_shift_bound l (m-l)
  rw [Nat.add_sub_of_le hlm] at h
  apply h.trans
  apply mul_le_mul_of_nonneg_left _ (le_of_lt (combCoefficient_pos m))
  apply pow_le_pow_right₀ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le m))
  omega

end CombCoefficientBounds

section ProgramKilledComposition
variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]
open UnifiedLean.Source.SourcePoissonExponential

lemma goodMass_bind_upper (p : PMF (Forest Copy)) (K : Forest Copy → PMF (Forest Copy))
    (good : Forest Copy → Prop) (c : ℝ)
    (h : ∀ G ∈ p.support, goodMass (K G) good ≤ c*(if good G then 1 else 0)) :
    goodMass (p.bind K) good ≤ c*goodMass p good := by
  rw [goodMass_bind,tsum_fintype]
  calc
    _ ≤ ∑ G : Forest Copy, (p G).toReal * (c*(if good G then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro G _
      by_cases hz : p G = 0
      · simp only [hz,ENNReal.toReal_zero,zero_mul,le_refl]
      · exact mul_le_mul_of_nonneg_left (h G ((PMF.mem_support_iff _ _).mpr hz)) ENNReal.toReal_nonneg
    _ = c*goodMass p good := by
      rw [goodMass,PMF.map,bind_probability_real,tsum_fintype,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro G _
      by_cases hg : good G <;> simp [hg,mul_assoc,mul_left_comm,mul_comm]

lemma forestProgram_goodMass_bound (ops : List (Finset Copy × ℝ≥0))
    (R good : Forest Copy → Prop) (cost : (Finset Copy × ℝ≥0) → ℝ)
    (hinv : ∀ op ∈ ops, ∀ F, R F → ∀ G ∈ (cladeKernel op.1 op.2 F).support, R G)
    (hrow : ∀ op ∈ ops, ∀ F, R F → goodMass (cladeKernel op.1 op.2 F) good ≤
      Real.exp (cost op)*(if good F then 1 else 0))
    (F : Forest Copy) (hF : R F) :
    goodMass (forestProgram ops F) good ≤ Real.exp ((ops.map cost).sum)*(if good F then 1 else 0) := by
  induction ops generalizing F with
  | nil => simp only [forestProgram,goodMass_pure,List.map_nil,List.sum_nil,Real.exp_zero,one_mul,le_refl]
  | cons op ops ih =>
      rw [forestProgram]
      have hi := goodMass_bind_upper (cladeKernel op.1 op.2 F) (forestProgram ops) good
        (Real.exp ((ops.map cost).sum)) (by
          intro G hG
          exact ih (fun q hq => hinv q (List.mem_cons_of_mem op hq))
            (fun q hq => hrow q (List.mem_cons_of_mem op hq)) G
            (hinv op (List.mem_cons_self ..) F hF G hG))
      apply hi.trans
      calc
        _ ≤ Real.exp ((ops.map cost).sum) *
            (Real.exp (cost op)*(if good F then 1 else 0)) :=
          mul_le_mul_of_nonneg_left (hrow op (List.mem_cons_self ..) F hF) (le_of_lt (Real.exp_pos _))
        _ = _ := by
          simp only [List.map_cons,List.sum_cons,Real.exp_add]
          ring

end ProgramKilledComposition

section PositiveCladeWord
variable {X Copy : Type*} [Fintype X] [Fintype Copy]
variable [DecidableEq X] [DecidableEq Copy]

noncomputable def positiveCladeWord (w : CladeWeights X) (sample : Copy → X)
    (keys : List (Finset X)) : List (Finset Copy × ℝ≥0) :=
  (keys.filter (fun A => w A ≠ 0)).map (fun A => (cladeCopySet sample A,w A))

lemma ordinaryCladeProgram_positiveWord (w : CladeWeights X) (sample : Copy → X)
    (keys : List (Finset X)) (F : Forest Copy) :
    ordinaryCladeProgram w sample keys F = forestProgram (positiveCladeWord w sample keys) F := by
  induction keys generalizing F with
  | nil => rfl
  | cons A keys ih =>
      by_cases hz : w A = 0
      · simp only [ordinaryCladeProgram,hz,cladeKernel_zero,PMF.pure_bind,
          positiveCladeWord,List.filter_cons,ne_eq,hz,not_true_eq_false,decide_false,
          Bool.false_eq_true,ite_false]
        exact ih F
      · simp only [ordinaryCladeProgram,positiveCladeWord,List.filter_cons,hz,
          not_false_eq_true,decide_true,ite_true,List.map_cons,forestProgram]
        congr 1
        funext G
        exact ih G

lemma mem_positiveCladeWord (w : CladeWeights X) (sample : Copy → X)
    (keys : List (Finset X)) (op : Finset Copy × ℝ≥0) :
    op ∈ positiveCladeWord w sample keys ↔
      ∃ A ∈ keys, w A ≠ 0 ∧ op = (cladeCopySet sample A,w A) := by
  simp only [positiveCladeWord,List.mem_map,List.mem_filter,decide_eq_true_eq]
  constructor
  · rintro ⟨A,⟨hA,hpos⟩,he⟩
    exact ⟨A,hA,hpos,he.symm⟩
  · rintro ⟨A,hA,hpos,rfl⟩
    exact ⟨A,⟨hA,hpos⟩,rfl⟩

end PositiveCladeWord

section WholeWordCompatibleEstimate
variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq X] [DecidableEq Copy]
open DotG34.SpecifiedCombEvent

lemma cladeIteration_combReachable (N : RootedBinary V E X) (sample : Copy → X)
    (register : V → Bool) (b : Copy) (as : List Copy) (A : Finset Copy) (k : Nat)
    (F : Forest Copy) (hF : Partition F) (h : CombReachable b as F)
    {G : Forest Copy} (hG : G ∈ (cladeIteration A k F).support) : CombReachable b as G := by
  induction k generalizing F with
  | zero =>
      have he : G = F := by simpa only [cladeIteration,PMF.mem_support_pure_iff] using hG
      simpa only [he] using h
  | succ k ih =>
      obtain ⟨M,hM,hG⟩ := (PMF.mem_support_bind_iff _ _ _).mp hG
      exact ih M (cladeStep_partition A F hF hM)
        (cladeStep_combReachable N sample register b as F hF h A hM) hG

lemma cladeKernel_combReachable (N : RootedBinary V E X) (sample : Copy → X)
    (register : V → Bool) (b : Copy) (as : List Copy) (A : Finset Copy) (t : ℝ≥0)
    (F : Forest Copy) (hF : Partition F) (h : CombReachable b as F)
    {G : Forest Copy} (hG : G ∈ (cladeKernel A t F).support) : CombReachable b as G := by
  obtain ⟨k,_,hk⟩ := (PMF.mem_support_bind_iff _ _ _).mp hG
  exact cladeIteration_combReachable N sample register b as A k F hF h hk

noncomputable def compatibleCost (n : Nat) (op : Finset Copy × ℝ≥0) : ℝ :=
  (-pairRatePolynomial ((op.1.card : ℝ)-((n : ℝ)-2))+1)*(op.2 : ℝ)

lemma actual_word_compatible_mass_bound (N : RootedBinary V E X)
    (sample : Copy → X) (register : V → Bool) (w : CladeWeights X)
    (hw : w Finset.univ = 0) (keys : List (Finset X))
    (b : Copy) (as : List Copy) (n : Nat) (hn : 2 ≤ n) (hlen : n-1 ≤ as.length)
    (hsize : Fintype.card Copy = as.length+1)
    (hcover : (insert b (as.take (n-1)).toFinset).image sample = Finset.univ)
    (hK : ∀ A ∈ keys, w A ≠ 0 → n ≤ (cladeCopySet sample A).card)
    (F : Forest Copy) (hF : Partition F) (hproper : TaxonProperForest sample F)
    (hreach : CombReachable b as F) (hgood : ¬ forbiddenForest (comb b as) F) :
    goodMass (ordinaryCladeProgram w sample keys F) (fun G => ¬ forbiddenForest (comb b as) G) ≤
      Real.exp (((positiveCladeWord w sample keys).map (compatibleCost n)).sum) := by
  let ops := positiveCladeWord w sample keys
  let good := fun G => ¬ forbiddenForest (comb b as) G
  let R := fun G => Partition G ∧ TaxonProperForest sample G ∧ CombReachable b as G
  have hinv : ∀ op ∈ ops, ∀ G, R G → ∀ H ∈ (cladeKernel op.1 op.2 G).support, R H := by
    intro op hop G hG H hH
    obtain ⟨A,hA,hpos,rfl⟩ := (mem_positiveCladeWord w sample keys op).mp hop
    have hproperA : A ≠ Finset.univ := by intro he; apply hpos; simpa only [he] using hw
    exact ⟨cladeKernel_partition _ _ G hG.1 hH,
      cladeKernel_taxonProper sample A hproperA (w A) G hG.2.1 hH,
      cladeKernel_combReachable N sample register b as _ _ G hG.1 hG.2.2 hH⟩
  have hrow : ∀ op ∈ ops, ∀ G, R G → goodMass (cladeKernel op.1 op.2 G) good ≤
      Real.exp (compatibleCost n op)*(if good G then 1 else 0) := by
    intro op hop G hG
    obtain ⟨A,hA,hpos,rfl⟩ := (mem_positiveCladeWord w sample keys op).mp hop
    have hproperA : A ≠ Finset.univ := by intro he; apply hpos; simpa only [he] using hw
    by_cases hg : good G
    · simp only [hg,ite_true,mul_one]
      have hb := actual_clade_compatible_mass_bound N sample register b as n hn hlen hsize hcover
        A hproperA (w A) (hK A hA hpos) G hG.1 hG.2.1 hG.2.2 hg
      convert hb using 1 <;> unfold compatibleCost <;> ring
    · have hbad : forbiddenForest (comb b as) G := not_not.mp hg
      have hz : goodMass (cladeKernel (cladeCopySet sample A) (w A) G) good = 0 := by
        apply goodMass_zero_of_support
        intro H hH hgH
        obtain ⟨D,hD,hnot⟩ := hbad
        exact hgH ⟨D,cladeKernel_preserves_clade G (cladeCopySet sample A) D hD (w A) hH,hnot⟩
      simp only [hz,hg,ite_false,mul_zero,le_refl]
  rw [ordinaryCladeProgram_positiveWord]
  simpa only [hgood,ite_true,mul_one] using
    forestProgram_goodMass_bound ops R good (compatibleCost n) hinv hrow F ⟨hF,hproper,hreach⟩

end WholeWordCompatibleEstimate

section RootReaderUpperBound
variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq X] [DecidableEq Copy]
open DotG34.SpecifiedCombEvent

lemma reachable_completion_coefficient_bound (N : RootedBinary V E X)
    (sample : Copy → X) (r : PositivePairRates E) (register : V → Bool)
    (b : Copy) (as : List Copy) (n : Nat) (hn : 2 ≤ n)
    (hsize : Fintype.card Copy = as.length+1)
    (hcover : (insert b (as.take (n-1)).toFinset).image sample = Finset.univ)
    (F : Forest Copy) (hF : Partition F) (hproper : TaxonProperForest sample F)
    (hreach : CombReachable b as F) :
    (completionCombMass F (comb b as)).toReal ≤
      (combCoefficient as.length * ((as.length+1 : Nat) : ℝ)^(2*(n-2))) *
        (if ¬ forbiddenForest (comb b as) F then 1 else 0) := by
  by_cases hg : ¬ forbiddenForest (comb b as) F
  · simp only [hg,ite_true,mul_one]
    obtain ⟨pre,rest,has,hfront⟩ := combReachable_good_frontier b as F hreach hg
    have hb : b ∈ (comb b pre).leaves := by rw [comb_leaves_eq]; exact Finset.mem_insert_self _ _
    have he := forestFrontier_completion_probability N sample r register F hF b (comb b pre) rest hfront hb
    have hc : completionCombMass F (comb b as) = ENNReal.ofReal (combCoefficient rest.length) := by
      simpa only [has,comb_append,combCoefficient] using he
    rw [hc,ENNReal.toReal_ofReal (le_of_lt (combCoefficient_pos _))]
    have hlen : rest.length ≤ as.length := by simp only [has,List.length_append]; omega
    have hloss := combReachable_proper_loss sample b as n hn F hF hproper hreach hg hsize hcover
    have hcard := forestFrontier_card F hF _ _ hfront
    have hdiff : as.length-rest.length ≤ n-2 := by omega
    exact combCoefficient_loss_bound rest.length as.length (n-2) hlen hdiff
  · have hbad : forbiddenForest (comb b as) F := not_not.mp hg
    obtain ⟨A,⟨g,hgF,hA⟩,hnot⟩ := hbad
    rw [independent_wrong_clade_completion_zero N sample r register F hF b (comb b as) g hgF A hA hnot]
    simp only [ENNReal.toReal_zero,hg,ite_false,mul_zero,le_refl]

lemma forestProgram_supportInvariant (ops : List (Finset Copy × ℝ≥0))
    (R : Forest Copy → Prop)
    (hstep : ∀ op ∈ ops, ∀ F, R F → ∀ G ∈ (cladeKernel op.1 op.2 F).support, R G)
    (F : Forest Copy) (hF : R F) {G : Forest Copy}
    (hG : G ∈ (forestProgram ops F).support) : R G := by
  induction ops generalizing F with
  | nil =>
      have he : G = F := by simpa only [forestProgram,PMF.mem_support_pure_iff] using hG
      simpa only [he] using hF
  | cons op ops ih =>
      obtain ⟨M,hM,hG⟩ := (PMF.mem_support_bind_iff _ _ _).mp hG
      exact ih (fun q hq => hstep q (List.mem_cons_of_mem op hq)) M
        (hstep op (List.mem_cons_self ..) F hF M hM) hG

lemma positiveWord_reachable (N : RootedBinary V E X)
    (sample : Copy → X) (register : V → Bool) (w : CladeWeights X)
    (hw : w Finset.univ = 0) (keys : List (Finset X))
    (b : Copy) (as : List Copy) (F : Forest Copy)
    (hF : Partition F) (hp : TaxonProperForest sample F) (hr : CombReachable b as F)
    {G : Forest Copy} (hG : G ∈ (forestProgram (positiveCladeWord w sample keys) F).support) :
    Partition G ∧ TaxonProperForest sample G ∧ CombReachable b as G := by
  apply forestProgram_supportInvariant (positiveCladeWord w sample keys)
    (fun G => Partition G ∧ TaxonProperForest sample G ∧ CombReachable b as G) _ F ⟨hF,hp,hr⟩ hG
  intro op hop H hH M hM
  obtain ⟨A,_,hpos,rfl⟩ := (mem_positiveCladeWord w sample keys op).mp hop
  have hA : A ≠ Finset.univ := by intro he; apply hpos; simpa only [he] using hw
  exact ⟨cladeKernel_partition _ _ H hH.1 hM,
    cladeKernel_taxonProper sample A hA (w A) H hH.2.1 hM,
    cladeKernel_combReachable N sample register b as _ _ H hH.1 hH.2.2 hM⟩

lemma programCombMass_reader_upper (ops : List (Finset Copy × ℝ≥0))
    (F : Forest Copy) (target : Genealogy Copy) (B : ℝ)
    (h : ∀ G ∈ (forestProgram ops F).support, (completionCombMass G target).toReal ≤
      B*(if ¬ forbiddenForest target G then 1 else 0)) :
    programCombMass ops F target ≤ B*goodMass (forestProgram ops F)
      (fun G => ¬ forbiddenForest target G) := by
  rw [programCombMass_sum]
  calc
    _ ≤ ∑ G : Forest Copy, (forestProgram ops F G).toReal *
        (B*(if ¬ forbiddenForest target G then 1 else 0)) := by
      apply Finset.sum_le_sum
      intro G _
      by_cases hz : forestProgram ops F G = 0
      · simp only [hz,ENNReal.toReal_zero,zero_mul,le_refl]
      · exact mul_le_mul_of_nonneg_left (h G ((PMF.mem_support_iff _ _).mpr hz)) ENNReal.toReal_nonneg
    _ = _ := by
      rw [goodMass,PMF.map,UnifiedLean.Source.SourcePoissonExponential.bind_probability_real,
        tsum_fintype,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro G _
      by_cases hg : forbiddenForest target G <;> simp [hg,mul_assoc,mul_left_comm,mul_comm]

end RootReaderUpperBound

section OrdinaryCombSandwich
variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq X] [DecidableEq Copy]
open DotG34.SpecifiedCombEvent

lemma initialForest_frontier (b : Copy) (as : List Copy)
    (hcover : ∀ x, x = b ∨ x ∈ as) (hb : b ∉ as) (hn : as.Nodup) :
    ForestFrontier initialForest (.leaf b) as := by
  refine ⟨?_,?_,?_,?_,hn⟩
  · exact ⟨treeLeaf b,Finset.mem_image.mpr ⟨b,Finset.mem_univ _,rfl⟩,UnorderedEquiv.refl _⟩
  · intro a _; exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,rfl⟩
  · intro x
    simpa only [Genealogy.leaves,Finset.mem_singleton] using hcover x
  · intro a ha he
    have he' : a = b := Finset.mem_singleton.mp he
    exact hb (he' ▸ ha)

lemma initialForest_not_forbidden (target : Genealogy Copy) :
    ¬ forbiddenForest target initialForest := by
  rintro ⟨A,⟨g,hg,hA⟩,_⟩
  obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hg
  simpa only [treeLeaf,internalClades,Finset.notMem_empty] using hA

lemma initial_completionCombMass (N : RootedBinary V E X) (sample : Copy → X)
    (r : PositivePairRates E) (register : V → Bool) (b : Copy) (as : List Copy)
    (hcover : ∀ x, x = b ∨ x ∈ as) (hb : b ∉ as) (hn : as.Nodup) :
    (completionCombMass initialForest (comb b as)).toReal = combCoefficient as.length := by
  have he := forestFrontier_completion_probability N sample r register initialForest
    initialForest_partition b (.leaf b) as (initialForest_frontier b as hcover hb hn)
    (Finset.mem_singleton_self b)
  change completionCombMass initialForest (comb b as) = ENNReal.ofReal (combCoefficient as.length) at he
  rw [he,ENNReal.toReal_ofReal (le_of_lt (combCoefficient_pos _))]

noncomputable def ordinaryCombProbability (w : CladeWeights X) (sample : Copy → X)
    (b : Copy) (as : List Copy) : ℝ :=
  (ordinaryCompletedTreeLaw w sample {toUnranked (comb b as)}).toReal

lemma ordinaryCombProbability_positiveWord (w : CladeWeights X) (sample : Copy → X)
    (b : Copy) (as : List Copy) :
    ordinaryCombProbability w sample b as =
      programCombMass (positiveCladeWord w sample (cladeOrder X)) initialForest (comb b as) := by
  rw [ordinaryCombProbability,ordinaryCompletedTreeLaw,ordinaryCladeProgram_positiveWord]
  rfl

/-- The inherited all-copy caterpillar sandwich on the independently constructed
ordinary evaluator. Uniformity in copy number follows from the explicit n−2
loss bound and the polynomial coefficient ratio, not a matrix-size constant. -/
theorem ordinary_comb_probability_sandwich (N : RootedBinary V E X)
    (sample : Copy → X) (r : PositivePairRates E) (register : V → Bool)
    (w : CladeWeights X) (hw : w Finset.univ = 0)
    (b : Copy) (as : List Copy) (n : Nat) (hn : 2 ≤ n) (hX : 2 ≤ Fintype.card X)
    (hlen : n-1 ≤ as.length) (hsize : Fintype.card Copy = as.length+1)
    (hcopy : ∀ x, x = b ∨ x ∈ as) (hb : b ∉ as) (hnodup : as.Nodup)
    (hcover : (insert b (as.take (n-1)).toFinset).image sample = Finset.univ)
    (hK : ∀ A ∈ cladeOrder X, w A ≠ 0 → n ≤ (cladeCopySet sample A).card) :
    combCoefficient as.length * Real.exp
        (-fixedForestHazard initialForest (positiveCladeWord w sample (cladeOrder X))) ≤
      ordinaryCombProbability w sample b as ∧
    ordinaryCombProbability w sample b as ≤
      combCoefficient as.length * ((as.length+1 : Nat) : ℝ)^(2*(n-2)) *
        Real.exp (((positiveCladeWord w sample (cladeOrder X)).map (compatibleCost n)).sum) := by
  let ops := positiveCladeWord w sample (cladeOrder X)
  have hp : TaxonProperForest sample initialForest := initialForest_taxonProper sample hX
  have hr : CombReachable b as initialForest := initialForest_combReachable b as hcopy hb hnodup
  have hg : ¬ forbiddenForest (comb b as) initialForest := initialForest_not_forbidden _
  constructor
  · rw [ordinaryCombProbability_positiveWord]
    have hl := programCombMass_no_merger_lower ops initialForest initialForest_partition (comb b as)
    rw [initial_completionCombMass N sample r register b as hcopy hb hnodup] at hl
    simpa only [mul_comm] using hl
  · rw [ordinaryCombProbability_positiveWord]
    have hreader := programCombMass_reader_upper ops initialForest (comb b as)
      (combCoefficient as.length*((as.length+1 : Nat) : ℝ)^(2*(n-2))) (by
        intro G hG
        have hstate := positiveWord_reachable N sample register w hw (cladeOrder X)
          b as initialForest initialForest_partition hp hr hG
        exact reachable_completion_coefficient_bound N sample r register b as n hn hsize hcover
          G hstate.1 hstate.2.1 hstate.2.2)
    apply hreader.trans
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    have hu := actual_word_compatible_mass_bound N sample register w hw (cladeOrder X)
      b as n hn hlen hsize hcover hK initialForest initialForest_partition hp hr hg
    rw [ordinaryCladeProgram_positiveWord] at hu
    exact hu

end OrdinaryCombSandwich

section AllTaxonAllocations
variable {X : Type*} [Fintype X] [DecidableEq X]

abbrev AllocationCopy (v : X → Nat) (scale : Nat) := Σ x : X, Fin (scale*v x)

def allocationSample {v : X → Nat} {scale : Nat} (c : AllocationCopy v scale) : X := c.1

noncomputable def allocationRep (v : X → Nat) (hv : ∀ x, 0 < v x)
    (scale : Nat) (hscale : 0 < scale) (x : X) : AllocationCopy v scale :=
  ⟨x,⟨0,Nat.mul_pos hscale (hv x)⟩⟩

lemma allocationRep_injective (v : X → Nat) (hv : ∀ x, 0 < v x)
    (scale : Nat) (hscale : 0 < scale) : Function.Injective (allocationRep v hv scale hscale) := by
  intro x y he
  exact congrArg Sigma.fst he

lemma allocationSample_surjective (v : X → Nat) (hv : ∀ x, 0 < v x)
    (scale : Nat) (hscale : 0 < scale) :
    Function.Surjective (allocationSample (v := v) (scale := scale)) := by
  intro x
  exact ⟨allocationRep v hv scale hscale x,rfl⟩

noncomputable def allocationFirstTail (v : X → Nat) (hv : ∀ x, 0 < v x)
    (scale : Nat) (hscale : 0 < scale) (x0 : X) : List (AllocationCopy v scale) :=
  ((Finset.univ : Finset X).erase x0).toList.map (allocationRep v hv scale hscale)

noncomputable def allocationExtras (v : X → Nat) (hv : ∀ x, 0 < v x)
    (scale : Nat) (hscale : 0 < scale) : Finset (AllocationCopy v scale) :=
  Finset.univ \ Finset.univ.image (allocationRep v hv scale hscale)

noncomputable def allocationCombTail (v : X → Nat) (hv : ∀ x, 0 < v x)
    (scale : Nat) (hscale : 0 < scale) (x0 : X) : List (AllocationCopy v scale) :=
  allocationFirstTail v hv scale hscale x0 ++ (allocationExtras v hv scale hscale).toList

lemma allocationFirstTail_length (v : X → Nat) (hv : ∀ x, 0 < v x)
    (scale : Nat) (hscale : 0 < scale) (x0 : X) :
    (allocationFirstTail v hv scale hscale x0).length = Fintype.card X-1 := by
  simp only [allocationFirstTail,List.length_map,Finset.length_toList,
    Finset.card_erase_of_mem (Finset.mem_univ x0),Finset.card_univ]

lemma allocationCombTail_nodup (v : X → Nat) (hv : ∀ x, 0 < v x)
    (scale : Nat) (hscale : 0 < scale) (x0 : X) :
    (allocationCombTail v hv scale hscale x0).Nodup := by
  apply List.nodup_append.mpr
  refine ⟨?_,Finset.nodup_toList _,?_⟩
  · exact (Finset.nodup_toList _).map (allocationRep_injective v hv scale hscale)
  · intro c hc hc'
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hc
    have hm := (Finset.mem_sdiff.mp (Finset.mem_toList.mp hc')).2
    exact hm (Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩)

lemma allocationCombTail_excludes_head (v : X → Nat) (hv : ∀ x, 0 < v x)
    (scale : Nat) (hscale : 0 < scale) (x0 : X) :
    allocationRep v hv scale hscale x0 ∉ allocationCombTail v hv scale hscale x0 := by
  intro hm
  rcases List.mem_append.mp hm with hm | hm
  · obtain ⟨x,hx,he⟩ := List.mem_map.mp hm
    have he' := allocationRep_injective v hv scale hscale he
    subst x
    exact (Finset.mem_erase.mp (Finset.mem_toList.mp hx)).1 rfl
  · exact (Finset.mem_sdiff.mp (Finset.mem_toList.mp hm)).2
      (Finset.mem_image.mpr ⟨x0,Finset.mem_univ _,rfl⟩)

lemma allocationCombTail_covers (v : X → Nat) (hv : ∀ x, 0 < v x)
    (scale : Nat) (hscale : 0 < scale) (x0 : X) (c : AllocationCopy v scale) :
    c = allocationRep v hv scale hscale x0 ∨ c ∈ allocationCombTail v hv scale hscale x0 := by
  by_cases hm : c ∈ Finset.univ.image (allocationRep v hv scale hscale)
  · obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp hm
    by_cases hx : x = x0
    · exact Or.inl (hx ▸ rfl)
    · right
      apply List.mem_append_left
      apply List.mem_map.mpr
      exact ⟨x,Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨hx,Finset.mem_univ _⟩),rfl⟩
  · right
    apply List.mem_append_right
    exact Finset.mem_toList.mpr (Finset.mem_sdiff.mpr ⟨Finset.mem_univ _,hm⟩)

lemma allocationCombTail_card (v : X → Nat) (hv : ∀ x, 0 < v x)
    (scale : Nat) (hscale : 0 < scale) (x0 : X) :
    Fintype.card (AllocationCopy v scale) = (allocationCombTail v hv scale hscale x0).length+1 := by
  have he : insert (allocationRep v hv scale hscale x0)
      (allocationCombTail v hv scale hscale x0).toFinset = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro c
    rcases allocationCombTail_covers v hv scale hscale x0 c with hc | hc
    · exact Finset.mem_insert.mpr (Or.inl hc)
    · exact Finset.mem_insert.mpr (Or.inr (List.mem_toFinset.mpr hc))
  have hc := congrArg Finset.card he
  rw [Finset.card_univ,Finset.card_insert_of_notMem (by
    simpa only [List.mem_toFinset] using allocationCombTail_excludes_head v hv scale hscale x0),
    List.toFinset_card_of_nodup (allocationCombTail_nodup v hv scale hscale x0)] at hc
  exact hc.symm

lemma allocationCombTail_first_taxa (v : X → Nat) (hv : ∀ x, 0 < v x)
    (scale : Nat) (hscale : 0 < scale) (x0 : X) :
    (insert (allocationRep v hv scale hscale x0)
      ((allocationCombTail v hv scale hscale x0).take (Fintype.card X-1)).toFinset).image
        allocationSample = Finset.univ := by
  have ht : (allocationCombTail v hv scale hscale x0).take (Fintype.card X-1) =
      allocationFirstTail v hv scale hscale x0 := by
    rw [← allocationFirstTail_length v hv scale hscale x0]
    exact List.take_append_length
  rw [ht]
  apply Finset.eq_univ_iff_forall.mpr
  intro x
  apply Finset.mem_image.mpr
  refine ⟨allocationRep v hv scale hscale x,?_,rfl⟩
  by_cases hx : x = x0
  · subst x
    exact Finset.mem_insert_self _ _
  · apply Finset.mem_insert_of_mem
    apply List.mem_toFinset.mpr
    apply List.mem_map.mpr
    exact ⟨x,Finset.mem_toList.mpr (Finset.mem_erase.mpr ⟨hx,Finset.mem_univ _⟩),rfl⟩

lemma allocation_clade_card (v : X → Nat) (scale : Nat) (A : Finset X) :
    (cladeCopySet (allocationSample (v := v) (scale := scale)) A).card =
      scale * ∑ x ∈ A, v x := by
  calc
    _ = ∑ c : AllocationCopy v scale, if c.1 ∈ A then (1 : Nat) else 0 := by
      simp only [cladeCopySet,allocationSample,Finset.sum_boole]
    _ = ∑ x : X, if x ∈ A then scale*v x else 0 := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ A <;> simp [hx]
    _ = ∑ x ∈ A, scale*v x := by simp only [← Finset.sum_filter]; simp
    _ = _ := by rw [Finset.mul_sum]

lemma allocation_clade_card_lower (v : X → Nat) (hv : ∀ x, 0 < v x)
    (scale : Nat) (A : Finset X) (hA : A.Nonempty) :
    scale ≤ (cladeCopySet (allocationSample (v := v) (scale := scale)) A).card := by
  rw [allocation_clade_card]
  obtain ⟨x,hx⟩ := hA
  have hsum : 1 ≤ ∑ x ∈ A, v x := (hv x).trans_le
    (Finset.single_le_sum (fun _ _ => Nat.zero_le _) hx)
  simpa only [Nat.mul_one] using Nat.mul_le_mul_left scale hsum

end AllTaxonAllocations

section AllocationHazardPolynomials
variable {X Copy : Type*} [Fintype X] [Fintype Copy]
variable [DecidableEq X] [DecidableEq Copy]

lemma positiveWord_weighted_sum (w : CladeWeights X) (sample : Copy → X)
    (keys : List (Finset X)) (f : Finset Copy → ℝ) :
    ((positiveCladeWord w sample keys).map (fun op => f op.1*(op.2 : ℝ))).sum =
      (keys.map (fun A => f (cladeCopySet sample A)*(w A : ℝ))).sum := by
  induction keys with
  | nil => rfl
  | cons A keys ih =>
      by_cases hz : w A = 0
      · simp [positiveCladeWord,hz,ih]
      · simp [positiveCladeWord,hz,ih]

noncomputable def totalCladeWeight (w : CladeWeights X) : ℝ := ∑ A : Finset X, (w A : ℝ)

lemma allocation_lower_hazard (w : CladeWeights X) (v : X → Nat) (scale : Nat) :
    fixedForestHazard initialForest (positiveCladeWord w
      (allocationSample (v := v) (scale := scale)) (cladeOrder X)) =
      ((scale : ℝ)^2 * quadraticExposure w (fun x => (v x : ℝ)) -
        (scale : ℝ)*linearExposure w (fun x => (v x : ℝ)))/2 := by
  unfold fixedForestHazard
  simp_rw [initialForest_active_card]
  rw [positiveWord_weighted_sum,cladeOrder_sum]
  simp_rw [allocation_clade_card,Nat.cast_mul,Nat.cast_sum]
  unfold quadraticExposure linearExposure
  rw [Finset.mul_sum,Finset.mul_sum,← Finset.sum_sub_distrib,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro A _
  unfold pairRatePolynomial
  ring

lemma allocation_upper_exponent (w : CladeWeights X) (v : X → Nat) (scale n : Nat) :
    (((positiveCladeWord w (allocationSample (v := v) (scale := scale)) (cladeOrder X)).map
      (compatibleCost n)).sum) =
      -(scale : ℝ)^2/2 * quadraticExposure w (fun x => (v x : ℝ)) +
        (((n : ℝ)-2)+1/2)*(scale : ℝ)*linearExposure w (fun x => (v x : ℝ)) +
        (1-((n : ℝ)-2)*((n : ℝ)-1)/2)*totalCladeWeight w := by
  unfold compatibleCost
  rw [positiveWord_weighted_sum,cladeOrder_sum]
  simp_rw [allocation_clade_card,Nat.cast_mul,Nat.cast_sum]
  unfold quadraticExposure linearExposure totalCladeWeight
  rw [Finset.mul_sum,Finset.mul_sum,Finset.mul_sum,← Finset.sum_add_distrib,← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A _
  unfold pairRatePolynomial
  ring

end AllocationHazardPolynomials

section QuadraticDecay
open Filter Topology

/-- The classical ratio step: a strictly negative quadratic exponent dominates
any fixed power, with no finite-state dimension appearing in the constants. -/
lemma polynomial_quadratic_exp_tendsto_zero (d : Nat) (S c a b : ℝ)
    (hS : 0 ≤ S) (hc : 0 < c) :
    Tendsto (fun k : Nat => ((((k : ℝ)+1)*S)^d *
      Real.exp (-c*((k : ℝ)+1)^2+a*((k : ℝ)+1)+b))) atTop (𝓝 0) := by
  have hx : Tendsto (fun k : Nat => (k : ℝ)+1) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds
  have hbase := (Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero d).comp hx
  have hupper : Tendsto (fun k : Nat => S^d*Real.exp b *
      (((k : ℝ)+1)^d*Real.exp (-((k : ℝ)+1)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hbase.const_mul (S^d*Real.exp b)
  apply squeeze_zero' (Eventually.of_forall (fun k => by positivity)) _ hupper
  filter_upwards [hx.eventually (eventually_ge_atTop ((a+1)/c))] with k hk
  have hnonneg : 0 ≤ (k : ℝ)+1 := by positivity
  have hcK : a+1 ≤ c*((k : ℝ)+1) := by
    have h := (div_le_iff₀ hc).mp hk
    nlinarith
  have hmul := mul_le_mul_of_nonneg_right hcK hnonneg
  have hexp : -c*((k : ℝ)+1)^2+a*((k : ℝ)+1)+b ≤ -((k : ℝ)+1)+b := by nlinarith
  calc
    _ ≤ ((((k : ℝ)+1)*S)^d * Real.exp (-((k : ℝ)+1)+b)) :=
      mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hexp) (by positivity)
    _ = _ := by rw [mul_pow,Real.exp_add]; ring

end QuadraticDecay

section ScaledLegalProfiles
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E] [DecidableEq X]

noncomputable def allocationProfile (w : CladeWeights X) (v : X → Nat)
    (hv : ∀ x, 0 < v x) (x0 : X) (k : Nat) : ℝ :=
  ordinaryCombProbability w allocationSample (allocationRep v hv (k+1) (Nat.succ_pos _) x0)
    (allocationCombTail v hv (k+1) (Nat.succ_pos _) x0)

noncomputable def allocationCoefficient (v : X → Nat)
    (hv : ∀ x, 0 < v x) (x0 : X) (k : Nat) : ℝ :=
  combCoefficient (allocationCombTail v hv (k+1) (Nat.succ_pos _) x0).length

noncomputable def lowerProfileExponent (w : CladeWeights X) (v : X → Nat) (scale : ℝ) : ℝ :=
  -scale^2/2*quadraticExposure w (fun x => (v x : ℝ)) +
    scale/2*linearExposure w (fun x => (v x : ℝ))

noncomputable def upperProfileExponent (w : CladeWeights X) (v : X → Nat) (scale : ℝ) : ℝ :=
  -scale^2/2*quadraticExposure w (fun x => (v x : ℝ)) +
    (((Fintype.card X : ℝ)-2)+1/2)*scale*linearExposure w (fun x => (v x : ℝ)) +
    (1-((Fintype.card X : ℝ)-2)*((Fintype.card X : ℝ)-1)/2)*totalCladeWeight w

lemma allocation_card (v : X → Nat) (scale : Nat) :
    Fintype.card (AllocationCopy v scale) = scale*∑ x, v x := by
  simp only [AllocationCopy,Fintype.card_sigma,Fintype.card_fin,Finset.mul_sum]

lemma allocation_profile_sandwich (N : RootedBinary V E X) (r : PositivePairRates E)
    (w : CladeWeights X) (he : w ∅ = 0) (hu : w Finset.univ = 0)
    (hn : 2 ≤ Fintype.card X) (v : X → Nat) (hv : ∀ x, 0 < v x) (x0 : X)
    (k : Nat) (hk : Fintype.card X ≤ k+1) :
    allocationCoefficient v hv x0 k * Real.exp (lowerProfileExponent w v ((k : ℝ)+1)) ≤
      allocationProfile w v hv x0 k ∧
    allocationProfile w v hv x0 k ≤
      allocationCoefficient v hv x0 k *
        (((k : ℝ)+1)*(∑ x, (v x : ℝ)))^(2*(Fintype.card X-2)) *
        Real.exp (upperProfileExponent w v ((k : ℝ)+1)) := by
  let sample := allocationSample (v := v) (scale := k+1)
  let b := allocationRep v hv (k+1) (Nat.succ_pos _) x0
  let as := allocationCombTail v hv (k+1) (Nat.succ_pos _) x0
  have hlen : Fintype.card X-1 ≤ as.length := by
    dsimp [as,allocationCombTail]
    rw [List.length_append,allocationFirstTail_length]
    omega
  have hK : ∀ A ∈ cladeOrder X, w A ≠ 0 → Fintype.card X ≤ (cladeCopySet sample A).card := by
    intro A _ hA
    have hne : A ≠ ∅ := by intro ha; apply hA; simpa only [ha] using he
    exact hk.trans (allocation_clade_card_lower v hv (k+1) A (Finset.nonempty_iff_ne_empty.mpr hne))
  have h := ordinary_comb_probability_sandwich N sample r (fun _ => false) w hu b as
    (Fintype.card X) hn hn hlen (allocationCombTail_card v hv (k+1) (Nat.succ_pos _) x0)
    (allocationCombTail_covers v hv (k+1) (Nat.succ_pos _) x0)
    (allocationCombTail_excludes_head v hv (k+1) (Nat.succ_pos _) x0)
    (allocationCombTail_nodup v hv (k+1) (Nat.succ_pos _) x0)
    (allocationCombTail_first_taxa v hv (k+1) (Nat.succ_pos _) x0) hK
  have hsize : ((as.length+1 : Nat) : ℝ) = ((k : ℝ)+1)*∑ x, (v x : ℝ) := by
    rw [← allocationCombTail_card v hv (k+1) (Nat.succ_pos _) x0,allocation_card]
    push_cast
    rfl
  rw [allocation_lower_hazard,allocation_upper_exponent,hsize] at h
  convert h using 1 <;>
    simp only [allocationCoefficient,allocationProfile,lowerProfileExponent,upperProfileExponent,
      Nat.cast_add,Nat.cast_one] <;> ring

lemma allocationProfile_pos (N : RootedBinary V E X) (r : PositivePairRates E)
    (w : CladeWeights X) (v : X → Nat) (hv : ∀ x, 0 < v x) (x0 : X) (k : Nat) :
    0 < allocationProfile w v hv x0 k := by
  rw [allocationProfile,ordinaryCombProbability_positiveWord]
  have h := programCombMass_no_merger_lower
    (positiveCladeWord w allocationSample (cladeOrder X)) initialForest initialForest_partition
    (DotG34.SpecifiedCombEvent.comb (allocationRep v hv (k+1) (Nat.succ_pos _) x0)
      (allocationCombTail v hv (k+1) (Nat.succ_pos _) x0))
  rw [initial_completionCombMass N allocationSample r (fun _ => false)
    _ _ (allocationCombTail_covers v hv (k+1) (Nat.succ_pos _) x0)
    (allocationCombTail_excludes_head v hv (k+1) (Nat.succ_pos _) x0)
    (allocationCombTail_nodup v hv (k+1) (Nat.succ_pos _) x0)] at h
  exact (mul_pos (Real.exp_pos _) (combCoefficient_pos _)).trans_le h

end ScaledLegalProfiles

section ActualProfileRatios
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E] [DecidableEq X]
open Filter Topology

/-- The strict quadratic order gives the classical vanishing-ratio criterion
for actual legal all-taxon comb queries, including arbitrary fixed positive
integer allocation vectors. -/
theorem allocationProfile_ratio_tendsto_zero (N : RootedBinary V E X)
    (r : PositivePairRates E) (hn : 2 ≤ Fintype.card X)
    (w u : CladeWeights X) (hwe : w ∅ = 0) (hwu : w Finset.univ = 0)
    (hue : u ∅ = 0) (huu : u Finset.univ = 0)
    (v : X → Nat) (hv : ∀ x, 0 < v x) (x0 : X)
    (hQ : quadraticExposure w (fun x => (v x : ℝ)) < quadraticExposure u (fun x => (v x : ℝ))) :
    Tendsto (fun k => allocationProfile u v hv x0 k / allocationProfile w v hv x0 k)
      atTop (𝓝 0) := by
  let c := (quadraticExposure u (fun x => (v x : ℝ)) -
    quadraticExposure w (fun x => (v x : ℝ)))/2
  let a := (((Fintype.card X : ℝ)-2)+1/2)*linearExposure u (fun x => (v x : ℝ)) -
    linearExposure w (fun x => (v x : ℝ))/2
  let b := (1-((Fintype.card X : ℝ)-2)*((Fintype.card X : ℝ)-1)/2)*totalCladeWeight u
  let S : ℝ := ∑ x, (v x : ℝ)
  let d := 2*(Fintype.card X-2)
  have hc : 0 < c := by dsimp [c]; linarith
  have hlim := polynomial_quadratic_exp_tendsto_zero d S c a b (by dsimp [S]; positivity) hc
  apply squeeze_zero' (Eventually.of_forall (fun k => div_nonneg
    (le_of_lt (allocationProfile_pos N r u v hv x0 k))
    (le_of_lt (allocationProfile_pos N r w v hv x0 k)))) _ hlim
  filter_upwards [eventually_ge_atTop (Fintype.card X)] with k hk
  have hk' : Fintype.card X ≤ k+1 := by omega
  have hlow := (allocation_profile_sandwich N r w hwe hwu hn v hv x0 k hk').1
  have hupp := (allocation_profile_sandwich N r u hue huu hn v hv x0 k hk').2
  have hcoef : 0 < allocationCoefficient v hv x0 k := combCoefficient_pos _
  have hrat := div_le_div₀ (by positivity) hupp
    (mul_pos hcoef (Real.exp_pos _)) hlow
  apply hrat.trans_eq
  have hexp : upperProfileExponent u v ((k : ℝ)+1) - lowerProfileExponent w v ((k : ℝ)+1) =
      -c*((k : ℝ)+1)^2+a*((k : ℝ)+1)+b := by
    unfold upperProfileExponent lowerProfileExponent
    dsimp [a,b,c]
    ring
  rw [show (allocationCoefficient v hv x0 k *
        (((k : ℝ)+1)*S)^d * Real.exp (upperProfileExponent u v ((k : ℝ)+1))) /
      (allocationCoefficient v hv x0 k * Real.exp (lowerProfileExponent w v ((k : ℝ)+1))) =
      (((k : ℝ)+1)*S)^d *
        (Real.exp (upperProfileExponent u v ((k : ℝ)+1)) /
          Real.exp (lowerProfileExponent w v ((k : ℝ)+1))) by
        field_simp [ne_of_gt hcoef]]
  rw [← Real.exp_sub,hexp]

end ActualProfileRatios

section FiniteProfileIndependence
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E] [DecidableEq X]
open Filter Topology

/-- Classical minimal-quadratic-term elimination, applied to the proved legal
profile ratios. Coefficients are arbitrary signed reals. -/
theorem allocation_profiles_signed_independent (N : RootedBinary V E X)
    (r : PositivePairRates E) (hn : 2 ≤ Fintype.card X)
    (H : Finset (CladeWeights X)) (hH : ∀ w ∈ H, LaminarWeights w)
    (v : X → Nat) (hv : ∀ x, 0 < v x) (x0 : X)
    (hQ : Set.InjOn (fun w => quadraticExposure w (fun x => (v x : ℝ))) (H : Set (CladeWeights X)))
    (c : CladeWeights X → ℝ)
    (hz : ∀ k : Nat, ∑ w ∈ H, c w * allocationProfile w v hv x0 k = 0) :
    ∀ w ∈ H, c w = 0 := by
  by_contra hnot
  push_neg at hnot
  obtain ⟨u,hu,hcu⟩ := hnot
  let S := H.filter (fun w => c w ≠ 0)
  have hS : S.Nonempty := ⟨u,Finset.mem_filter.mpr ⟨hu,hcu⟩⟩
  obtain ⟨w,hw,hmin⟩ := Finset.exists_min_image S
    (fun z => quadraticExposure z (fun x => (v x : ℝ))) hS
  have hwH : w ∈ H := (Finset.mem_filter.mp hw).1
  have hcw : c w ≠ 0 := (Finset.mem_filter.mp hw).2
  have hterm (z : CladeWeights X) (hzH : z ∈ H) :
      Tendsto (fun k => c z * (allocationProfile z v hv x0 k / allocationProfile w v hv x0 k))
        atTop (𝓝 (if z = w then c w else 0)) := by
    by_cases hzw : z = w
    · subst z
      have he (k : Nat) : allocationProfile w v hv x0 k / allocationProfile w v hv x0 k = 1 :=
        div_self (ne_of_gt (allocationProfile_pos N r w v hv x0 k))
      simpa only [he,mul_one,ite_true] using (tendsto_const_nhds : Tendsto (fun _ : Nat => c w) atTop (𝓝 (c w)))
    · by_cases hcz : c z = 0
      · simp only [hcz,zero_mul,hzw,ite_false]
        exact tendsto_const_nhds
      · have hzS : z ∈ S := Finset.mem_filter.mpr ⟨hzH,hcz⟩
        have hlt : quadraticExposure w (fun x => (v x : ℝ)) <
            quadraticExposure z (fun x => (v x : ℝ)) := by
          apply lt_of_le_of_ne (hmin z hzS)
          intro he
          exact hzw (hQ hzH hwH he.symm)
        have hratio := allocationProfile_ratio_tendsto_zero N r hn w z
          (hH w hwH).1 (hH w hwH).2.1 (hH z hzH).1 (hH z hzH).2.1 v hv x0 hlt
        simpa only [hzw,ite_false,mul_zero] using hratio.const_mul (c z)
  have hsum := tendsto_finsetSum H hterm
  have hs0 (k : Nat) :
      (∑ z ∈ H, c z * (allocationProfile z v hv x0 k / allocationProfile w v hv x0 k)) = 0 := by
    calc
      _ = (∑ z ∈ H, c z * allocationProfile z v hv x0 k) / allocationProfile w v hv x0 k := by
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro z _
        ring
      _ = 0 := by rw [hz,zero_div]
  have hval : (∑ z ∈ H, if z = w then c w else 0) = c w := by simp [hwH]
  rw [hval] at hsum
  have he : (0 : ℝ) = c w := tendsto_nhds_unique tendsto_const_nhds
    (by simpa only [hs0] using hsum)
  exact hcw he.symm

/-- Every finite catalogue admits a single positive integer allocation vector
whose legal all-copy comb sequence separates all signed mixture weights. -/
theorem finite_catalogue_has_separating_profiles (N : RootedBinary V E X)
    (r : PositivePairRates E) (hn : 2 ≤ Fintype.card X) (x0 : X)
    (H : Finset (CladeWeights X)) (hH : ∀ w ∈ H, LaminarWeights w) :
    ∃ v : X → Nat, ∃ hv : ∀ x, 0 < v x,
      ∀ c : CladeWeights X → ℝ,
        (∀ k : Nat, ∑ w ∈ H, c w * allocationProfile w v hv x0 k = 0) →
        ∀ w ∈ H, c w = 0 := by
  obtain ⟨v,hv,hQ⟩ := finite_catalogue_integer_quadratic_separation H hH
  exact ⟨v,hv,fun c hz => allocation_profiles_signed_independent N r hn H hH v hv x0 hQ c hz⟩

end FiniteProfileIndependence

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
