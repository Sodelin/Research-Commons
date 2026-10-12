import G4WeightedOrdinaryTreeLaw
import G4ActualPositiveGridUniqueness
import G7SinglePopulationPolynomialKernel

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
      rw [← positive_clade_is_covariance_threshold u hu A hp hi]
      ext j
      simp only [covarianceThreshold,Finset.mem_filter,Finset.mem_univ,true_and,he]
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
    obtain ⟨j,hj⟩ := Finset.exists_notMem_of_ne_univ hproper
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

end Coordinates

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
