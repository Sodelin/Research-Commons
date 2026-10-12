import UnifiedLean.Source.FiniteGenealogyEncoding
import SourceForestKingmanProjection
import UnifiedLean.Source.SourcePoissonExponential
import UnifiedLean.Source.SourceCompletedUnrankedTree
import G5CommonSwitchingQuartetWitness
import G1ActualDisplayedTreeFamily
import UnifiedLean.Source.OriginalFixedIDControls
import Mathlib.Probability.Distributions.Uniform

/-!
# Independent weighted ordinary-tree evaluator and actual COMMON transport

Contributor: dot (OpenAI), 12 October 2026. WORK IN PROGRESS / UNCOMPILED.
Formal composition toward Section 2 of the accepted October 8 whole-COMMON
argument; no novelty claim. This file constructs an independent finite forest
carrier and ordinary clade kernels. The actual controlled-source equality and
normalization proof are still being assembled. No equality is an interface
field and no ordinary evaluator is defined by aliasing the network source.

Original-copy labels and complete ordered binary genealogies are retained until
the actual child-swap quotient observation. Ordered pairs each have half-rate.
The intended scope includes heterogeneous leaf ages and original-ID globally
forced masks, with one original COMMON bank. A forced routing bit does not
replace the original stored register. All original taxa determine normalization;
the arbitrary copy allocation is an input only to the ordinary evaluator.
-/
namespace DotG4.WeightedOrdinaryTreeLaw
open Nanuq.Source GProgram.SourceForest
open GProgram.SourceForestKingmanProjection GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.FiniteGenealogyEncoding
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourcePoissonExponential
open Matrix NormedSpace
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.SourceCompletedUnrankedTree
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeCommonPairGerm
open UnifiedLean.Source.OriginalFixedIDControls
open GProgram.G5 GProgram.G5.AttainedChronology GProgram.G5.Normalization
open G1ActualDisplayedTreeFamily G1ActualDisplayedClusterSplitTransport
open G1ActualSelectedClusterTransport
open scoped Classical BigOperators NNReal Matrix.Norms.Operator

section Forest
variable {Copy : Type*} [Fintype Copy] [DecidableEq Copy]

/-- Finite carrier independent of any original graph, population or register.
Invalid partitions are permitted in the ambient carrier, with identity behavior
outside the explicit legal-pair predicate. Actual transport uses Partition. -/
abbrev Forest (Copy : Type*) [DecidableEq Copy] := Finset (WellLabelledTree Copy)

noncomputable def treeLeaf (x : Copy) : WellLabelledTree Copy := ⟨.leaf x,trivial⟩

noncomputable def initialForest : Forest Copy := Finset.univ.image treeLeaf

/-- Complete leaf fibres, not one representative label, determine a forest. -/
def Partition (F : Forest Copy) : Prop :=
  (∀ t ∈ F, ∀ u ∈ F, t ≠ u → Disjoint t.val.leaves u.val.leaves) ∧
  (∀ x : Copy, ∃ t ∈ F, x ∈ t.val.leaves)

lemma initialForest_partition : Partition (initialForest (Copy := Copy)) := by
  constructor
  · intro t ht u hu htu
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨y,_,rfl⟩ := Finset.mem_image.mp hu
    have hxy : x ≠ y := by intro h; subst y; exact htu rfl
    simpa [treeLeaf,Genealogy.leaves] using hxy
  · intro x
    exact ⟨treeLeaf x,Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩,
      Finset.mem_singleton_self x⟩

noncomputable def treeGraft (a b : WellLabelledTree Copy)
    (h : Disjoint a.val.leaves b.val.leaves) : WellLabelledTree Copy :=
  ⟨.graft a.val b.val, a.property,b.property,h⟩

noncomputable def mergeForest (F : Forest Copy) (a b : WellLabelledTree Copy)
    (h : Disjoint a.val.leaves b.val.leaves) : Forest Copy :=
  insert (treeGraft a b h) ((F.erase a).erase b)

lemma mergeForest_partition (F : Forest Copy) (hF : Partition F)
    (a b : WellLabelledTree Copy) (ha : a ∈ F) (hb : b ∈ F)
    (hd : Disjoint a.val.leaves b.val.leaves) :
    Partition (mergeForest F a b hd) := by
  have hold : ∀ u ∈ (F.erase a).erase b,
      Disjoint (treeGraft a b hd).val.leaves u.val.leaves := by
    intro u hu
    have hum := Finset.mem_erase.mp hu
    have hua := Finset.mem_erase.mp hum.2
    change Disjoint (a.val.leaves ∪ b.val.leaves) u.val.leaves
    exact Finset.disjoint_union_left.mpr
      ⟨hF.1 a ha u hua.2 hua.1.symm,hF.1 b hb u hua.2 hum.1.symm⟩
  constructor
  · intro t ht u hu htu
    rcases Finset.mem_insert.mp ht with rfl | ht
    · rcases Finset.mem_insert.mp hu with rfl | hu
      · exact (htu rfl).elim
      · exact hold u hu
    · rcases Finset.mem_insert.mp hu with rfl | hu
      · exact (hold t ht).symm
      · exact hF.1 t (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht))
          u (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase hu)) htu
  · intro x
    obtain ⟨t,ht,hx⟩ := hF.2 x
    by_cases hta : t = a
    · subst t
      exact ⟨treeGraft a b hd,Finset.mem_insert_self _ _,
        Finset.mem_union.mpr (Or.inl hx)⟩
    · by_cases htb : t = b
      · subst t
        exact ⟨treeGraft a b hd,Finset.mem_insert_self _ _,
          Finset.mem_union.mpr (Or.inr hx)⟩
      · exact ⟨t,Finset.mem_insert_of_mem
          (Finset.mem_erase.mpr ⟨htb,Finset.mem_erase.mpr ⟨hta,ht⟩⟩),hx⟩

lemma treeGraft_ne_left (a b : WellLabelledTree Copy)
    (hd : Disjoint a.val.leaves b.val.leaves) : treeGraft a b hd ≠ a := by
  intro he
  obtain ⟨x,hx⟩ := genealogy_leaves_nonempty b.val
  have hmem : x ∈ (treeGraft a b hd).val.leaves := Finset.mem_union.mpr (Or.inr hx)
  rw [he] at hmem
  exact Finset.disjoint_left.mp hd hmem hx

lemma treeGraft_not_mem (F : Forest Copy) (hF : Partition F)
    (a b : WellLabelledTree Copy) (ha : a ∈ F)
    (hd : Disjoint a.val.leaves b.val.leaves) : treeGraft a b hd ∉ F := by
  intro hg
  have hdis := hF.1 a ha (treeGraft a b hd) hg (treeGraft_ne_left a b hd).symm
  obtain ⟨x,hx⟩ := genealogy_leaves_nonempty a.val
  exact Finset.disjoint_left.mp hdis hx (Finset.mem_union.mpr (Or.inl hx))

lemma mergeForest_card (F : Forest Copy) (hF : Partition F)
    (a b : WellLabelledTree Copy) (ha : a ∈ F) (hb : b ∈ F) (hne : a ≠ b)
    (hd : Disjoint a.val.leaves b.val.leaves) :
    (mergeForest F a b hd).card + 1 = F.card := by
  have hg : treeGraft a b hd ∉ (F.erase a).erase b := by
    intro h
    exact treeGraft_not_mem F hF a b ha hd
      (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase h))
  have hb' : b ∈ F.erase a := Finset.mem_erase.mpr ⟨hne.symm,hb⟩
  have hca := Finset.card_erase_add_one ha
  have hcb := Finset.card_erase_add_one hb'
  rw [mergeForest,Finset.card_insert_of_notMem hg]
  omega

lemma partition_card_le (F : Forest Copy) (hF : Partition F) :
    F.card ≤ Fintype.card Copy := by
  let leaf : {t // t ∈ F} → Copy := fun t =>
    Classical.choose (genealogy_leaves_nonempty t.val.val)
  have hleaf : ∀ t : {t // t ∈ F}, leaf t ∈ t.val.val.leaves :=
    fun t => Classical.choose_spec (genealogy_leaves_nonempty t.val.val)
  have hinj : Function.Injective leaf := by
    intro a b hab
    apply Subtype.ext
    by_contra hne
    have hd := hF.1 a.val a.property b.val b.property hne
    exact Finset.disjoint_left.mp hd (hleaf a) (by simpa only [hab] using hleaf b)
  simpa only [Fintype.card_coe] using Fintype.card_le_of_injective leaf hinj

/-- A clade acts only on complete current trees wholly inside its copy fibre. -/
def LegalPair (F : Forest Copy) (A : Finset Copy)
    (p : WellLabelledTree Copy × WellLabelledTree Copy) : Prop :=
  p.1 ∈ F ∧ p.2 ∈ F ∧ p.1 ≠ p.2 ∧
  p.1.val.leaves ⊆ A ∧ p.2.val.leaves ⊆ A ∧
  Disjoint p.1.val.leaves p.2.val.leaves

noncomputable def pairAction (F : Forest Copy) (A : Finset Copy)
    (p : WellLabelledTree Copy × WellLabelledTree Copy) : Forest Copy :=
  if h : LegalPair F A p then mergeForest F p.1 p.2 h.2.2.2.2.2 else F

lemma pairAction_partition (F : Forest Copy) (hF : Partition F)
    (A : Finset Copy) (p : WellLabelledTree Copy × WellLabelledTree Copy) :
    Partition (pairAction F A p) := by
  unfold pairAction
  split_ifs with h
  · exact mergeForest_partition F hF p.1 p.2 h.1 h.2.1 h.2.2.2.2.2
  · exact hF

lemma disjoint_fibres_tree_ne {A B : Finset Copy} (hAB : Disjoint A B)
    (a b : WellLabelledTree Copy) (ha : a.val.leaves ⊆ A) (hb : b.val.leaves ⊆ B) :
    a ≠ b := by
  intro he
  obtain ⟨x,hx⟩ := genealogy_leaves_nonempty a.val
  exact Finset.disjoint_left.mp hAB (ha hx) (hb (he ▸ hx))

lemma mergeForest_mem_other_fibre (F : Forest Copy) {A B : Finset Copy}
    (hAB : Disjoint A B) (p : WellLabelledTree Copy × WellLabelledTree Copy)
    (hp : LegalPair F A p) (t : WellLabelledTree Copy) (ht : t.val.leaves ⊆ B) :
    t ∈ mergeForest F p.1 p.2 hp.2.2.2.2.2 ↔ t ∈ F := by
  have hta : t ≠ p.1 := (disjoint_fibres_tree_ne hAB p.1 t hp.2.2.2.1 ht).symm
  have htb : t ≠ p.2 := (disjoint_fibres_tree_ne hAB p.2 t hp.2.2.2.2.1 ht).symm
  have hgA : (treeGraft p.1 p.2 hp.2.2.2.2.2).val.leaves ⊆ A :=
    Finset.union_subset hp.2.2.2.1 hp.2.2.2.2.1
  have htg : t ≠ treeGraft p.1 p.2 hp.2.2.2.2.2 :=
    (disjoint_fibres_tree_ne hAB _ t hgA ht).symm
  simp only [mergeForest,Finset.mem_insert,Finset.mem_erase,hta,htb,htg,
    false_or,true_and,not_false_eq_true]

/-- An operation on a disjoint clade cannot enable/disable another clade's
whole-tree ordered pair. This is a statement about actual leaf sets. -/
lemma legalPair_other_fibre (F : Forest Copy) {A B : Finset Copy}
    (hAB : Disjoint A B) (p q : WellLabelledTree Copy × WellLabelledTree Copy) :
    LegalPair (pairAction F A p) B q ↔ LegalPair F B q := by
  unfold pairAction
  split_ifs with hp
  · constructor
    · intro hq
      exact ⟨(mergeForest_mem_other_fibre F hAB p hp q.1 hq.2.2.2.1).mp hq.1,
        (mergeForest_mem_other_fibre F hAB p hp q.2 hq.2.2.2.2.1).mp hq.2.1,
        hq.2.2⟩
    · intro hq
      exact ⟨(mergeForest_mem_other_fibre F hAB p hp q.1 hq.2.2.2.1).mpr hq.1,
        (mergeForest_mem_other_fibre F hAB p hp q.2 hq.2.2.2.2.1).mpr hq.2.1,
        hq.2.2⟩
  · rfl

lemma pairAction_disjoint_commute (F : Forest Copy) {A B : Finset Copy}
    (hAB : Disjoint A B) (p q : WellLabelledTree Copy × WellLabelledTree Copy) :
    pairAction (pairAction F A p) B q = pairAction (pairAction F B q) A p := by
  by_cases hp : LegalPair F A p
  · by_cases hq : LegalPair F B q
    · have hq' := (legalPair_other_fibre F hAB p q).mpr hq
      have hp' := (legalPair_other_fibre F hAB.symm q p).mpr hp
      rw [pairAction,dif_pos hq',pairAction,dif_pos hp',
        pairAction,dif_pos hp,pairAction,dif_pos hq]
      have hgA : (treeGraft p.1 p.2 hp.2.2.2.2.2).val.leaves ⊆ A :=
        Finset.union_subset hp.2.2.2.1 hp.2.2.2.2.1
      have hgB : (treeGraft q.1 q.2 hq.2.2.2.2.2).val.leaves ⊆ B :=
        Finset.union_subset hq.2.2.2.1 hq.2.2.2.2.1
      have hAq1 := disjoint_fibres_tree_ne hAB _ q.1 hgA hq.2.2.2.1
      have hAq2 := disjoint_fibres_tree_ne hAB _ q.2 hgA hq.2.2.2.2.1
      have hBp1 := disjoint_fibres_tree_ne hAB.symm _ p.1 hgB hp.2.2.2.1
      have hBp2 := disjoint_fibres_tree_ne hAB.symm _ p.2 hgB hp.2.2.2.2.1
      ext t
      simp only [mergeForest,Finset.mem_insert,Finset.mem_erase]
      constructor <;> intro h <;> rcases h with h | h
      · subst t
        exact Or.inr ⟨hBp2,hBp1,Or.inl rfl⟩
      · rcases h.2.2 with htg | htf
        · exact Or.inl htg
        · exact Or.inr ⟨htf.1,htf.2.1,Or.inr ⟨h.1,h.2.1,htf.2.2⟩⟩
      · subst t
        exact Or.inr ⟨hAq2,hAq1,Or.inl rfl⟩
      · rcases h.2.2 with htg | htf
        · exact Or.inl htg
        · exact Or.inr ⟨htf.1,htf.2.1,Or.inr ⟨h.1,h.2.1,htf.2.2⟩⟩
    · have hq' : ¬ LegalPair (pairAction F A p) B q :=
        fun h => hq ((legalPair_other_fibre F hAB p q).mp h)
      simp only [pairAction,dif_neg hq',dif_neg hq]
  · have hp' : ¬ LegalPair (pairAction F B q) A p :=
      fun h => hp ((legalPair_other_fibre F hAB.symm q p).mp h)
    simp only [pairAction,dif_neg hp',dif_neg hp]

/-- Padding makes the uniformization carrier nonempty even when Copy is empty.
Its fixed rate divided by the choice cardinality is exactly one half. -/
abbrev PaddedChoice (Copy : Type*) [DecidableEq Copy] :=
  Option (WellLabelledTree Copy × WellLabelledTree Copy)

noncomputable def paddedAction (F : Forest Copy) (A : Finset Copy) :
    PaddedChoice Copy → Forest Copy
  | none => F
  | some p => pairAction F A p

noncomputable def cladeStep (A : Finset Copy) (F : Forest Copy) : PMF (Forest Copy) :=
  (PMF.uniformOfFintype (PaddedChoice Copy)).map (paddedAction F A)

lemma paddedAction_disjoint_commute (F : Forest Copy) {A B : Finset Copy}
    (hAB : Disjoint A B) (p q : PaddedChoice Copy) :
    paddedAction (paddedAction F A p) B q = paddedAction (paddedAction F B q) A p := by
  cases p with
  | none => rfl
  | some p =>
      cases q with
      | none => rfl
      | some q => exact pairAction_disjoint_commute F hAB p q

lemma cladeStep_disjoint_commute (F : Forest Copy) {A B : Finset Copy}
    (hAB : Disjoint A B) :
    (cladeStep A F).bind (cladeStep B) = (cladeStep B F).bind (cladeStep A) := by
  simp only [cladeStep,PMF.bind_map,Function.comp_def,PMF.map]
  rw [PMF.bind_comm]
  congr 1
  funext q
  congr 1
  funext p
  exact congrArg PMF.pure (paddedAction_disjoint_commute F hAB p q)

noncomputable def uniformizationRate : ℝ≥0 :=
  (Fintype.card (PaddedChoice Copy) : ℝ≥0) / 2

lemma uniformizationRate_positive : 0 < uniformizationRate (Copy := Copy) := by
  unfold uniformizationRate
  exact div_pos (by exact_mod_cast Fintype.card_pos) (by norm_num)

lemma ordered_pair_intensity :
    (uniformizationRate (Copy := Copy) : ℝ) /
      (Fintype.card (PaddedChoice Copy) : ℝ) = 1 / 2 := by
  have hc : (Fintype.card (PaddedChoice Copy) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos (α := PaddedChoice Copy)))
  simp only [uniformizationRate,NNReal.coe_div,NNReal.coe_natCast,NNReal.coe_ofNat]
  field_simp

noncomputable def cladeIteration (A : Finset Copy) :
    Nat → Forest Copy → PMF (Forest Copy)
  | 0,F => PMF.pure F
  | n+1,F => (cladeStep A F).bind (cladeIteration A n)

/-- Independent ordinary unit-pair-rate population of duration/exposure t. -/
noncomputable def cladeKernel (A : Finset Copy) (t : ℝ≥0)
    (F : Forest Copy) : PMF (Forest Copy) :=
  (countPMF (uniformizationRate (Copy := Copy) * t)).bind
    (fun n => cladeIteration A n F)

lemma cladeStep_partition (A : Finset Copy) (F : Forest Copy) (hF : Partition F)
    {G : Forest Copy} (hG : G ∈ (cladeStep A F).support) : Partition G := by
  obtain ⟨p,_,hp⟩ := (PMF.mem_support_map_iff _ _ _).mp hG
  subst G
  cases p with
  | none => exact hF
  | some p => exact pairAction_partition F hF A p

lemma cladeIteration_partition (A : Finset Copy) (n : Nat)
    (F : Forest Copy) (hF : Partition F) {G : Forest Copy}
    (hG : G ∈ (cladeIteration A n F).support) : Partition G := by
  induction n generalizing F with
  | zero =>
      have h : G = F := by simpa only [cladeIteration,PMF.mem_support_pure_iff] using hG
      simpa only [h] using hF
  | succ n ih =>
      obtain ⟨M,hM,hG⟩ := (PMF.mem_support_bind_iff _ _ _).mp hG
      exact ih M (cladeStep_partition A F hF hM) hG

lemma cladeKernel_partition (A : Finset Copy) (t : ℝ≥0)
    (F : Forest Copy) (hF : Partition F) {G : Forest Copy}
    (hG : G ∈ (cladeKernel A t F).support) : Partition G := by
  obtain ⟨n,_,hG⟩ := (PMF.mem_support_bind_iff _ _ _).mp hG
  exact cladeIteration_partition A n F hF hG

noncomputable def cladeTransition (A : Finset Copy) :
    Matrix (Forest Copy) (Forest Copy) ℝ := fun F G => (cladeStep A F G).toReal

noncomputable def cladeGenerator (A : Finset Copy) :
    Matrix (Forest Copy) (Forest Copy) ℝ :=
  (uniformizationRate (Copy := Copy) : ℝ) • (cladeTransition A - 1)

lemma cladeTransition_uniform (A : Finset Copy) (F G : Forest Copy) :
    cladeTransition A F G =
      (Fintype.card (PaddedChoice Copy) : ℝ)⁻¹ *
        ∑ p : PaddedChoice Copy, if paddedAction F A p = G then 1 else 0 := by
  rw [cladeTransition,cladeStep,PMF.map,bind_probability_real,tsum_fintype]
  simp only [Function.comp_apply,PMF.uniformOfFintype_apply,
    ENNReal.toReal_inv,ENNReal.toReal_natCast,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : paddedAction F A p = G
  · simp [PMF.pure_apply,h]
  · simp [PMF.pure_apply,h,Ne.symm h]

/-- The padded PMF has exactly the Kingman ordered-pair generator. Self loops
cancel and each legal ordered graft contributes one half, with no quotient
identification or omitted second orientation. -/
lemma cladeGenerator_apply (A : Finset Copy) (F G : Forest Copy) :
    cladeGenerator A F G =
      (1 / 2 : ℝ) * ∑ p : WellLabelledTree Copy × WellLabelledTree Copy,
        if h : LegalPair F A p then
          (if mergeForest F p.1 p.2 h.2.2.2.2.2 = G then 1 else 0) -
            (if F = G then 1 else 0)
        else 0 := by
  have hc : (Fintype.card (PaddedChoice Copy) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Fintype.card_pos (α := PaddedChoice Copy)))
  have hdelta : cladeGenerator A F G = (1 / 2 : ℝ) *
      ∑ p : PaddedChoice Copy,
        ((if paddedAction F A p = G then 1 else 0) - (if F = G then 1 else 0)) := by
    rw [cladeGenerator,Matrix.smul_apply,Matrix.sub_apply,Matrix.one_apply,
      cladeTransition_uniform]
    simp only [smul_eq_mul,uniformizationRate,NNReal.coe_div,NNReal.coe_natCast,
      NNReal.coe_ofNat,Finset.sum_sub_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
    field_simp [hc]
    <;> ring
  rw [hdelta,Fintype.sum_option]
  simp only [paddedAction,sub_self,zero_add]
  congr 1
  apply Finset.sum_congr rfl
  intro p _
  by_cases h : LegalPair F A p
  · simp only [pairAction,dif_pos h]
  · simp only [pairAction,dif_neg h,sub_self]

lemma cladeIteration_probability (A : Finset Copy) (n : Nat) (F G : Forest Copy) :
    (cladeIteration A n F G).toReal = (cladeTransition A ^ n) F G := by
  induction n generalizing F with
  | zero =>
      simp only [cladeIteration,pow_zero,PMF.pure_apply,Matrix.one_apply]
      by_cases h : G = F
      · simp [h]
      · simp [h,Ne.symm h]
  | succ n ih =>
      rw [cladeIteration,bind_probability_real,tsum_fintype,pow_succ',Matrix.mul_apply]
      simp_rw [ih]
      rfl

/-- Reuses the accepted generic Poisson/exponential calculation; the matrix here
is the independently constructed ordinary forest transition, not a source alias. -/
lemma cladeKernel_exponential (A : Finset Copy) (t : ℝ≥0) (F G : Forest Copy) :
    (cladeKernel A t F G).toReal = (exp ((t : ℝ) • cladeGenerator A)) F G := by
  rw [cladeKernel,bind_probability_real]
  simp_rw [countPMF_real,cladeIteration_probability]
  rw [poisson_matrix_entry]
  apply congrArg (fun M : Matrix (Forest Copy) (Forest Copy) ℝ => (exp M) F G)
  simp only [cladeGenerator,smul_smul,NNReal.coe_mul]
  congr 1
  exact mul_comm _ _

lemma cladeKernel_zero (A : Finset Copy) (F : Forest Copy) :
    cladeKernel A 0 F = PMF.pure F := by
  apply PMF.ext
  intro G
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [cladeKernel_exponential]
  simp only [NNReal.coe_zero,zero_smul,exp_zero,Matrix.one_apply,PMF.pure_apply]
  by_cases h : G = F
  · simp [h]
  · simp [h,Ne.symm h]

/-- Unary-chain weights may add only AFTER the source transport identifies the
same independent clade carrier. This theorem itself concerns that concrete kernel. -/
lemma cladeKernel_add (A : Finset Copy) (t u : ℝ≥0) (F : Forest Copy) :
    cladeKernel A (t+u) F =
      (cladeKernel A t F).bind (cladeKernel A u) := by
  apply PMF.ext
  intro G
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [bind_probability_real,tsum_fintype]
  simp_rw [cladeKernel_exponential]
  change (exp (((t+u : ℝ≥0) : ℝ) • cladeGenerator A)) F G =
    (exp ((t : ℝ) • cladeGenerator A) * exp ((u : ℝ) • cladeGenerator A)) F G
  rw [NNReal.coe_add,add_smul,NormedSpace.exp_add_of_commute
    ((Commute.refl (cladeGenerator A)).smul_left (t : ℝ) |>.smul_right (u : ℝ))]

lemma cladeTransition_disjoint_commute {A B : Finset Copy} (hAB : Disjoint A B) :
    Commute (cladeTransition A) (cladeTransition B) := by
  ext F G
  calc
    (cladeTransition A * cladeTransition B) F G =
        (((cladeStep A F).bind (cladeStep B)) G).toReal := by
      rw [bind_probability_real,tsum_fintype,Matrix.mul_apply]
      rfl
    _ = (((cladeStep B F).bind (cladeStep A)) G).toReal :=
      congrArg (fun p : PMF (Forest Copy) => (p G).toReal)
        (cladeStep_disjoint_commute F hAB)
    _ = (cladeTransition B * cladeTransition A) F G := by
      rw [bind_probability_real,tsum_fintype,Matrix.mul_apply]
      rfl

lemma cladeGenerator_disjoint_commute {A B : Finset Copy} (hAB : Disjoint A B) :
    Commute (cladeGenerator A) (cladeGenerator B) := by
  have h := cladeTransition_disjoint_commute hAB
  have hsub : Commute (cladeTransition A - 1) (cladeTransition B - 1) :=
    (h.sub_left (Commute.one_left _)).sub_right (Commute.one_right _)
  exact (hsub.smul_left (uniformizationRate (Copy := Copy) : ℝ)).smul_right
    (uniformizationRate (Copy := Copy) : ℝ)

/-- Separate species branches commute before their parent pooling step. This
is proved for the actual independently constructed clade PMFs. -/
lemma cladeKernel_disjoint_commute {A B : Finset Copy} (hAB : Disjoint A B)
    (t u : ℝ≥0) (F : Forest Copy) :
    (cladeKernel A t F).bind (cladeKernel B u) =
      (cladeKernel B u F).bind (cladeKernel A t) := by
  apply PMF.ext
  intro G
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [bind_probability_real,bind_probability_real,tsum_fintype,tsum_fintype]
  simp_rw [cladeKernel_exponential]
  change (exp ((t : ℝ) • cladeGenerator A) * exp ((u : ℝ) • cladeGenerator B)) F G =
    (exp ((u : ℝ) • cladeGenerator B) * exp ((t : ℝ) • cladeGenerator A)) F G
  have h := ((cladeGenerator_disjoint_commute hAB).smul_left (t : ℝ)).smul_right (u : ℝ)
  exact congrArg (fun M : Matrix (Forest Copy) (Forest Copy) ℝ => M F G)
    h.exp_left.exp_right.eq

noncomputable def rootPairs (F : Forest Copy) :
    Finset (WellLabelledTree Copy × WellLabelledTree Copy) :=
  Finset.univ.filter (LegalPair F Finset.univ)

/-- At a terminal forest the root step is pure. Otherwise it chooses the actual
ordered live pairs, retaining both orientations until unranked observation. -/
noncomputable def rootStep (F : Forest Copy) : PMF (Forest Copy) :=
  if h : (rootPairs F).Nonempty then
    (PMF.uniformOfFinset (rootPairs F) h).map (pairAction F Finset.univ)
  else PMF.pure F

lemma rootPairs_eq_offDiag (F : Forest Copy) (hF : Partition F) :
    rootPairs F = F.offDiag := by
  ext p
  simp only [rootPairs,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_offDiag]
  constructor
  · intro h; exact ⟨h.1,h.2.1,h.2.2.1⟩
  · rintro ⟨ha,hb,hne⟩
    exact ⟨ha,hb,hne,Finset.subset_univ _,Finset.subset_univ _,hF.1 _ ha _ hb hne⟩

lemma rootPairs_empty_iff (F : Forest Copy) (hF : Partition F) :
    ¬ (rootPairs F).Nonempty ↔ F.card ≤ 1 := by
  rw [rootPairs_eq_offDiag F hF,Finset.card_le_one]
  constructor
  · intro h a ha b hb
    by_contra hne
    exact h ⟨(a,b),Finset.mem_offDiag.mpr ⟨ha,hb,hne⟩⟩
  · intro h ⟨⟨a,b⟩,hp⟩
    obtain ⟨ha,hb,hne⟩ := Finset.mem_offDiag.mp hp
    exact hne (h a ha b hb)

lemma rootStep_support (F : Forest Copy) (hF : Partition F) {G : Forest Copy}
    (hG : G ∈ (rootStep F).support) :
    Partition G ∧ ((G = F ∧ F.card ≤ 1) ∨ G.card + 1 = F.card) := by
  unfold rootStep at hG
  split_ifs at hG with h
  · obtain ⟨p,hp,rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hG
    have hp' := (PMF.mem_support_uniformOfFinset_iff _ _).mp hp
    have hlegal : LegalPair F Finset.univ p := (Finset.mem_filter.mp hp').2
    refine ⟨pairAction_partition F hF _ p,Or.inr ?_⟩
    rw [pairAction,dif_pos hlegal]
    exact mergeForest_card F hF p.1 p.2 hlegal.1 hlegal.2.1
      hlegal.2.2.1 hlegal.2.2.2.2.2
  · have he : G = F := (PMF.mem_support_pure_iff _ _).mp hG
    subst G
    exact ⟨hF,Or.inl ⟨rfl,(rootPairs_empty_iff F hF).mp h⟩⟩

noncomputable def rootIteration : Nat → Forest Copy → PMF (Forest Copy)
  | 0,F => PMF.pure F
  | n+1,F => (rootStep F).bind (rootIteration n)

noncomputable def ordinaryCompletion (F : Forest Copy) : PMF (Forest Copy) :=
  rootIteration (Fintype.card Copy) F

lemma rootIteration_partition (n : Nat) (F : Forest Copy) (hF : Partition F)
    {G : Forest Copy} (hG : G ∈ (rootIteration n F).support) : Partition G := by
  induction n generalizing F with
  | zero =>
      have he : G = F := by simpa only [rootIteration,PMF.mem_support_pure_iff] using hG
      simpa only [he] using hF
  | succ n ih =>
      obtain ⟨M,hM,hG⟩ := (PMF.mem_support_bind_iff _ _ _).mp hG
      exact ih M (rootStep_support F hF hM).1 hG

lemma rootIteration_terminal (n : Nat) (F : Forest Copy) (hF : Partition F)
    (hcard : F.card ≤ n+1) {G : Forest Copy}
    (hG : G ∈ (rootIteration n F).support) : G.card ≤ 1 := by
  induction n generalizing F with
  | zero =>
      have he : G = F := by simpa only [rootIteration,PMF.mem_support_pure_iff] using hG
      simpa only [he] using hcard
  | succ n ih =>
      obtain ⟨M,hM,hG⟩ := (PMF.mem_support_bind_iff _ _ _).mp hG
      obtain ⟨hMP,hMc⟩ := rootStep_support F hF hM
      apply ih M hMP _ hG
      rcases hMc with ⟨rfl,hsmall⟩ | hdrop <;> omega

lemma ordinaryCompletion_terminal (F : Forest Copy) (hF : Partition F)
    {G : Forest Copy} (hG : G ∈ (ordinaryCompletion F).support) :
    Partition G ∧ G.card ≤ 1 := by
  exact ⟨rootIteration_partition _ F hF hG,
    rootIteration_terminal _ F hF (by have := partition_card_le F hF; omega) hG⟩

noncomputable def forestObservation (F : Forest Copy) : Finset (UnrankedTree Copy) :=
  F.image (fun t => toUnranked t.val)

/-- Existing actual source states map to the independent full-genealogy carrier.
No population or register survives in this passive projection. -/
noncomputable def actualForest {V E : Type*} (s : State V E Copy) (hs : Valid s) :
    Forest Copy :=
  s.live.attach.image (fun l => ⟨s.genealogy l.val,hs.wellLabelled l.val l.property⟩)

lemma mem_actualForest {V E : Type*} (s : State V E Copy) (hs : Valid s)
    (t : WellLabelledTree Copy) :
    t ∈ actualForest s hs ↔ ∃ l ∈ s.live, s.genealogy l = t.val := by
  constructor
  · rintro h
    obtain ⟨l,_,hl⟩ := Finset.mem_image.mp h
    exact ⟨l.val,l.property,congrArg Subtype.val hl⟩
  · rintro ⟨l,hl,he⟩
    exact Finset.mem_image.mpr ⟨⟨l,hl⟩,Finset.mem_attach _ _,Subtype.ext he⟩

lemma live_genealogy_injective {V E : Type*} (s : State V E Copy) (hs : Valid s)
    {a b : Copy} (ha : a ∈ s.live) (hb : b ∈ s.live)
    (he : s.genealogy a = s.genealogy b) : a = b := by
  have hmem : a ∈ (s.genealogy a).leaves :=
    (hs.leaf_fiber a ha a).mpr (hs.representative a ha)
  rw [he] at hmem
  exact (hs.representative a ha).symm.trans ((hs.leaf_fiber b hb a).mp hmem)

lemma actualForest_card {V E : Type*} (s : State V E Copy) (hs : Valid s) :
    (actualForest s hs).card = s.live.card := by
  rw [actualForest,Finset.card_image_iff.mpr]
  · exact Finset.card_attach _
  · intro a ha b hb he
    apply Subtype.ext
    exact live_genealogy_injective s hs a.property b.property
      (congrArg Subtype.val he)

/-- Boundary moves and inert register changes are erased only in this proved
full-forest projection, rather than by replacing the original state/register. -/
lemma actualForest_eq_of_live_genealogy {V E V' E' : Type*}
    (s : State V E Copy) (t : State V' E' Copy) (hs : Valid s) (ht : Valid t)
    (hl : s.live = t.live) (hg : ∀ l ∈ s.live, s.genealogy l = t.genealogy l) :
    actualForest s hs = actualForest t ht := by
  ext u
  rw [mem_actualForest,mem_actualForest]
  constructor
  · rintro ⟨l,hm,he⟩
    exact ⟨l,hl ▸ hm,(hg l hm).symm.trans he⟩
  · rintro ⟨l,hm,he⟩
    have hm' : l ∈ s.live := hl.symm ▸ hm
    exact ⟨l,hm',(hg l hm').trans he⟩

/-- Recover a population fibre from complete leaves. This uses Valid's actual
ancestor map and does not designate a representative of an abstract tree. -/
lemma live_tree_in_location_fibre {V E : Type*} [DecidableEq V] [DecidableEq E]
    (s : State V E Copy) (hs : Valid s) {l : Copy} (hl : l ∈ s.live)
    (place : Location V E) :
    (s.genealogy l).leaves ⊆ Finset.univ.filter (fun x => copyLocation s x = place) ↔
      s.location l = place := by
  constructor
  · intro h
    have hll : l ∈ (s.genealogy l).leaves :=
      (hs.leaf_fiber l hl l).mpr (hs.representative l hl)
    have he := (Finset.mem_filter.mp (h hll)).2
    simpa only [copyLocation,hs.representative l hl] using he
  · intro he x hx
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    change s.location (s.ancestor x) = place
    rw [(hs.leaf_fiber l hl x).mp hx]
    exact he

lemma actualForest_location_compatible {V E : Type*}
    (s : State V E Copy) (hs : Valid s) (t : WellLabelledTree Copy)
    (ht : t ∈ actualForest s hs) {x y : Copy}
    (hx : x ∈ t.val.leaves) (hy : y ∈ t.val.leaves) :
    copyLocation s x = copyLocation s y := by
  obtain ⟨l,hl,he⟩ := (mem_actualForest s hs t).mp ht
  have hxl := (hs.leaf_fiber l hl x).mp (by simpa only [he] using hx)
  have hyl := (hs.leaf_fiber l hl y).mp (by simpa only [he] using hy)
  simp only [copyLocation,hxl,hyl]

lemma actualForest_merge {V E : Type*} [Fintype V] [Fintype E] [DecidableEq V]
    (s : State V E Copy) (hs : Valid s) {a b : Copy} (hm : LegalMerge s a b) :
    actualForest (merge s a b) (merge_valid s hs hm) =
      mergeForest (actualForest s hs)
        ⟨s.genealogy a,hs.wellLabelled a hm.first_live⟩
        ⟨s.genealogy b,hs.wellLabelled b hm.second_live⟩
        (distinct_live_genealogies_disjoint s hs hm.first_live hm.second_live hm.different) := by
  let ta : WellLabelledTree Copy := ⟨s.genealogy a,hs.wellLabelled a hm.first_live⟩
  let tb : WellLabelledTree Copy := ⟨s.genealogy b,hs.wellLabelled b hm.second_live⟩
  let hd := distinct_live_genealogies_disjoint s hs hm.first_live hm.second_live hm.different
  change actualForest (merge s a b) _ = mergeForest (actualForest s hs) ta tb hd
  ext u
  rw [mem_actualForest]
  change (∃ l ∈ s.live.erase b, (merge s a b).genealogy l = u.val) ↔
    u ∈ insert (treeGraft ta tb hd) (((actualForest s hs).erase ta).erase tb)
  constructor
  · rintro ⟨l,hl,hg⟩
    obtain ⟨hlb,hll⟩ := Finset.mem_erase.mp hl
    by_cases hla : l = a
    · subst l
      apply Finset.mem_insert.mpr
      left
      apply Subtype.ext
      simpa only [merge,if_true,treeGraft,ta,tb] using hg.symm
    · have hgu : s.genealogy l = u.val := by
        simpa only [merge,if_neg hla] using hg
      apply Finset.mem_insert_of_mem
      apply Finset.mem_erase.mpr
      constructor
      · intro he
        have hg' : s.genealogy l = s.genealogy b :=
          hgu.trans (congrArg Subtype.val he)
        exact hlb (live_genealogy_injective s hs hll hm.second_live hg')
      · apply Finset.mem_erase.mpr
        constructor
        · intro he
          have hg' : s.genealogy l = s.genealogy a :=
            hgu.trans (congrArg Subtype.val he)
          exact hla (live_genealogy_injective s hs hll hm.first_live hg')
        · exact (mem_actualForest s hs u).mpr ⟨l,hll,hgu⟩
  · intro hu
    rcases Finset.mem_insert.mp hu with hu | hu
    · subst u
      refine ⟨a,Finset.mem_erase.mpr ⟨hm.different,hm.first_live⟩,?_⟩
      simp only [merge,if_true,treeGraft,ta,tb]
    · obtain ⟨hub,hu'⟩ := Finset.mem_erase.mp hu
      obtain ⟨hua,huF⟩ := Finset.mem_erase.mp hu'
      obtain ⟨l,hl,hg⟩ := (mem_actualForest s hs u).mp huF
      have hlb : l ≠ b := by
        intro he; subst l; exact hub (Subtype.ext hg.symm)
      have hla : l ≠ a := by
        intro he; subst l; exact hua (Subtype.ext hg.symm)
      exact ⟨l,Finset.mem_erase.mpr ⟨hlb,hl⟩,by simpa only [merge,if_neg hla] using hg⟩

/-- Total map solely for reuse of the accepted ordered off-diagonal bijection.
The fallback is never used on an actual population root. -/
noncomputable def liveTreeOrLeaf {V E : Type*} (s : State V E Copy) (hs : Valid s)
    (l : Copy) : WellLabelledTree Copy :=
  if h : l ∈ s.live then ⟨s.genealogy l,hs.wellLabelled l h⟩ else treeLeaf l

lemma liveTreeOrLeaf_val {V E : Type*} (s : State V E Copy) (hs : Valid s)
    {l : Copy} (hl : l ∈ s.live) : (liveTreeOrLeaf s hs l).val = s.genealogy l := by
  simp only [liveTreeOrLeaf,dif_pos hl]

lemma liveTreeOrLeaf_injective_on {V E : Type*} (s : State V E Copy) (hs : Valid s) :
    ∀ a ∈ s.live, ∀ b ∈ s.live, liveTreeOrLeaf s hs a = liveTreeOrLeaf s hs b → a = b := by
  intro a ha b hb he
  apply live_genealogy_injective s hs ha hb
  have h := congrArg Subtype.val he
  simpa only [liveTreeOrLeaf_val s hs ha,liveTreeOrLeaf_val s hs hb] using h

lemma image_populationRoots {V E : Type*} [DecidableEq V] [DecidableEq E]
    (s : State V E Copy) (hs : Valid s) (place : Location V E) :
    (populationRoots s place).image (liveTreeOrLeaf s hs) =
      (actualForest s hs).filter (fun t =>
        t.val.leaves ⊆ Finset.univ.filter (fun x => copyLocation s x = place)) := by
  ext t
  constructor
  · rintro h
    obtain ⟨l,hl,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨hll,hlp⟩ := Finset.mem_filter.mp hl
    apply Finset.mem_filter.mpr
    constructor
    · exact (mem_actualForest s hs _).mpr ⟨l,hll,(liveTreeOrLeaf_val s hs hll).symm⟩
    · rw [liveTreeOrLeaf_val s hs hll]
      exact (live_tree_in_location_fibre s hs hll place).mpr hlp
  · intro ht
    obtain ⟨htF,htp⟩ := Finset.mem_filter.mp ht
    obtain ⟨l,hl,hg⟩ := (mem_actualForest s hs t).mp htF
    apply Finset.mem_image.mpr
    refine ⟨l,Finset.mem_filter.mpr ⟨hl,?_⟩,?_⟩
    · apply (live_tree_in_location_fibre s hs hl place).mp
      simpa only [hg] using htp
    · apply Subtype.ext
      exact (liveTreeOrLeaf_val s hs hl).trans hg

/-- Reuses the exact accepted off-diagonal pair bijection. Both ordered
orientations are retained, even after original survivor labels are erased. -/
lemma image_population_pairs {V E : Type*} [DecidableEq V] [DecidableEq E]
    (s : State V E Copy) (hs : Valid s) (place : Location V E) :
    (populationRoots s place).offDiag.image (pairMap (liveTreeOrLeaf s hs)) =
      ((actualForest s hs).filter (fun t =>
        t.val.leaves ⊆ Finset.univ.filter (fun x => copyLocation s x = place))).offDiag := by
  rw [image_offDiag_eq]
  · rw [image_populationRoots]
  · intro a ha b hb
    exact liveTreeOrLeaf_injective_on s hs a (populationRoots_subset_live s place ha)
      b (populationRoots_subset_live s place hb)

lemma actualForest_partition {V E : Type*} (s : State V E Copy) (hs : Valid s) :
    Partition (actualForest s hs) := by
  constructor
  · intro t ht u hu htu
    obtain ⟨l,hl,htl⟩ := (mem_actualForest s hs t).mp ht
    obtain ⟨m,hm,hum⟩ := (mem_actualForest s hs u).mp hu
    apply Finset.disjoint_left.mpr
    intro x hxt hxu
    have hxl := (hs.leaf_fiber l hl x).mp (by simpa only [htl] using hxt)
    have hxm := (hs.leaf_fiber m hm x).mp (by simpa only [hum] using hxu)
    have hlm : l = m := hxl.symm.trans hxm
    apply htu
    apply Subtype.ext
    exact htl.symm.trans ((congrArg s.genealogy hlm).trans hum)
  · intro x
    let l := s.ancestor x
    let t : WellLabelledTree Copy := ⟨s.genealogy l,hs.wellLabelled l (hs.ancestor_live x)⟩
    refine ⟨t,(mem_actualForest s hs t).mpr ⟨l,hs.ancestor_live x,rfl⟩,?_⟩
    exact (hs.leaf_fiber l (hs.ancestor_live x) x).mpr rfl

lemma actualForest_observation {V E : Type*} (s : State V E Copy) (hs : Valid s) :
    forestObservation (actualForest s hs) = sourceUnrankedForest s Finset.univ := by
  ext q
  rw [forestObservation,Finset.mem_image]
  change (∃ t, t ∈ actualForest s hs ∧ toUnranked t.val = q) ↔ _
  rw [sourceUnrankedForest,mem_unrankedForest]
  constructor
  · rintro ⟨t,ht,hq⟩
    obtain ⟨l,hl,he⟩ := (mem_actualForest s hs t).mp ht
    refine ⟨l,t.val,?_,hq⟩
    simp only [selectedView,selectedGenealogy,Finset.mem_univ,if_true,
      hs.representative l hl,full_prune,he]
  · rintro ⟨x,t,ht,hq⟩
    have he : s.genealogy (s.ancestor x) = t := by
      simpa only [selectedView,selectedGenealogy,Finset.mem_univ,if_true,
        full_prune,Option.some.injEq] using ht
    let u : WellLabelledTree Copy :=
      ⟨s.genealogy (s.ancestor x),hs.wellLabelled _ (hs.ancestor_live x)⟩
    exact ⟨u,(mem_actualForest s hs u).mpr ⟨_,hs.ancestor_live x,rfl⟩,
      (congrArg toUnranked he).trans hq⟩

end Forest

section Evaluation
variable {X Copy : Type*} [Fintype X] [DecidableEq X]
variable [Fintype Copy] [DecidableEq Copy]

/-- The independent evaluator receives only taxon clades and ordinary pair
exposures. Source realization/laminarity will be proved for weightedNormalize;
no source-law equality is a field of this representation. -/
abbrev CladeWeights (X : Type*) [DecidableEq X] := Finset X → ℝ≥0

noncomputable def cladeCopySet (sample : Copy → X) (A : Finset X) : Finset Copy :=
  Finset.univ.filter (fun x => sample x ∈ A)

/-- Fixed inclusion-compatible order. Disjoint-clade commutation supplies its
later independence from the arbitrary initial finite enumeration. -/
noncomputable def cladeOrder (X : Type*) [Fintype X] [DecidableEq X] : List (Finset X) :=
  (Finset.univ : Finset (Finset X)).toList.mergeSort (fun A B => A.card ≤ B.card)

noncomputable def ordinaryCladeProgram (w : CladeWeights X) (sample : Copy → X) :
    List (Finset X) → Forest Copy → PMF (Forest Copy)
  | [],F => PMF.pure F
  | A::as,F => (cladeKernel (cladeCopySet sample A) (w A) F).bind
      (ordinaryCladeProgram w sample as)

noncomputable def ordinaryCompletedTreeLaw (w : CladeWeights X) (sample : Copy → X) :
    PMF (Finset (UnrankedTree Copy)) :=
  (((ordinaryCladeProgram w sample (cladeOrder X) initialForest).bind
    ordinaryCompletion).map forestObservation)

end Evaluation
section Weights
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E] [DecidableEq X]

/-- All ORIGINAL taxa carried below an original selected edge. This has no
sample-allocation argument; an unselected/unused edge has empty route fibre. -/
noncomputable def edgeTaxa (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (coin : CommonSeed N) (e : E) : Finset X :=
  Finset.univ.filter (fun x => e ∈ (commonRoutes N C H coin).edges x)

lemma mem_edgeTaxa (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (coin : CommonSeed N) (e : E) (x : X) :
    x ∈ edgeTaxa N C H coin e ↔ e ∈ (commonRoutes N C H coin).edges x := by
  simp only [edgeTaxa,Finset.mem_filter,Finset.mem_univ,true_and]

lemma edgeTaxa_selected_descendants (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (coin : CommonSeed N)
    (e : (commonSwitching N H coin).Edge) (x : X) :
    x ∈ edgeTaxa N C H coin e.val ↔
      (commonSwitching N H coin).graph.DReach (N.graph.target e.val) (N.leaf x) := by
  rw [mem_edgeTaxa]
  exact common_route_edge_iff_selected_descendant N C H coin x e

noncomputable def edgeExposure (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (e : E) : ℝ≥0 :=
  ⟨r.edge e * (C.age (N.graph.source e) - C.age (N.graph.target e)),
    mul_nonneg (r.edge_pos e).le (sub_nonneg.mpr (C.edge_older e).le)⟩

lemma edgeExposure_positive (N : RootedBinary V E X) (C : Calendar N.graph)
    (r : PositivePairRates E) (e : E) : 0 < edgeExposure N C r e := by
  exact mul_pos (r.edge_pos e) (sub_pos.mpr (C.edge_older e))

/-- Concrete clade-coordinate normalization. Empty descendant edges are pruned;
repeated proper clades sum their edge exposures. The full-taxon stem is reserved
for completion absorption. Identification with the actual pruned topology and
full source-law transport remain theorem obligations, not fields here. -/
noncomputable def weightedNormalize (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E)
    (coin : CommonSeed N) : CladeWeights X := fun A =>
  if A = ∅ ∨ A = Finset.univ then 0 else
    ∑ e : E, if edgeTaxa N C H coin e = A then edgeExposure N C r e else 0

@[simp] lemma weightedNormalize_empty (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (coin : CommonSeed N) :
    weightedNormalize N C H r coin ∅ = 0 := by simp [weightedNormalize]

@[simp] lemma weightedNormalize_univ (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (coin : CommonSeed N) :
    weightedNormalize N C H r coin Finset.univ = 0 := by simp [weightedNormalize]

lemma weightedNormalize_pos_iff_edge (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (r : PositivePairRates E) (coin : CommonSeed N)
    (A : Finset X) (ha : A ≠ ∅) (hu : A ≠ Finset.univ) :
    0 < weightedNormalize N C H r coin A ↔ ∃ e : E, edgeTaxa N C H coin e = A := by
  rw [weightedNormalize,if_neg (by tauto),
    Finset.sum_pos_iff_of_nonneg (fun _ _ => zero_le _)]
  constructor
  · rintro ⟨e,_,he⟩
    by_cases h : edgeTaxa N C H coin e = A
    · exact ⟨e,h⟩
    · simp only [if_neg h,lt_self_iff_false] at he
  · rintro ⟨e,he⟩
    exact ⟨e,Finset.mem_univ _,by simpa only [if_pos he] using edgeExposure_positive N C r e⟩

lemma edgeTaxa_eq_sampledDescendants (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (coin : CommonSeed N)
    (e : (commonSwitching N H coin).Edge) :
    edgeTaxa N C H coin e.val =
      sampledDescendants N (commonSwitching N H coin) Finset.univ (N.graph.target e.val) := by
  ext x
  rw [edgeTaxa_selected_descendants]
  simp only [sampledDescendants,Finset.mem_filter,Finset.mem_univ,true_and]

/-- Exact support of the concrete weight coordinates equals the actual selected
proper-clade set. This uses every original taxon, with no copy allocation and
no supplied topology equality. Empty twigs disappear and unary repeats share a
coordinate. The strict source edge/calendar premises make every present one positive. -/
lemma weightedNormalize_pos_iff_selectedCluster (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (r : PositivePairRates E)
    (coin : CommonSeed N) (A : Finset X) (ha : A ≠ ∅) (hu : A ≠ Finset.univ) :
    0 < weightedNormalize N C H r coin A ↔
      A ∈ selectedClusters N (commonSwitching N H coin) Finset.univ := by
  rw [weightedNormalize_pos_iff_edge N C H r coin A ha hu,mem_selectedClusters]
  constructor
  · rintro ⟨e,he⟩
    have hn : (edgeTaxa N C H coin e).Nonempty := he.symm ▸ Finset.nonempty_iff_ne_empty.mpr ha
    obtain ⟨x,hx⟩ := hn
    have hkeep := common_route_kept N C H coin x ((mem_edgeTaxa N C H coin e x).mp hx)
    let f : (commonSwitching N H coin).Edge := ⟨e,hkeep⟩
    exact ⟨Finset.nonempty_iff_ne_empty.mpr ha,N.graph.target e,
      (edgeTaxa_eq_sampledDescendants N C H coin f).symm.trans he⟩
  · rintro ⟨_,v,hv⟩
    have hvr : v ≠ N.root := by
      intro h; subst v
      rw [sampledDescendants_root] at hv
      exact hu hv.symm
    obtain ⟨e,he⟩ := (commonSwitching N H coin).selected_parent hvr
    refine ⟨e.val,?_⟩
    rw [edgeTaxa_eq_sampledDescendants]
    change N.graph.target e.val = v at he
    rw [he]
    exact hv

/-- The concrete weight support is the proper-clade support of the accepted
actual pruning/unary evaluator, rather than an independent per-clade union. -/
theorem weightedNormalize_actual_pruned_clades (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (r : PositivePairRates E)
    (coin : CommonSeed N) {T : Genealogy X}
    (hT : PrunedAt N (commonSwitching N H coin) Finset.univ N.root (some T))
    (A : Finset X) (ha : A ≠ ∅) (hu : A ≠ Finset.univ) :
    0 < weightedNormalize N C H r coin A ↔ A ∈ treeClusters T := by
  rw [actual_pruned_root_clusters N (commonSwitching N H coin) Finset.univ hT]
  exact weightedNormalize_pos_iff_selectedCluster N C H r coin A ha hu

/-- Routing selector after the ORIGINAL global mask. The source's stored
originalRegister coin remains unchanged in the intended transport theorem. -/
noncomputable def overrideBank (N : RootedBinary V E X)
    (mask : OriginalMask N) (coin : CommonSeed N) : CommonSeed N :=
  fun h => (mask h).getD (coin h)

end Weights

end DotG4.WeightedOrdinaryTreeLaw
