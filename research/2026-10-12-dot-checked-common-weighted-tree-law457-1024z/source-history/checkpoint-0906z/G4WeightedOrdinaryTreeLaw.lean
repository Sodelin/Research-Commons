import UnifiedLean.Source.FiniteGenealogyEncoding
import SourceForestKingmanProjection
import UnifiedLean.Source.SourcePoissonExponential
import UnifiedLean.Source.SourceCompletedUnrankedTree
import G5CommonSwitchingQuartetWitness
import G5OriginalProgramSurvival
import G6GuardedBinErasure
import ActualStoredRegister
import G1ActualDisplayedTreeFamily
import G7OriginalEdgeOperators
import G7AncestralPolynomialKernel
import UnifiedLean.Source.SourceCompletionHarmonic
import UnifiedLean.Source.MatrixProjectionExponential
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
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open GProgram.G7.OriginalEdgeOperators
open GProgram.G7.AncestralPolynomialKernel
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.G6.AncestralRateFree
open UnifiedLean.Source.SourceEmbeddedJumpLaw
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
      have hleft : pairAction (pairAction F A p) B q =
          mergeForest (pairAction F A p) q.1 q.2 hq'.2.2.2.2.2 := dif_pos hq'
      have hright : pairAction (pairAction F B q) A p =
          mergeForest (pairAction F B q) p.1 p.2 hp'.2.2.2.2.2 := dif_pos hp'
      have hinnerA : pairAction F A p = mergeForest F p.1 p.2 hp.2.2.2.2.2 := dif_pos hp
      have hinnerB : pairAction F B q = mergeForest F q.1 q.2 hq.2.2.2.2.2 := dif_pos hq
      rw [hleft,hright,hinnerA,hinnerB]
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

noncomputable def activeTrees (F : Forest Copy) (A : Finset Copy) : Forest Copy :=
  F.filter (fun t => t.val.leaves ⊆ A)

lemma legalPair_iff_mem_active_offDiag (F : Forest Copy) (hF : Partition F)
    (A : Finset Copy) (p : WellLabelledTree Copy × WellLabelledTree Copy) :
    LegalPair F A p ↔ p ∈ (activeTrees F A).offDiag := by
  simp only [activeTrees,Finset.mem_offDiag,Finset.mem_filter]
  constructor
  · intro h; exact ⟨⟨h.1,h.2.2.2.1⟩,⟨h.2.1,h.2.2.2.2.1⟩,h.2.2.1⟩
  · rintro ⟨⟨ha,haA⟩,⟨hb,hbA⟩,hne⟩
    exact ⟨ha,hb,hne,haA,hbA,hF.1 _ ha _ hb hne⟩

lemma cladeGenerator_active_row (F : Forest Copy) (hF : Partition F)
    (A : Finset Copy) (G : Forest Copy) :
    cladeGenerator A F G = (1 / 2 : ℝ) *
      ∑ p ∈ (activeTrees F A).offDiag,
        ((if pairAction F A p = G then 1 else 0) - (if F = G then 1 else 0)) := by
  let f := fun p : WellLabelledTree Copy × WellLabelledTree Copy =>
    (if pairAction F A p = G then (1 : ℝ) else 0) - (if F = G then 1 else 0)
  have ht : ∀ p : WellLabelledTree Copy × WellLabelledTree Copy,
      (if h : LegalPair F A p then
        (if mergeForest F p.1 p.2 h.2.2.2.2.2 = G then (1 : ℝ) else 0) -
          (if F = G then 1 else 0) else 0) =
      if LegalPair F A p then f p else 0 := by
    intro p
    by_cases h : LegalPair F A p <;> simp only [f,pairAction,h,dif_pos,dif_neg,if_true,if_false]
  rw [cladeGenerator_apply]
  simp_rw [ht]
  rw [← Finset.sum_filter]
  have hset : Finset.univ.filter (LegalPair F A) = (activeTrees F A).offDiag := by
    ext p
    simp only [Finset.mem_filter,Finset.mem_univ,true_and]
    exact legalPair_iff_mem_active_offDiag F hF A p
  rw [hset]

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

/-- Reading the carried genealogy at every original copy gives the same
ordered forest. Repeated reads of a live tree are collapsed only by Finset. -/
lemma actualForest_eq_copy_image {V E : Type*} (s : State V E Copy) (hs : Valid s) :
    actualForest s hs = Finset.univ.image (fun x : Copy =>
      (⟨s.genealogy (s.ancestor x),hs.wellLabelled _ (hs.ancestor_live x)⟩ :
        WellLabelledTree Copy)) := by
  ext t
  constructor
  · intro ht
    obtain ⟨l,hl,he⟩ := (mem_actualForest s hs t).mp ht
    refine Finset.mem_image.mpr ⟨l,Finset.mem_univ _,?_⟩
    apply Subtype.ext
    rw [hs.representative l hl]
    exact he
  · rintro ht
    obtain ⟨x,_,rfl⟩ := Finset.mem_image.mp ht
    exact (mem_actualForest s hs _).mpr ⟨s.ancestor x,hs.ancestor_live x,rfl⟩

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

noncomputable def forestProgram : List (Finset Copy × ℝ≥0) → Forest Copy → PMF (Forest Copy)
  | [],F => PMF.pure F
  | op::ops,F => (cladeKernel op.1 op.2 F).bind (forestProgram ops)

noncomputable def weightedCladeGenerator (op : Finset Copy × ℝ≥0) :
    Matrix (Forest Copy) (Forest Copy) ℝ := (op.2 : ℝ) • cladeGenerator op.1

lemma forestProgram_partition (ops : List (Finset Copy × ℝ≥0))
    (F : Forest Copy) (hF : Partition F) {G : Forest Copy}
    (hG : G ∈ (forestProgram ops F).support) : Partition G := by
  induction ops generalizing F with
  | nil =>
      have he : G = F := by simpa only [forestProgram,PMF.mem_support_pure_iff] using hG
      simpa only [he] using hF
  | cons op ops ih =>
      obtain ⟨M,hM,hG⟩ := (PMF.mem_support_bind_iff _ _ _).mp hG
      exact ih M (cladeKernel_partition op.1 op.2 F hF hM) hG

/-- Finite products of mutually commuting ordinary population kernels give the
exponential of their sum. The exponential identity is the existing generic
algebra theorem; no stochastic factorization is assumed. -/
lemma forestProgram_commuting_probability (ops : List (Finset Copy × ℝ≥0))
    (hcomm : ∀ a ∈ ops, ∀ b ∈ ops,
      Commute (weightedCladeGenerator a) (weightedCladeGenerator b)) (F G : Forest Copy) :
    (forestProgram ops F G).toReal = (exp ((ops.map weightedCladeGenerator).sum)) F G := by
  induction ops generalizing F with
  | nil =>
      simp only [forestProgram,List.map_nil,List.sum_nil,exp_zero,Matrix.one_apply,PMF.pure_apply]
      by_cases h : F = G
      · simp [h]
      · simp [h,Ne.symm h]
  | cons op ops ih =>
      have htail : ∀ a ∈ ops, ∀ b ∈ ops,
          Commute (weightedCladeGenerator a) (weightedCladeGenerator b) := by
        intro a ha b hb
        exact hcomm a (List.mem_cons_of_mem op ha) b (List.mem_cons_of_mem op hb)
      have hc : Commute (weightedCladeGenerator op) ((ops.map weightedCladeGenerator).sum) := by
        apply Commute.list_sum_right
        intro B hB
        obtain ⟨b,hb,rfl⟩ := List.mem_map.mp hB
        exact hcomm op List.mem_cons_self b (List.mem_cons_of_mem op hb)
      rw [forestProgram,bind_probability_real,tsum_fintype]
      simp_rw [ih htail,cladeKernel_exponential]
      rw [List.map_cons,List.sum_cons,NormedSpace.exp_add_of_commute hc]
      rfl

end Forest

section SourceProjection
variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

abbrev ColouredForest (Colour Copy : Type*) [DecidableEq Copy] :=
  Forest Copy × (Copy → Colour)

noncomputable def colourFibre {Colour : Type*} [DecidableEq Colour]
    (f : Copy → Colour) (c : Colour) : Finset Copy :=
  Finset.univ.filter (fun x => f x = c)

lemma colourFibres_disjoint {Colour : Type*} [DecidableEq Colour]
    (f : Copy → Colour) {c d : Colour} (h : c ≠ d) :
    Disjoint (colourFibre f c) (colourFibre f d) := by
  apply Finset.disjoint_left.mpr
  intro x hx hy
  exact h ((Finset.mem_filter.mp hx).2.symm.trans (Finset.mem_filter.mp hy).2)

noncomputable def forestCode (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : Forest Copy := actualForest (state s) s.property.forest

/-- All original zero-time boundary kernels preserve the full ordered forest.
The accepted full selected-genealogy preservation theorem includes supported
current-owner INDEPENDENT pulses, and therefore also forced endpoint pulses. -/
lemma actual_boundary_forest (N : RootedBinary V E X) {sample : Copy → X}
    (op : UnifiedLean.Source.SourceBoundaryKernels.BoundaryOperation N)
    (s d : Code N sample)
    (hd : d ∈ (UnifiedLean.Source.SourceBoundaryKernels.boundaryKernel N op s).support) :
    forestCode N d = forestCode N s := by
  have hg := GProgram.G5.OriginalProgramSurvival.actual_boundary_selected_genealogy
    N Finset.univ op s d hd
  unfold forestCode
  rw [actualForest_eq_copy_image,actualForest_eq_copy_image]
  congr 1
  funext x
  apply Subtype.ext
  have hx := congrFun hg x
  simpa only [selectedView,selectedGenealogy,Finset.mem_univ,if_true,
    full_prune,Option.some.injEq] using hx

/-- The intermediate carrier remembers actual original-copy locations, with
zero-rate node fibres. It does not erase population distinctions prematurely. -/
noncomputable def colourProjection (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : ColouredForest (Location V E) Copy :=
  (forestCode N s,copyLocation (state s))

lemma forestCode_admitted (N : RootedBinary V E X) (sample : Copy → X)
    (s : State V E Copy) (hs : SourceValid N sample s) :
    forestCode N (admittedCode N sample s hs) = actualForest s hs.forest := by
  apply actualForest_eq_of_live_genealogy
  · rfl
  · intro l hl
    exact decode_encode_live_genealogy N.root s hs.forest hl

lemma forestCode_choice (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) :
    forestCode N (stepDestination N s (some p)) =
      actualForest (merge (state s) p.2.val.1 p.2.val.2)
        (merge_valid (state s) s.property.forest
          (population_pair_is_source_legal (state s) (originalPlace N p.1)
            (originalPlace_not_node N p.1) p.2.property)) := by
  rw [stepDestination,forestCode_admitted]

lemma colourProjection_choice_locations (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Choice N s) :
    (colourProjection N (stepDestination N s (some p))).2 = (colourProjection N s).2 := by
  funext x
  let hm := population_pair_is_source_legal (state s) (originalPlace N p.1)
    (originalPlace_not_node N p.1) p.2.property
  change copyLocation (state (stepDestination N s (some p))) x = copyLocation (state s) x
  rw [stepDestination]
  change copyLocation (decodeSnapshot N.root (encodeSnapshot _ _)) x = _
  rw [decode_encode_copyLocation]
  exact merge_population_preserved (state s) hm x

lemma projected_population_merge (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (i : Option E) (p : Copy × Copy) (hp : PairAt N i p s) :
    colourProjection N (mergeAt N i p s) =
      (pairAction (forestCode N s) (colourFibre (copyLocation (state s)) (originalPlace N i))
        (pairMap (liveTreeOrLeaf (state s) s.property.forest) p),
       copyLocation (state s)) := by
  have hpair := Finset.mem_offDiag.mp hp
  have ha := populationRoots_subset_live (state s) (originalPlace N i) hpair.1
  have hb := populationRoots_subset_live (state s) (originalPlace N i) hpair.2.1
  have hmem : pairMap (liveTreeOrLeaf (state s) s.property.forest) p ∈
      (activeTrees (forestCode N s)
        (colourFibre (copyLocation (state s)) (originalPlace N i))).offDiag := by
    change _ ∈ ((actualForest (state s) s.property.forest).filter _).offDiag
    rw [← image_population_pairs]
    exact Finset.mem_image.mpr ⟨p,hp,rfl⟩
  have hl := (legalPair_iff_mem_active_offDiag (forestCode N s)
    (actualForest_partition (state s) s.property.forest) _ _).mpr hmem
  apply Prod.ext
  · change forestCode N (mergeAt N i p s) = _
    rw [mergeAt_of_mem N i p s hp,forestCode_choice,actualForest_merge,pairAction,dif_pos hl]
    simp only [pairMap,liveTreeOrLeaf,dif_pos ha,dif_pos hb,forestCode]
  · rw [mergeAt_of_mem N i p s hp]
    exact colourProjection_choice_locations N s ⟨i,⟨p,hp⟩⟩

/-- At ancestral entry every original copy has the same root colour. -/
lemma ancestral_colourFibre (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : AncestralRoot N s) :
    colourFibre (copyLocation (state s)) (.rootPopulation N.root) = Finset.univ := by
  ext x
  simp only [colourFibre,Finset.mem_filter,Finset.mem_univ,true_and]
  exact iff_of_true (hs x) trivial

lemma ancestral_forest_pair_image (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : AncestralRoot N s) :
    (state s).live.offDiag.image (pairMap (liveTreeOrLeaf (state s) s.property.forest)) =
      rootPairs (forestCode N s) := by
  rw [rootPairs_eq_offDiag _ (actualForest_partition (state s) s.property.forest)]
  have hi := image_population_pairs (state s) s.property.forest (.rootPopulation N.root)
  rw [ancestral_roots N s hs] at hi
  have hf := ancestral_colourFibre N s hs
  change Finset.univ.filter (fun x => copyLocation (state s) x =
    Location.rootPopulation N.root) = Finset.univ at hf
  simpa only [hf,Finset.subset_univ,Finset.filter_true,forestCode] using hi

/-- The accepted actual ordered-Choice equivalence is followed by the injective
live genealogy image. No unordered-pair identification or survivor choice is
introduced in the root completion step. -/
noncomputable def rootForestChoice (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : AncestralRoot N s) (p : Choice N s) :
    {q // q ∈ rootPairs (forestCode N s)} :=
  ⟨pairMap (liveTreeOrLeaf (state s) s.property.forest) (rootChoices N s hs p).val,by
    rw [← ancestral_forest_pair_image N s hs]
    exact Finset.mem_image.mpr ⟨_,(rootChoices N s hs p).property,rfl⟩⟩

lemma rootForestChoice_bijective (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : AncestralRoot N s) :
    Function.Bijective (rootForestChoice N s hs) := by
  constructor
  · intro p q he
    apply (rootChoices N s hs).injective
    apply Subtype.ext
    have hp := Finset.mem_offDiag.mp (rootChoices N s hs p).property
    have hq := Finset.mem_offDiag.mp (rootChoices N s hs q).property
    have hv := congrArg Subtype.val he
    apply Prod.ext
    · exact liveTreeOrLeaf_injective_on (state s) s.property.forest _ hp.1 _ hq.1
        (congrArg Prod.fst hv)
    · exact liveTreeOrLeaf_injective_on (state s) s.property.forest _ hp.2.1 _ hq.2.1
        (congrArg Prod.snd hv)
  · intro q
    have hq := q.property
    rw [← ancestral_forest_pair_image N s hs] at hq
    obtain ⟨p,hp,he⟩ := Finset.mem_image.mp hq
    refine ⟨(rootChoices N s hs).symm ⟨p,hp⟩,?_⟩
    apply Subtype.ext
    simpa only [rootForestChoice,Equiv.apply_symm_apply] using he

noncomputable def rootForestChoices (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : AncestralRoot N s) :
    Choice N s ≃ {q // q ∈ rootPairs (forestCode N s)} :=
  Equiv.ofBijective (rootForestChoice N s hs) (rootForestChoice_bijective N s hs)

lemma rootForestChoice_destination (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (hs : AncestralRoot N s) (p : Choice N s) :
    forestCode N (stepDestination N s (some p)) =
      pairAction (forestCode N s) Finset.univ (rootForestChoice N s hs p).val := by
  have hp := p.2.property
  have hi := ancestral_choice_population N s hs p
  have ht := congrArg Prod.fst (projected_population_merge N s p.1 p.2.val hp)
  rw [mergeAt_of_mem N p.1 p.2.val s hp] at ht
  change forestCode N (stepDestination N s (some p)) = _ at ht
  simpa only [hi,originalPlace,ancestral_colourFibre N s hs,
    rootForestChoice,rootChoices] using ht

lemma rootStep_probability (F G : Forest Copy) (h : (rootPairs F).Nonempty) :
    (rootStep F G).toReal =
      ∑ q : {q // q ∈ rootPairs F},
        (1 / ((rootPairs F).card : ℝ)) *
          (if pairAction F Finset.univ q.val = G then 1 else 0) := by
  rw [rootStep,dif_pos h]
  change (((PMF.uniformOfFinset (rootPairs F) h).bind
    (fun q => PMF.pure (pairAction F Finset.univ q))) G).toReal = _
  rw [bind_probability_real,tsum_fintype,Finset.sum_coe_sort]
  simp only [PMF.uniformOfFinset_apply,apply_ite ENNReal.toReal,
    ENNReal.toReal_inv,ENNReal.toReal_natCast,ENNReal.toReal_zero,
    PMF.pure_apply,apply_ite ENNReal.toReal,ENNReal.toReal_one,one_div]
  have he (q : WellLabelledTree Copy × WellLabelledTree Copy) :
      (if q ∈ rootPairs F then ((rootPairs F).card : ℝ)⁻¹ else 0) *
          (if G = pairAction F Finset.univ q then 1 else 0) =
      if q ∈ rootPairs F then ((rootPairs F).card : ℝ)⁻¹ *
          (if pairAction F Finset.univ q = G then 1 else 0) else 0 := by
    by_cases hq : q ∈ rootPairs F <;> simp [hq,eq_comm]
  simp_rw [he]
  rw [← Finset.sum_filter]
  simp only [Finset.filter_mem_eq_inter,Finset.univ_inter]

/-- The ancestral embedded jump pushes forward to the independent uniform
ordered whole-tree merger. This statement includes empty and singleton copies. -/
theorem actual_root_step_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hs : AncestralRoot N s) :
    (sourceJumpStep N r s).map (forestCode N) = rootStep (forestCode N s) := by
  have hF := actualForest_partition (state s) s.property.forest
  have hc : (forestCode N s).card = liveCard s := by
    exact actualForest_card (state s) s.property.forest
  by_cases ht : liveCard s ≤ 1
  · rw [source_jump_absorbs_terminal N r s ht,PMF.pure_map]
    have hn := (rootPairs_empty_iff _ hF).mpr (by simpa only [hc] using ht)
    rw [rootStep,dif_neg hn]
  · have hnt : 1 < liveCard s := Nat.lt_of_not_ge ht
    letI := ancestral_choice_exists N s hs hnt
    have hn : (rootPairs (forestCode N s)).Nonempty := by
      by_contra he
      exact ht (by simpa only [hc] using (rootPairs_empty_iff _ hF).mp he)
    have hcard : Fintype.card (Choice N s) = (rootPairs (forestCode N s)).card := by
      rw [Fintype.card_congr (rootForestChoices N s hs),Fintype.card_coe]
    have hpos : Fintype.card (Choice N s) ≠ 0 := ne_of_gt Fintype.card_pos
    apply PMF.ext
    intro G
    apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
    rw [rootStep_probability _ _ hn,sourceJumpStep,PMF.map_comp]
    change (((sourceJumpChoice N r s).bind
      (fun q => PMF.pure (forestCode N (stepDestination N s q)))) G).toReal = _
    rw [bind_probability_real,tsum_fintype,Fintype.sum_option]
    simp_rw [sourceJumpChoice_apply,ENNReal.toReal_ofReal (jumpMass_nonnegative N r s _),
      ancestral_jump_mass N r s hs]
    simp only [ancestralChoiceMass,if_neg hpos,zero_mul,zero_add,
      PMF.pure_apply,apply_ite ENNReal.toReal,ENNReal.toReal_one,ENNReal.toReal_zero]
    rw [hcard]
    calc
      _ = ∑ p : Choice N s, (1 / ((rootPairs (forestCode N s)).card : ℝ)) *
          (if pairAction (forestCode N s) Finset.univ
            (rootForestChoice N s hs p).val = G then 1 else 0) := by
        apply Finset.sum_congr rfl
        intro p _
        rw [rootForestChoice_destination N s hs p]
        simp only [eq_comm]
      _ = _ := (rootForestChoices N s hs).sum_comp _

/-- Every supported actual root jump retains the ancestral-root condition;
this reuses actual source support, rather than an abstract merger relation. -/
lemma actual_root_step_preserved (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hs : AncestralRoot N s)
    {d : Code N sample} (hd : d ∈ (sourceJumpStep N r s).support) : AncestralRoot N d := by
  rcases source_jump_support_cases N r s hd with ⟨rfl,_⟩ | ⟨p,rfl⟩
  · exact hs
  · exact ancestral_merger_preserved N s hs p

/-- Full ordered forest transport through the finite actual ancestral jump
completion, with the same iteration budget on the independent evaluator. -/
theorem actual_root_iteration_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) (hs : AncestralRoot N s) :
    (ancestralCompletion N r n s).map (forestCode N) = rootIteration n (forestCode N s) := by
  induction n generalizing s with
  | zero => simp only [ancestralCompletion,rootIteration,PMF.pure_map]
  | succ n ih =>
      rw [ancestralCompletion,PMF.map_bind,rootIteration]
      calc
        _ = (sourceJumpStep N r s).bind (fun d => rootIteration n (forestCode N d)) := by
          apply UnifiedLean.Source.SourceCompletionHarmonic.bind_congr_on_support
          intro d hd
          exact ih d (actual_root_step_preserved N r s hs hd)
        _ = ((sourceJumpStep N r s).map (forestCode N)).bind (rootIteration n) := by
          rw [PMF.bind_map]
        _ = _ := by rw [actual_root_step_law N r s hs]

theorem actual_ordinary_completion_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (hs : AncestralRoot N s) :
    (ancestralCompletion N r (Fintype.card Copy) s).map (forestCode N) =
      ordinaryCompletion (forestCode N s) :=
  actual_root_iteration_law N r (Fintype.card Copy) s hs

/-- Observation is the actual child-swap quotient on the completed full forest.
No reassociation or leaf-label erasure occurs at this final map. -/
theorem actual_ordinary_completed_observation (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s : Code N sample)
    (hs : AncestralRoot N s) :
    (ancestralCompletion N r (Fintype.card Copy) s).map
        (fun d => sourceUnrankedForest (state d) Finset.univ) =
      (ordinaryCompletion (forestCode N s)).map forestObservation := by
  rw [← actual_ordinary_completion_law N r s hs,PMF.map_comp]
  congr 1
  funext d
  exact (actualForest_observation (state d) d.property.forest).symm

/-- Root completion depends only on the full carried forest, once actual
ancestral entry is proved. In particular an inert stored-register change is
invisible here; no equality of source Codes is asserted. -/
theorem actual_root_completion_eq_of_forest_eq (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (s d : Code N sample)
    (hs : AncestralRoot N s) (hd : AncestralRoot N d)
    (hf : forestCode N s = forestCode N d) :
    (ancestralCompletion N r (Fintype.card Copy) s).map
        (fun z => sourceUnrankedForest (state z) Finset.univ) =
      (ancestralCompletion N r (Fintype.card Copy) d).map
        (fun z => sourceUnrankedForest (state z) Finset.univ) := by
  rw [actual_ordinary_completed_observation N r s hs,
    actual_ordinary_completed_observation N r d hd,hf]

/-- One population factor of the independent coloured-forest generator. Other
colours do not move; the full original generator sums only finite-edge and the
original root-population factors. Pending-birth/node colours receive no factor. -/
noncomputable def colouredGenerator (place : Location V E) :
    Matrix (ColouredForest (Location V E) Copy) (ColouredForest (Location V E) Copy) ℝ :=
  fun s d => if s.2 = d.2 then cladeGenerator (colourFibre s.2 place) s.1 d.1 else 0

noncomputable def originalColouredGenerator (N : RootedBinary V E X)
    (r : PositivePairRates E) :
    Matrix (ColouredForest (Location V E) Copy) (ColouredForest (Location V E) Copy) ℝ :=
  ∑ i : Option E, pairRate r i • colouredGenerator (originalPlace N i)

noncomputable def fibreGenerator (N : RootedBinary V E X) (r : PositivePairRates E)
    (f : Copy → Location V E) : Matrix (Forest Copy) (Forest Copy) ℝ :=
  ∑ i : Option E, pairRate r i • cladeGenerator (colourFibre f (originalPlace N i))

noncomputable def populationExposure (r : PositivePairRates E) (t : ℝ≥0)
    (i : Option E) : ℝ≥0 :=
  ⟨(t : ℝ) * pairRate r i,mul_nonneg t.property (pairRate_pos r i).le⟩

noncomputable def fibreEpochOps (N : RootedBinary V E X) (r : PositivePairRates E)
    (f : Copy → Location V E) (t : ℝ≥0) : List (Finset Copy × ℝ≥0) :=
  (Finset.univ : Finset (Option E)).toList.map
    (fun i => (colourFibre f (originalPlace N i),populationExposure r t i))

noncomputable def fibreEpochKernel (N : RootedBinary V E X) (r : PositivePairRates E)
    (f : Copy → Location V E) (t : ℝ≥0) (F : Forest Copy) : PMF (Forest Copy) :=
  forestProgram (fibreEpochOps N r f t) F

lemma fibreEpochOps_commute (N : RootedBinary V E X) (r : PositivePairRates E)
    (f : Copy → Location V E) (t : ℝ≥0) :
    ∀ a ∈ fibreEpochOps N r f t, ∀ b ∈ fibreEpochOps N r f t,
      Commute (weightedCladeGenerator a) (weightedCladeGenerator b) := by
  intro a ha b hb
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp ha
  obtain ⟨j,_,rfl⟩ := List.mem_map.mp hb
  by_cases hij : i = j
  · subst j; exact Commute.refl _
  · have hplaces : originalPlace N i ≠ originalPlace N j := by
      intro he; exact hij (GProgram.G7.SinglePopulationPolynomialKernel.originalPlace_injective N he)
    exact ((cladeGenerator_disjoint_commute (colourFibres_disjoint f hplaces)).smul_left
      (populationExposure r t i : ℝ)).smul_right (populationExposure r t j : ℝ)

lemma fibreEpochOps_sum (N : RootedBinary V E X) (r : PositivePairRates E)
    (f : Copy → Location V E) (t : ℝ≥0) :
    ((fibreEpochOps N r f t).map weightedCladeGenerator).sum = (t : ℝ) • fibreGenerator N r f := by
  simp only [fibreEpochOps,List.map_map,Function.comp_def,weightedCladeGenerator,
    populationExposure,Finset.sum_toList,fibreGenerator,Finset.smul_sum,smul_smul]

lemma fibreEpochKernel_exponential (N : RootedBinary V E X) (r : PositivePairRates E)
    (f : Copy → Location V E) (t : ℝ≥0) (F G : Forest Copy) :
    (fibreEpochKernel N r f t F G).toReal = (exp ((t : ℝ) • fibreGenerator N r f)) F G := by
  rw [fibreEpochKernel,forestProgram_commuting_probability _ (fibreEpochOps_commute N r f t),
    fibreEpochOps_sum]

noncomputable def fixedColourMatrix (f : Copy → Location V E) :
    Matrix (Forest Copy) (ColouredForest (Location V E) Copy) ℝ :=
  fun F d => if (F,f) = d then 1 else 0

lemma fixedColourMatrix_mul (f : Copy → Location V E)
    (B : Matrix (ColouredForest (Location V E) Copy) (ColouredForest (Location V E) Copy) ℝ)
    (F : Forest Copy) (d : ColouredForest (Location V E) Copy) :
    (fixedColourMatrix f * B) F d = B (F,f) d := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (F,f)]
  · simp [fixedColourMatrix]
  · intro x _ hx; simp [fixedColourMatrix,Ne.symm hx]
  · simp

lemma mul_fixedColourMatrix (f : Copy → Location V E)
    (B : Matrix (Forest Copy) (Forest Copy) ℝ) (F G : Forest Copy) (g : Copy → Location V E) :
    (B * fixedColourMatrix f) F (G,g) = if f = g then B F G else 0 := by
  rw [Matrix.mul_apply]
  by_cases h : f = g
  · subst g
    simp only [fixedColourMatrix,Prod.mk.injEq,and_true,if_true]
    simp
  · simp only [fixedColourMatrix,Prod.mk.injEq,h,and_false,if_false,mul_zero,Finset.sum_const_zero]

lemma fixedColour_generator_intertwining (N : RootedBinary V E X) (r : PositivePairRates E)
    (f : Copy → Location V E) :
    fibreGenerator N r f * fixedColourMatrix f =
      fixedColourMatrix f * originalColouredGenerator N (Copy := Copy) r := by
  ext F d
  rcases d with ⟨G,g⟩
  rw [mul_fixedColourMatrix,fixedColourMatrix_mul]
  by_cases h : f = g
  · simp only [h,if_true,originalColouredGenerator,colouredGenerator,
      Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,fibreGenerator]
  · simp only [h,if_false,originalColouredGenerator,colouredGenerator,
      Matrix.sum_apply,Matrix.smul_apply,smul_eq_mul,mul_zero,Finset.sum_const_zero]

lemma fixedColour_epoch (N : RootedBinary V E X) (r : PositivePairRates E)
    (f : Copy → Location V E) (t : ℝ≥0) (F G : Forest Copy) (g : Copy → Location V E) :
    (exp ((t : ℝ) • originalColouredGenerator N (Copy := Copy) r)) (F,f) (G,g) =
      if f = g then (exp ((t : ℝ) • fibreGenerator N r f)) F G else 0 := by
  have h := UnifiedLean.Source.MatrixProjectionExponential.rectangular_scaled_exp_intertwining
    _ _ _ (fixedColour_generator_intertwining N r f) (t : ℝ)
  have he := congrArg (fun M : Matrix (Forest Copy) (ColouredForest (Location V E) Copy) ℝ => M F (G,g)) h
  rw [mul_fixedColourMatrix,fixedColourMatrix_mul] at he
  exact he.symm

noncomputable def colourProjectionMatrix (N : RootedBinary V E X) {sample : Copy → X} :
    Matrix (Code N sample) (ColouredForest (Location V E) Copy) ℝ :=
  fun s d => if colourProjection N s = d then 1 else 0

lemma pairMatrix_readout {Obs : Type*} (N : RootedBinary V E X) {sample : Copy → X}
    (i : Option E) (p : Copy × Copy) (B : Matrix (Code N sample) Obs ℝ)
    (s : Code N sample) (d : Obs) :
    (pairMatrix N i p * B) s d = B (mergeAt N i p s) d := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (mergeAt N i p s)]
  · simp [pairMatrix]
  · intro x _ hx
    simp [pairMatrix,Ne.symm hx]
  · simp

lemma populationGenerator_readout {Obs : Type*} (N : RootedBinary V E X)
    {sample : Copy → X} (i : Option E) (B : Matrix (Code N sample) Obs ℝ)
    (s : Code N sample) (d : Obs) :
    (populationGenerator N i * B) s d =
      (1 / 2 : ℝ) * ∑ p : Copy × Copy, (B (mergeAt N i p s) d - B s d) := by
  rw [populationGenerator,Matrix.smul_mul,Matrix.sum_mul]
  simp only [Matrix.sub_mul,Matrix.one_mul,Matrix.smul_apply,Matrix.sum_apply,
    Matrix.sub_apply,smul_eq_mul,pairMatrix_readout]

lemma populationGenerator_readout_active {Obs : Type*} (N : RootedBinary V E X)
    {sample : Copy → X} (i : Option E) (B : Matrix (Code N sample) Obs ℝ)
    (s : Code N sample) (d : Obs) :
    (populationGenerator N i * B) s d =
      (1 / 2 : ℝ) * ∑ p ∈ (populationRoots (state s) (originalPlace N i)).offDiag,
        (B (mergeAt N i p s) d - B s d) := by
  rw [populationGenerator_readout]
  congr 1
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro p _ hp
  rw [mergeAt_of_not_mem N i p s hp,sub_self]

lemma colourProjectionMatrix_mul (N : RootedBinary V E X) {sample : Copy → X}
    (B : Matrix (ColouredForest (Location V E) Copy) (ColouredForest (Location V E) Copy) ℝ)
    (s : Code N sample) (d : ColouredForest (Location V E) Copy) :
    (colourProjectionMatrix N * B) s d = B (colourProjection N s) d := by
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single (colourProjection N s)]
  · simp [colourProjectionMatrix]
  · intro x _ hx
    simp [colourProjectionMatrix,Ne.symm hx]
  · simp

/-- Concrete source population generator transport. This derives the needed
rectangular identity from actual merger destinations and the accepted ordered
pair bijection. It is not a supplied lumpability or conditional-law premise. -/
lemma population_colour_intertwining (N : RootedBinary V E X) {sample : Copy → X}
    (i : Option E) :
    populationGenerator N (sample := sample) i * colourProjectionMatrix N =
      colourProjectionMatrix N * colouredGenerator (originalPlace N i) := by
  ext s d
  rcases d with ⟨G,g⟩
  rw [populationGenerator_readout_active,colourProjectionMatrix_mul]
  by_cases hf : copyLocation (state s) = g
  · subst g
    simp only [colouredGenerator,colourProjection,if_true]
    rw [cladeGenerator_active_row (forestCode N s)
      (actualForest_partition (state s) s.property.forest)]
    congr 1
    let A := colourFibre (copyLocation (state s)) (originalPlace N i)
    let w := fun q : WellLabelledTree Copy × WellLabelledTree Copy =>
      (if pairAction (forestCode N s) A q = G then (1 : ℝ) else 0) -
        (if forestCode N s = G then 1 else 0)
    calc
      _ = ∑ p ∈ (populationRoots (state s) (originalPlace N i)).offDiag,
          w (pairMap (liveTreeOrLeaf (state s) s.property.forest) p) := by
        apply Finset.sum_congr rfl
        intro p hp
        rw [colourProjectionMatrix,projected_population_merge N s i p hp]
        simp only [colourProjectionMatrix,colourProjection,Prod.mk.injEq,and_true,w,A]
      _ = ∑ q ∈ ((populationRoots (state s) (originalPlace N i)).image
          (liveTreeOrLeaf (state s) s.property.forest)).offDiag, w q := by
        apply projected_pair_sum
        intro a ha b hb
        exact liveTreeOrLeaf_injective_on (state s) s.property.forest a
          (populationRoots_subset_live (state s) (originalPlace N i) ha) b
          (populationRoots_subset_live (state s) (originalPlace N i) hb)
      _ = _ := by
        rw [image_populationRoots]
        rfl
  · simp only [colouredGenerator,colourProjection,if_neg hf]
    rw [mul_eq_zero]
    right
    apply Finset.sum_eq_zero
    intro p hp
    rw [colourProjectionMatrix,projected_population_merge N s i p hp]
    simp only [colourProjectionMatrix,colourProjection,Prod.mk.injEq,hf,and_false,if_false,sub_self]

lemma actual_colour_generator_intertwining (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) :
    UnifiedLean.Source.SourceGeneratorExponential.sourceGeneratorMatrix N r *
        (colourProjectionMatrix N (sample := sample)) =
      colourProjectionMatrix N * originalColouredGenerator N (Copy := Copy) r := by
  rw [actual_generator_all_populations,originalColouredGenerator,Matrix.sum_mul,Matrix.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Matrix.smul_mul,Matrix.mul_smul,population_colour_intertwining]

/-- The full actual epoch law now has a derived coloured-forest exponential
projection. Subsequent clade scheduling/normalization is a separate composition,
not a premise hidden in this equality. -/
theorem actual_colour_epoch_intertwining (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (t : ℝ≥0) :
    exp ((t : ℝ) • UnifiedLean.Source.SourceGeneratorExponential.sourceGeneratorMatrix N r) *
        (colourProjectionMatrix N (sample := sample)) =
      colourProjectionMatrix N * exp ((t : ℝ) • originalColouredGenerator N (Copy := Copy) r) :=
  UnifiedLean.Source.MatrixProjectionExponential.rectangular_scaled_exp_intertwining
    _ _ _ (actual_colour_generator_intertwining N r) t

theorem actual_colour_epoch_probability (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample)
    (d : ColouredForest (Location V E) Copy) :
    (((sourceTimeKernel N r t s).map (colourProjection N)) d).toReal =
      (exp ((t : ℝ) • originalColouredGenerator N (Copy := Copy) r)) (colourProjection N s) d := by
  calc
    _ = (exp ((t : ℝ) • UnifiedLean.Source.SourceGeneratorExponential.sourceGeneratorMatrix N r) *
        colourProjectionMatrix N) s d := by
      rw [PMF.map,bind_probability_real,tsum_fintype,Matrix.mul_apply]
      apply Finset.sum_congr rfl
      intro z _
      rw [source_time_kernel_eq_exponential]
      by_cases h : colourProjection N z = d
      · simp [colourProjectionMatrix,PMF.pure_apply,Function.comp_apply,h]
      · simp [colourProjectionMatrix,PMF.pure_apply,Function.comp_apply,h,Ne.symm h]
    _ = (colourProjectionMatrix N * exp ((t : ℝ) • originalColouredGenerator N (Copy := Copy) r)) s d := by
      rw [actual_colour_epoch_intertwining]
    _ = _ := colourProjectionMatrix_mul N _ s d

lemma fibreEpochKernel_colour_map_probability (N : RootedBinary V E X)
    (r : PositivePairRates E) (f : Copy → Location V E) (t : ℝ≥0)
    (F G : Forest Copy) (g : Copy → Location V E) :
    (((fibreEpochKernel N r f t F).map (fun K => (K,f))) (G,g)).toReal =
      if f = g then (fibreEpochKernel N r f t F G).toReal else 0 := by
  rw [PMF.map,bind_probability_real,tsum_fintype]
  by_cases h : f = g
  · subst g
    simp only [Function.comp_apply,PMF.pure_apply,Prod.mk.injEq,and_true,if_true]
    simp
  · have h' : g ≠ f := Ne.symm h
    simp only [Function.comp_apply,PMF.pure_apply,Prod.mk.injEq,h',and_false,
      if_false,ENNReal.toReal_zero,mul_zero,Finset.sum_const_zero,h]

/-- Full actual epoch pushforward, retaining the exact location fibres. The
right PMF is built solely from the independent ordinary clade kernels. -/
theorem actual_colour_epoch_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) :
    (sourceTimeKernel N r t s).map (colourProjection N) =
      (fibreEpochKernel N r (copyLocation (state s)) t (forestCode N s)).map
        (fun F => (F,copyLocation (state s))) := by
  apply PMF.ext
  intro d
  rcases d with ⟨G,g⟩
  apply (ENNReal.toReal_eq_toReal_iff' (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [actual_colour_epoch_probability,fibreEpochKernel_colour_map_probability]
  change (exp ((t : ℝ) • originalColouredGenerator N (Copy := Copy) r))
    (forestCode N s,copyLocation (state s)) (G,g) = _
  rw [fixedColour_epoch,fibreEpochKernel_exponential]

/-- Complete ordered genealogy-forest epoch transport, with no fitted kernel,
count-only replacement, or equality-valued interface premise. The fixed fibre
function is the actual original-copy location function of the supplied state. -/
theorem actual_forest_epoch_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) :
    (sourceTimeKernel N r t s).map (forestCode N) =
      fibreEpochKernel N r (copyLocation (state s)) t (forestCode N s) := by
  have h := congrArg (fun p : PMF (ColouredForest (Location V E) Copy) => p.map Prod.fst)
    (actual_colour_epoch_law N r t s)
  simpa only [PMF.map_comp,Function.comp_def,colourProjection,PMF.map_id] using h

end SourceProjection

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
variable {V E X Copy : Type*}
variable [Fintype Copy] [DecidableEq Copy]
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

/-- Only forced ORIGINAL hybrid vertices are erased for the comparison;
unforced stored bits remain correlated exactly as drawn initially. -/
noncomputable def forcedVertices (N : RootedBinary V E X) (mask : OriginalMask N) : Finset V :=
  (Finset.univ.filter (fun h : Hybrid N => (mask h).isSome)).image Subtype.val

lemma mem_forcedVertices (N : RootedBinary V E X) (mask : OriginalMask N) (h : Hybrid N) :
    h.val ∈ forcedVertices N mask ↔ (mask h).isSome := by
  constructor
  · intro hh
    obtain ⟨h',hh',he⟩ := Finset.mem_image.mp hh
    have heq : h' = h := Subtype.ext he
    subst h'
    exact (Finset.mem_filter.mp hh').2
  · intro hh
    exact Finset.mem_image.mpr ⟨h,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hh⟩,rfl⟩

open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.G6.PrivateRegisterErasure
open UnifiedLean.G6.PrivateRegisterBoundary
open UnifiedLean.G6.PrivateRegisterProgram
open UnifiedLean.G6.GuardedBinErasure

lemma controlled_node_no_forced_read (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (mask : OriginalMask N) (v : V) :
    NoPrivateRead N (forcedVertices N mask)
      (originalNodeOperation N H (controlledGamma p mask)
        (controlledMode (fun _ => true) mask) v) := by
  by_cases hr : v = N.root
  · simp [originalNodeOperation,hr,NoPrivateRead]
  · by_cases hh : N.graph.IsHybrid v
    · cases hm : mask ⟨v,hh⟩ with
      | none =>
          have hn : v ∉ forcedVertices N mask := by
            rw [mem_forcedVertices N mask ⟨v,hh⟩,hm]
            simp
          simpa [originalNodeOperation,hr,hh,controlledMode,hm,NoPrivateRead,
            H.original_site] using hn
      | some b =>
          simp [originalNodeOperation,hr,hh,controlledMode,controlledGamma,hm,NoPrivateRead]
    · simp [originalNodeOperation,hr,hh,NoPrivateRead]

lemma controlled_batch_no_forced_read (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (mask : OriginalMask N) (a : ℝ) :
    NoPrivateWordRead N (forcedVertices N mask)
      (boundaryOperations N C H (controlledGamma p mask)
        (controlledMode (fun _ => true) mask) a) := by
  intro op hop
  change op ∈ _ ++ _ at hop
  rcases List.mem_append.mp hop with he | hv
  · obtain ⟨e,_,rfl⟩ := List.mem_map.mp he
    trivial
  · obtain ⟨v,_,rfl⟩ := List.mem_map.mp hv
    exact controlled_node_no_forced_read N H p mask v

lemma controlled_tail_no_forced_read (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (mask : OriginalMask N) (a : ℝ) (dates : List ℝ) :
    NoPrivateWordRead N (forcedVertices N mask)
      (calendarTail N C H (controlledGamma p mask)
        (controlledMode (fun _ => true) mask) a dates) := by
  induction dates generalizing a with
  | nil => intro op hop; simp [calendarTail] at hop
  | cons b dates ih =>
      intro op hop
      rcases List.mem_cons.mp hop with rfl | hop
      · trivial
      · rcases List.mem_append.mp hop with hb | ht
        · exact controlled_batch_no_forced_read N C H p mask b op hb
        · exact ih b op ht

/-- The literal controlled compiler never reads a forced site's stored bit.
This is derived despite controlledMode being false at that site. -/
theorem controlled_calendar_no_forced_read (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (mask : OriginalMask N) :
    NoPrivateWordRead N (forcedVertices N mask)
      (controlledCalendarProgram N C H p (fun _ => true) mask) := by
  unfold controlledCalendarProgram compiledCalendarProgram
  cases hd : sortedOriginalDates N C with
  | nil => intro op hop; simp at hop
  | cons a dates =>
      intro op hop
      rcases List.mem_append.mp hop with ha | ht
      · exact controlled_batch_no_forced_read N C H p mask a op ha
      · exact controlled_tail_no_forced_read N C H p mask a dates op ht

/-- Erasure commutes with the literal controlled calendar AND its actual
finite ancestral completion. Both ingredients are accepted source transports;
no natural-register marginal is substituted at a conditioned cut. -/
theorem controlled_completed_erasure (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (mask : OriginalMask N) {sample : Copy → X}
    (s : Code N sample) :
    (((sourceProgram N r (controlledCalendarProgram N C H p (fun _ => true) mask) s).bind
      (ancestralCompletion N r (Fintype.card Copy))).map
        (erasePrivateCode N (forcedVertices N mask))) =
      (sourceProgram N r (controlledCalendarProgram N C H p (fun _ => true) mask)
        (erasePrivateCode N (forcedVertices N mask) s)).bind
          (ancestralCompletion N r (Fintype.card Copy)) := by
  rw [PMF.map_bind]
  simp_rw [actual_ancestral_completion_erasure]
  change (sourceProgram N r _ s).bind
    ((ancestralCompletion N r (Fintype.card Copy)) ∘
      erasePrivateCode N (forcedVertices N mask)) = _
  rw [← PMF.bind_map,actual_sourceProgram_erasure N r (forcedVertices N mask) _
    (controlled_calendar_no_forced_read N C H p mask) s]

lemma erased_full_observation (N : RootedBinary V E X) {sample : Copy → X}
    (P : Finset V) (s : Code N sample) :
    sourceUnrankedForest (state (erasePrivateCode N P s)) Finset.univ =
      sourceUnrankedForest (state s) Finset.univ := rfl

theorem controlled_completed_observation_erasure (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (mask : OriginalMask N) {sample : Copy → X}
    (s : Code N sample) :
    ((sourceProgram N r (controlledCalendarProgram N C H p (fun _ => true) mask) s).bind
      (ancestralCompletion N r (Fintype.card Copy))).map
        (fun d => sourceUnrankedForest (state d) Finset.univ) =
      ((sourceProgram N r (controlledCalendarProgram N C H p (fun _ => true) mask)
        (erasePrivateCode N (forcedVertices N mask) s)).bind
          (ancestralCompletion N r (Fintype.card Copy))).map
            (fun d => sourceUnrankedForest (state d) Finset.univ) := by
  rw [← controlled_completed_erasure N C H p r mask s,PMF.map_comp]
  rfl

open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceInitializedCalendar

lemma original_register_override_outside_forced (N : RootedBinary V E X)
    (mask : OriginalMask N) (coin : CommonSeed N) (v : V)
    (hv : v ∉ forcedVertices N mask) :
    originalRegister N (overrideBank N mask coin) v = originalRegister N coin v := by
  by_cases hh : N.graph.IsHybrid v
  · have hm : mask ⟨v,hh⟩ = none := by
      cases he : mask ⟨v,hh⟩ with
      | none => rfl
      | some b =>
          exact False.elim (hv ((mem_forcedVertices N mask ⟨v,hh⟩).mpr (by simp [he])))
    simp only [originalRegister,dif_pos hh,overrideBank,hm,Option.getD_none]
  · simp only [originalRegister,dif_neg hh]

lemma erased_initial_override (N : RootedBinary V E X) (sample : Copy → X)
    (mask : OriginalMask N) (coin : CommonSeed N) :
    erasePrivateCode N (forcedVertices N mask)
        (initialCode N sample (originalRegister N coin)) =
      erasePrivateCode N (forcedVertices N mask)
        (initialCode N sample (originalRegister N (overrideBank N mask coin))) := by
  apply Subtype.ext
  apply Snapshot.ext <;> try rfl
  funext v
  change (if v ∈ forcedVertices N mask then false else originalRegister N coin v) =
    (if v ∈ forcedVertices N mask then false else
      originalRegister N (overrideBank N mask coin) v)
  by_cases hv : v ∈ forcedVertices N mask
  · simp only [if_pos hv]
  · rw [if_neg hv,if_neg hv,original_register_override_outside_forced N mask coin v hv]

/-- First controlled-mask leg: only the passive completed forest law is
compared. The left source still starts with its ORIGINAL once-drawn register;
forcing does not overwrite that source state. -/
theorem controlled_initial_bank_override_observation (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (mask : OriginalMask N) (sample : Copy → X)
    (coin : CommonSeed N) :
    ((sourceProgram N r (controlledCalendarProgram N C H p (fun _ => true) mask)
      (initialCode N sample (originalRegister N coin))).bind
        (ancestralCompletion N r (Fintype.card Copy))).map
          (fun d => sourceUnrankedForest (state d) Finset.univ) =
      ((sourceProgram N r (controlledCalendarProgram N C H p (fun _ => true) mask)
        (initialCode N sample (originalRegister N (overrideBank N mask coin)))).bind
          (ancestralCompletion N r (Fintype.card Copy))).map
            (fun d => sourceUnrankedForest (state d) Finset.univ) := by
  rw [controlled_completed_observation_erasure N C H p r mask
    (initialCode N sample (originalRegister N coin)),
    controlled_completed_observation_erasure N C H p r mask
      (initialCode N sample (originalRegister N (overrideBank N mask coin))),
    erased_initial_override N sample mask coin]

lemma forced_boundary_eq_common_of_register {N : RootedBinary V E X}
    {sample : Copy → X} (H : GProgram.G2.OriginalHybridParents N)
    (s : Code N sample) (b : Bool) (hb : (state s).register H.hybrid = b) :
    boundaryKernel N (.independent H (forcedParameter b)) s =
      boundaryKernel N (.common H) s := by
  rw [actual_forced_hybrid_kernel]
  change PMF.pure (pulseCode H s (fun _ => b)) =
    PMF.pure (pulseCode H s (fun _ => (state s).register H.hybrid))
  rw [hb]

lemma controlled_node_eq_override_common (N : RootedBinary V E X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (mask : OriginalMask N) (coin : CommonSeed N) {sample : Copy → X}
    (s : Code N sample)
    (hreg : (state s).register = originalRegister N (overrideBank N mask coin)) (v : V) :
    boundaryKernel N (originalNodeOperation N H (controlledGamma p mask)
      (controlledMode (fun _ => true) mask) v) s =
      boundaryKernel N (originalNodeOperation N H (originalGamma p) (fun _ => true) v) s := by
  by_cases hr : v = N.root
  · simp only [originalNodeOperation,dif_pos hr]
  · by_cases hh : N.graph.IsHybrid v
    · cases hm : mask ⟨v,hh⟩ with
      | none => simp [originalNodeOperation,hr,hh,controlledMode,hm]
      | some b =>
          rw [original_forced_node_compiler N H p (fun _ => true) mask ⟨v,hh⟩ b hm]
          have hb : (state s).register (H.parents ⟨v,hh⟩).hybrid = b := by
            rw [hreg,H.original_site]
            simp only [originalRegister,dif_pos hh,overrideBank,hm,Option.getD_some]
          simpa only [originalNodeOperation,dif_neg hr,dif_pos hh,if_true] using
            forced_boundary_eq_common_of_register (H.parents ⟨v,hh⟩) s b hb
    · simp only [originalNodeOperation,dif_neg hr,dif_neg hh]

/-- A proof device for replacing concrete compiler steps on the preserved
register fibre. The final compiler theorem below derives every row equality. -/
def SameRegisterStep (N : RootedBinary V E X) (sample : Copy → X)
    (r : PositivePairRates E) (register : V → Bool) (op oq : ProgramStep N) : Prop :=
  ∀ s : Code N sample, (state s).register = register →
    sourceProgramStep N r op s = sourceProgramStep N r oq s

lemma program_eq_of_same_register_steps (N : RootedBinary V E X)
    (sample : Copy → X) (r : PositivePairRates E) (register : V → Bool)
    (ops oqs : List (ProgramStep N))
    (h : List.Forall₂ (SameRegisterStep N sample r register) ops oqs)
    (s : Code N sample) (hs : (state s).register = register) :
    sourceProgram N r ops s = sourceProgram N r oqs s := by
  induction h generalizing s with
  | nil => rfl
  | @cons op oq ops oqs hop htail ih =>
      rw [sourceProgram,sourceProgram,← hop s hs]
      apply UnifiedLean.Source.SourceCompletionHarmonic.bind_congr_on_support
      intro d hd
      apply ih d
      have hd' : d ∈ (sourceProgram N r [op] s).support := by
        simpa only [sourceProgram,PMF.bind_pure] using hd
      exact (DotG34.ActualStoredRegister.actual_program_register_support N r [op] s d hd').trans hs

lemma same_register_map_steps {A : Type*} (N : RootedBinary V E X)
    (sample : Copy → X) (r : PositivePairRates E) (register : V → Bool)
    (as : List A) (f g : A → ProgramStep N)
    (h : ∀ a, SameRegisterStep N sample r register (f a) (g a)) :
    List.Forall₂ (SameRegisterStep N sample r register) (as.map f) (as.map g) := by
  induction as with
  | nil => exact .nil
  | cons a as ih => exact .cons (h a) ih

lemma controlled_batch_override_steps (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (mask : OriginalMask N) (coin : CommonSeed N)
    (sample : Copy → X) (a : ℝ) :
    List.Forall₂ (SameRegisterStep N sample r (originalRegister N (overrideBank N mask coin)))
      (boundaryOperations N C H (controlledGamma p mask)
        (controlledMode (fun _ => true) mask) a)
      (boundaryOperations N C H (originalGamma p) (fun _ => true) a) := by
  unfold boundaryOperations
  apply List.Forall₂.append
  · apply same_register_map_steps
    intro e s hs
    rfl
  · apply same_register_map_steps
    intro v s hs
    exact controlled_node_eq_override_common N H p mask coin s hs v

lemma controlled_tail_override_steps (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (mask : OriginalMask N) (coin : CommonSeed N)
    (sample : Copy → X) (a : ℝ) (dates : List ℝ) :
    List.Forall₂ (SameRegisterStep N sample r (originalRegister N (overrideBank N mask coin)))
      (calendarTail N C H (controlledGamma p mask)
        (controlledMode (fun _ => true) mask) a dates)
      (calendarTail N C H (originalGamma p) (fun _ => true) a dates) := by
  induction dates generalizing a with
  | nil => exact .nil
  | cons b dates ih =>
      apply List.Forall₂.cons
      · intro s hs; rfl
      · exact (controlled_batch_override_steps N C H p r mask coin sample b).append (ih b)

/-- Second mask leg: the entire controlled program agrees with the original
all-COMMON compiler when evaluated on the overridden register fibre. Register
preservation is used at EVERY supported intermediate state. -/
theorem controlled_program_eq_override_common (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (mask : OriginalMask N) (coin : CommonSeed N)
    {sample : Copy → X} (s : Code N sample)
    (hs : (state s).register = originalRegister N (overrideBank N mask coin)) :
    sourceProgram N r (controlledCalendarProgram N C H p (fun _ => true) mask) s =
      sourceProgram N r (compiledCalendarProgram N C H (originalGamma p) (fun _ => true)) s := by
  apply program_eq_of_same_register_steps N sample r _ _ _ _ s hs
  unfold controlledCalendarProgram compiledCalendarProgram
  cases hd : sortedOriginalDates N C with
  | nil => exact .nil
  | cons a dates =>
      exact (controlled_batch_override_steps N C H p r mask coin sample a).append
        (controlled_tail_override_steps N C H p r mask coin sample a dates)

/-- Exact two-leg controlled-to-COMMON completed passive law. The left-hand
source retains its original bank. The comparison selector is overridden once,
using the same original IDs, rates, calendar and arbitrary copy allocation. -/
theorem controlled_completed_eq_override_common (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (r : PositivePairRates E) (mask : OriginalMask N) (sample : Copy → X)
    (coin : CommonSeed N) :
    ((sourceProgram N r (controlledCalendarProgram N C H p (fun _ => true) mask)
      (initialCode N sample (originalRegister N coin))).bind
        (ancestralCompletion N r (Fintype.card Copy))).map
          (fun d => sourceUnrankedForest (state d) Finset.univ) =
      ((sourceProgram N r (compiledCalendarProgram N C H (originalGamma p) (fun _ => true))
        (initialCode N sample (originalRegister N (overrideBank N mask coin)))).bind
          (ancestralCompletion N r (Fintype.card Copy))).map
            (fun d => sourceUnrankedForest (state d) Finset.univ) := by
  rw [controlled_initial_bank_override_observation N C H p r mask sample coin,
    controlled_program_eq_override_common N C H p r mask coin _ (by rfl)]

end Weights

end DotG4.WeightedOrdinaryTreeLaw
