import G1OriginalDescendantCohortAgenda

/-! Canonical fixed ORIGINAL-copy three-way cohort partition for crossing
source-derived bridges. The proof uses real active core routes and does not
cap old subtree descendants. -/
namespace G1CanonicalCrossingCohortPartition
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting
open G1ActualGraphNormalization G1DecoratedOriginalProvenance G1FiniteOriginalDecoratedCore
open G1ActiveCoreBridgeCohorts G1OriginalExteriorCohort
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

noncomputable def crossingLeftCopies (O T : Source X) (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] (sample : Copy → X) (e : T.Edge) :=
  originalInsideCopies O sample (D.vertex (T.network.graph.target e))

noncomputable def crossingRightCopies (O T : Source X) (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] (sample : Copy → X) (f : T.Edge) :=
  originalInsideCopies O sample (D.vertex (T.network.graph.target f))

noncomputable def crossingExteriorCopies (O T : Source X) (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] (sample : Copy → X) (e f : T.Edge) : Finset Copy :=
  Finset.univ \ (crossingLeftCopies O T D sample e ∪ crossingRightCopies O T D sample f)

theorem actual_crossing_original_cohorts_disjoint (O : Source.{u,v,w} X)
    (H : OriginalParentRegistry O.network) {T : Source X} (D : Decoration O T) (hD : Originated O H D)
    (e f : T.Edge) (he : T.network.graph.IsBridge e) (hf : T.network.graph.IsBridge f)
    (hab : O.calendar.age (D.vertex (T.network.graph.target e)) < O.calendar.age (D.vertex (T.network.graph.target f)))
    (hbc : O.calendar.age (D.vertex (T.network.graph.target f)) < O.calendar.age (D.vertex (T.network.graph.source e)))
    {Copy : Type*} [Fintype Copy] (sample : Copy → X) :
    Disjoint (crossingLeftCopies O T D sample e) (crossingRightCopies O T D sample f) := by
  have hef : e ≠ f := by intro h; subst f; exact (lt_irrefl _) hab
  have ha : T.calendar.Active (T.calendar.age (T.network.graph.target f)) e := by
    simpa only [Calendar.Active,D.calendar] using And.intro hab.le hbc
  have hb : T.calendar.Active (T.calendar.age (T.network.graph.target f)) f :=
    ⟨le_refl _,T.calendar.edge_older f⟩
  exact actual_active_originated_original_cohorts_disjoint O H D hD e f he hf hef _ ha hb sample

lemma actual_original_cohort_complement (O : Source X) {Copy : Type*} [Fintype Copy]
    (sample : Copy → X) (input : O.Vertex) :
    Finset.univ \ originalInsideCopies O sample input = originalOutsideCopies O sample input := by
  ext x
  simp [originalInsideCopies,originalOutsideCopies]

lemma actual_three_cohort_left_complement (O T : Source X) (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] (sample : Copy → X) (e f : T.Edge)
    (hdis : Disjoint (crossingLeftCopies O T D sample e) (crossingRightCopies O T D sample f)) :
    crossingRightCopies O T D sample f ∪ crossingExteriorCopies O T D sample e f =
      originalOutsideCopies O sample (D.vertex (T.network.graph.target e)) := by
  rw [←actual_original_cohort_complement]
  ext x
  have hn : ¬(x ∈ crossingLeftCopies O T D sample e ∧ x ∈ crossingRightCopies O T D sample f) :=
    fun h => Finset.disjoint_left.mp hdis h.1 h.2
  change x ∈ crossingRightCopies O T D sample f ∪ crossingExteriorCopies O T D sample e f ↔
    x ∈ Finset.univ \ crossingLeftCopies O T D sample e
  simp only [crossingExteriorCopies,Finset.mem_union,Finset.mem_sdiff,Finset.mem_univ,true_and]
  tauto

lemma actual_three_cohort_right_complement (O T : Source X) (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] (sample : Copy → X) (e f : T.Edge)
    (hdis : Disjoint (crossingLeftCopies O T D sample e) (crossingRightCopies O T D sample f)) :
    crossingLeftCopies O T D sample e ∪ crossingExteriorCopies O T D sample e f =
      originalOutsideCopies O sample (D.vertex (T.network.graph.target f)) := by
  rw [←actual_original_cohort_complement]
  ext x
  have hn : ¬(x ∈ crossingLeftCopies O T D sample e ∧ x ∈ crossingRightCopies O T D sample f) :=
    fun h => Finset.disjoint_left.mp hdis h.1 h.2
  change x ∈ crossingLeftCopies O T D sample e ∪ crossingExteriorCopies O T D sample e f ↔
    x ∈ Finset.univ \ crossingRightCopies O T D sample f
  simp only [crossingExteriorCopies,Finset.mem_union,Finset.mem_sdiff,Finset.mem_univ,true_and]
  tauto

lemma actual_three_cohort_whole_original_cover (O T : Source X) (D : Decoration O T)
    {Copy : Type*} [Fintype Copy] (sample : Copy → X) (e f : T.Edge) :
    crossingRightCopies O T D sample f ∪
      (crossingLeftCopies O T D sample e ∪ crossingExteriorCopies O T D sample e f) = Finset.univ := by
  ext x
  simp only [crossingExteriorCopies,Finset.mem_union,Finset.mem_sdiff,Finset.mem_univ,true_and]
  tauto

#print axioms actual_crossing_original_cohorts_disjoint
end G1CanonicalCrossingCohortPartition
