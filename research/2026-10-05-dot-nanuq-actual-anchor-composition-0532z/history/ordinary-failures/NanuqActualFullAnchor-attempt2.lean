import NanuqActualDistinctAnchor

/-! Complete actual-source anchor identity, including repeated labels. Three
source labels have one derived original triple median; four distinct labels
use the actual rooted-cap anchor identity. -/
namespace Nanuq.PortPatterns
open scoped Classical
variable {P : Type*} [DecidableEq P]

theorem tupleAnchor_repeat_02 (f : Fin 4 → P) (rho : ℚ) (h : f 0 = f 2) :
    tupleAnchor f rho = if tripleInjective f 0 then 1 else 0 := by
  simp only [tripleInjective_zero]
  by_cases h01 : f 0 = f 1 <;> by_cases h03 : f 0 = f 3 <;> by_cases h13 : f 1 = f 3
  all_goals simp_all [tupleAnchor,eq_comm]

theorem tupleAnchor_repeat_03 (f : Fin 4 → P) (rho : ℚ) (h : f 0 = f 3) :
    tupleAnchor f rho = if tripleInjective f 0 then 1 else 0 := by
  simp only [tripleInjective_zero]
  by_cases h01 : f 0 = f 1 <;> by_cases h02 : f 0 = f 2 <;> by_cases h12 : f 1 = f 2
  all_goals simp_all [tupleAnchor,eq_comm]

theorem tupleAnchor_repeat_12 (f : Fin 4 → P) (rho : ℚ) (h : f 1 = f 2) :
    tupleAnchor f rho = if tripleInjective f 1 then 1 else 0 := by
  simp only [tripleInjective_one]
  by_cases h01 : f 0 = f 1 <;> by_cases h03 : f 0 = f 3 <;> by_cases h13 : f 1 = f 3
  all_goals simp_all [tupleAnchor,eq_comm]

theorem tupleAnchor_repeat_13 (f : Fin 4 → P) (rho : ℚ) (h : f 1 = f 3) :
    tupleAnchor f rho = if tripleInjective f 1 then 1 else 0 := by
  simp only [tripleInjective_one]
  by_cases h01 : f 0 = f 1 <;> by_cases h02 : f 0 = f 2 <;> by_cases h12 : f 1 = f 2
  all_goals simp_all [tupleAnchor,eq_comm]
end Nanuq.PortPatterns

namespace Nanuq.Source.RootedBinary
open scoped Classical BigOperators
open Nanuq.PortPatterns
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)

noncomputable def actualTupleMean (v : Fin 4 → X) : ℚ :=
  if h : Function.Injective v then N.rawQuartetMean ⟨v,h⟩ else 0

noncomputable def actualTupleAnchor (v : Fin 4 → X) : ℚ := tupleAnchor v (N.actualTupleMean v)

theorem actual_triple_indicator_sum (v : Fin 4 → X) (i : Fin 4) :
    (if tripleInjective v i then (1 : ℚ) else 0) =
      ∑ b : {b : N.graph.Blob // N.NonleafBlob b},
        if tripleInjective (fun j => N.blobProjection b.val b.property (v j)) i then 1 else 0 := by
  by_cases hi : tripleInjective v i
  · let q3 : Fin 3 ↪ X := ⟨fun j => v (omitTriple i j),hi⟩
    obtain ⟨b,⟨hb,hbi⟩,hu⟩ := N.existsUnique_three_way_blob q3
    have he (c : {b : N.graph.Blob // N.NonleafBlob b}) :
        tripleInjective (fun j => N.blobProjection c.val c.property (v j)) i ↔ c = ⟨b,hb⟩ := by
      constructor
      · intro hc
        exact Subtype.ext (hu c.val ⟨c.property,hc⟩)
      · intro hc
        subst c
        exact hbi
    simp_rw [he]
    simp [hi]
  · have hz (b : {b : N.graph.Blob // N.NonleafBlob b}) :
        ¬ tripleInjective (fun j => N.blobProjection b.val b.property (v j)) i := by
      intro h
      apply hi
      intro j k hjk
      exact h (congrArg (N.blobProjection b.val b.property) hjk)
    simp [hi,hz]

theorem actual_full_anchor_identity (v : Fin 4 → X) :
    N.actualTupleAnchor v =
      ∑ b : {b : N.graph.Blob // N.NonleafBlob b}, N.actualBlobTupleAnchor b.val b.property v := by
  classical
  unfold actualTupleAnchor actualBlobTupleAnchor
  by_cases h01 : v 0 = v 1
  · have hl (b : {b : N.graph.Blob // N.NonleafBlob b}) :
        N.blobProjection b.val b.property (v 0) = N.blobProjection b.val b.property (v 1) :=
      congrArg (N.blobProjection b.val b.property) h01
    simp [tupleAnchor,h01,hl]
  by_cases h23 : v 2 = v 3
  · have hl (b : {b : N.graph.Blob // N.NonleafBlob b}) :
        N.blobProjection b.val b.property (v 2) = N.blobProjection b.val b.property (v 3) :=
      congrArg (N.blobProjection b.val b.property) h23
    simp [tupleAnchor,h23,hl]
  by_cases h02 : v 0 = v 2
  · rw [tupleAnchor_repeat_02 v _ h02]
    have hl (b : {b : N.graph.Blob // N.NonleafBlob b}) :=
      tupleAnchor_repeat_02 (fun j => N.blobProjection b.val b.property (v j))
        (N.actualBlobTupleMean b.val b.property v) (congrArg (N.blobProjection b.val b.property) h02)
    simp_rw [hl]
    exact N.actual_triple_indicator_sum v 0
  by_cases h03 : v 0 = v 3
  · rw [tupleAnchor_repeat_03 v _ h03]
    have hl (b : {b : N.graph.Blob // N.NonleafBlob b}) :=
      tupleAnchor_repeat_03 (fun j => N.blobProjection b.val b.property (v j))
        (N.actualBlobTupleMean b.val b.property v) (congrArg (N.blobProjection b.val b.property) h03)
    simp_rw [hl]
    exact N.actual_triple_indicator_sum v 0
  by_cases h12 : v 1 = v 2
  · rw [tupleAnchor_repeat_12 v _ h12]
    have hl (b : {b : N.graph.Blob // N.NonleafBlob b}) :=
      tupleAnchor_repeat_12 (fun j => N.blobProjection b.val b.property (v j))
        (N.actualBlobTupleMean b.val b.property v) (congrArg (N.blobProjection b.val b.property) h12)
    simp_rw [hl]
    exact N.actual_triple_indicator_sum v 1
  by_cases h13 : v 1 = v 3
  · rw [tupleAnchor_repeat_13 v _ h13]
    have hl (b : {b : N.graph.Blob // N.NonleafBlob b}) :=
      tupleAnchor_repeat_13 (fun j => N.blobProjection b.val b.property (v j))
        (N.actualBlobTupleMean b.val b.property v) (congrArg (N.blobProjection b.val b.property) h13)
    simp_rw [hl]
    exact N.actual_triple_indicator_sum v 1
  have hi : Function.Injective v := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  rw [tupleAnchor_injective v _ hi]
  have hm : N.actualTupleMean v = N.rawQuartetMean ⟨v,hi⟩ := by simp [actualTupleMean,hi]
  rw [hm]
  exact N.actual_distinct_anchor_identity ⟨v,hi⟩
end Nanuq.Source.RootedBinary

#print axioms Nanuq.Source.RootedBinary.actual_full_anchor_identity
