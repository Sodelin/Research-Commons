import RankGaps
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Pairwise

/-! UNCOMPILED. Convert the derived actual sorted-parameter gaps to the
unchanged restriction receiver's exact CyclicGap predicate. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.Restriction

/-- Injectivity strengthens the derived weak sorting relation to strict ranks. -/
theorem sorted_rank_strictMono {T : Type*} (xs : List T) (θ : T → ℝ)
    (hnd : xs.Nodup) (hinj : Function.Injective θ)
    (hsort : xs.Pairwise (fun a c => θ a≤θ c)) :
    StrictMono (fun i : Fin xs.length => θ (xs.get i)) := by
  intro i j hij
  have hle : θ (xs.get i)≤θ (xs.get j) :=
    (List.pairwise_iff_getElem.mp hsort) i.val j.val i.isLt j.isLt hij
  apply lt_of_le_of_ne hle
  intro heq
  have hij' : i=j := hnd.injective_get (hinj heq)
  exact (ne_of_lt hij) hij'

/-- A label map is allowed to repeat. The ordering is on distinct actual
occurrences, and only then mapped into the finite Nat-label receiver. -/
theorem sorted_empty_gap_cyclicGap {T : Type*} (xs : List T) (θ : T → ℝ)
    (label : T → Nat) (hnd : xs.Nodup) (hinj : Function.Injective θ)
    (hsort : xs.Pairwise (fun a c => θ a≤θ c))
    (a c : T) (ha : a∈xs) (hc : c∈xs) (hac : θ a<θ c)
    (hgap : (∀ w, ¬(θ a<θ w ∧ θ w<θ c)) ∨
      (∀ w, ¬(θ w<θ a ∨ θ c<θ w))) :
    CyclicGap (xs.map label) (label a) (label c) ∨
      CyclicGap (xs.map label) (label c) (label a) := by
  classical
  let ia : Fin xs.length := ⟨xs.idxOf a,List.idxOf_lt_length_iff.mpr ha⟩
  let ic : Fin xs.length := ⟨xs.idxOf c,List.idxOf_lt_length_iff.mpr hc⟩
  have hia : xs.get ia=a := List.getElem_idxOf ia.isLt
  have hic : xs.get ic=c := List.getElem_idxOf ic.isLt
  let q : Fin xs.length → ℝ := fun i => θ (xs.get i)
  have hq : StrictMono q := sorted_rank_strictMono xs θ hnd hinj hsort
  have hiac : ia<ic := hq.lt_iff_lt.mp (by simpa only [q,hia,hic] using hac)
  have hg : (∀ w, ¬(q ia<q w ∧ q w<q ic)) ∨
      (∀ w, ¬(q w<q ia ∨ q ic<q w)) := by
    rcases hgap with h | h
    · left; intro w; simpa only [q,hia,hic] using h (xs.get w)
    · right; intro w; simpa only [q,hia,hic] using h (xs.get w)
  have h := rank_cyclic_gap q hq ia ic hiac hg
  let atLabel : Nat → Nat := fun i => label ((xs[i]?).getD a)
  have hmap : (List.range xs.length).map atLabel=xs.map label := by
    apply List.ext_getElem
    · simp
    · intro i hi hj
      have hi' : i<xs.length := by simpa using hi
      simp only [List.getElem_map,List.getElem_range,atLabel,
        List.getElem?_eq_getElem hi',Option.getD_some]
  have hla : atLabel ia.val=label a := by
    simp only [atLabel,List.getElem?_eq_getElem ia.isLt,Option.getD_some]
    exact congrArg label hia
  have hlc : atLabel ic.val=label c := by
    simp only [atLabel,List.getElem?_eq_getElem ic.isLt,Option.getD_some]
    exact congrArg label hic
  rcases h with h | h
  · left
    simpa only [hmap,hla,hlc] using gap_map (List.range xs.length) atLabel ia.val ic.val h
  · right
    simpa only [hmap,hla,hlc] using gap_map (List.range xs.length) atLabel ic.val ia.val h

#print axioms sorted_rank_strictMono
#print axioms sorted_empty_gap_cyclicGap
end Nanuq.Restriction
