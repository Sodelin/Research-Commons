import CyclicBlocks
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin

/-! UNCOMPILED. The finite cardinality bridge counts ORIGINAL occurrences,
not distinct Nat codes. Its source application must use an injective code. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.Restriction
open scoped Classical

/-- An exhaustive Nodup occurrence list counts exactly the original finite fibre. -/
theorem exhaustive_map_count {T : Type*} [Fintype T] (xs : List T)
    (hnd : xs.Nodup) (hall : ∀ t, t∈xs) (lab : T → Nat) (y : Nat) :
    (xs.map lab).count y=(Finset.univ.filter (fun t => lab t=y)).card := by
  classical
  have hfin : xs.toFinset=Finset.univ := by ext t; simp [hall t]
  calc
    (xs.map lab).count y = xs.countP (fun t => decide (lab t=y)) := by
      simp only [List.count_eq_countP,List.countP_map]
      apply List.countP_congr
      intro t ht
      simp
    _ = (Finset.univ.filter (fun t => lab t=y)).card := by
      symm
      simpa only [hfin] using hnd.card_eq_countP (P:=fun t => lab t=y)

/-- The block receiver derives its multiplicities from original fibres and
retains only a zero/one cyclic rotation of the supplied occurrence list. -/
theorem finite_label_blocks {T L : Type*} [Fintype T] [Fintype L]
    (xs : List T) (hnd : xs.Nodup) (hall : ∀ t, t∈xs)
    (label : T → L) (hsurj : Function.Surjective label)
    (code : L → Nat) (hinj : Function.Injective code)
    (hmult : ∀ x, (Finset.univ.filter (fun t => label t=x)).card≤2)
    (htwo : 2≤Fintype.card L)
    (hgaps : ∀ a c, a≠c → label a=label c →
      CyclicGap (xs.map (fun t => code (label t))) (code (label a)) (code (label a))) :
    ∃ k base dup, k≤1 ∧ base.Nodup ∧
      (xs.rotate k).map (fun t => code (label t))=blocks base dup := by
  classical
  let lab : T → Nat := fun t => code (label t)
  have hcount : ∀ y, (xs.map lab).count y≤2 := by
    intro y
    rw [exhaustive_map_count xs hnd hall lab y]
    by_cases hy : ∃ x, code x=y
    · obtain ⟨x,rfl⟩ := hy
      have he : (Finset.univ.filter (fun t => lab t=code x))=
          (Finset.univ.filter (fun t => label t=x)) := by
        ext t
        simp [lab,hinj.eq_iff]
      rw [he]
      exact hmult x
    · have he : (Finset.univ.filter (fun t => lab t=y))=∅ := by
        apply Finset.eq_empty_iff_forall_notMem.mpr
        intro t ht
        exact hy ⟨label t,(Finset.mem_filter.mp ht).2⟩
      rw [he]
      simp
  have hdist : ∃ a∈xs.map lab, ∃ c∈xs.map lab, a≠c := by
    have hc : 1<(Finset.univ : Finset L).card := by simpa using (show 1<Fintype.card L by omega)
    obtain ⟨a,ha,c,hc,hac⟩ := Finset.one_lt_card.mp hc
    obtain ⟨ta,hta⟩ := hsurj a
    obtain ⟨tc,htc⟩ := hsurj c
    refine ⟨code a,List.mem_map.mpr ⟨ta,hall ta,?_⟩,
      code c,List.mem_map.mpr ⟨tc,hall tc,?_⟩,fun h => hac (hinj h)⟩
    · exact congrArg code hta
    · exact congrArg code htc
  have hpairs : ∀ y, (xs.map lab).count y=2 → CyclicGap (xs.map lab) y y := by
    intro y hy
    rw [exhaustive_map_count xs hnd hall lab y] at hy
    obtain ⟨a,ha,c,hc,hac⟩ := Finset.one_lt_card.mp (show
      1<(Finset.univ.filter (fun t => lab t=y)).card by omega)
    have hay : lab a=y := (Finset.mem_filter.mp ha).2
    have hcy : lab c=y := (Finset.mem_filter.mp hc).2
    have hl : label a=label c := hinj (hay.trans hcy.symm)
    have hg := hgaps a c hac hl
    simpa only [← hay] using hg
  obtain ⟨k,base,dup,hk,hnb,he⟩ := cyclic_blocks_factor (xs.map lab) hcount hdist hpairs
  exact ⟨k,base,dup,hk,hnb,by simpa only [List.map_rotate] using he⟩

#print axioms exhaustive_map_count
#print axioms finite_label_blocks
end Nanuq.Restriction
