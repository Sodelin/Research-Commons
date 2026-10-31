import ActualOccurrenceQuartets
import LabelWitness
import GraphLeaves
import Mathlib.Tactic.FinCases

/-! UNCOMPILED exact terminal-occurrence bridge. Internal labels cannot
supply phantom quartet witnesses; completeness comes from the actual source. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.Source.RootedBinary
open scoped Classical
open Nanuq.Quartet Nanuq.GraphReceiver
variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X)
variable (hl : ∀ e, N.graph.IsHybrid (N.graph.source e) → ∃ x, N.graph.target e=N.leaf x)
variable (code : X ↪ Nat) (lab : N.OpenedHybridVertex → Nat)
variable (hlab : ∀ t, lab (N.openedTipVertex t)=code (N.openedTipLabel hl t))

include hlab

theorem labelled_quartet_iff_tip_witness (a b c d : X) :
    LabelledQuartet (N.openedHybridGraph hl) lab (code a) (code b) (code c) (code d) ↔
      ∃ w x y z : N.OpenedTip,
        (N.openedTipLabel hl w=a ∧ N.openedTipLabel hl x=b ∧
          N.openedTipLabel hl y=c ∧ N.openedTipLabel hl z=d) ∧
        (N.openedHybridGraph hl).HasQuartet (N.openedTipVertex w) (N.openedTipVertex x)
          (N.openedTipVertex y) (N.openedTipVertex z) := by
  constructor
  · rintro ⟨w,x,y,z,⟨hw,hx,hy,hz⟩,⟨lw,lx,ly,lz⟩,hq⟩
    obtain ⟨w',rfl⟩ := ((N.actualOpenedRootedSource hl).leaf_iff_outDegree_zero w).mpr hw
    obtain ⟨x',rfl⟩ := ((N.actualOpenedRootedSource hl).leaf_iff_outDegree_zero x).mpr hx
    obtain ⟨y',rfl⟩ := ((N.actualOpenedRootedSource hl).leaf_iff_outDegree_zero y).mpr hy
    obtain ⟨z',rfl⟩ := ((N.actualOpenedRootedSource hl).leaf_iff_outDegree_zero z).mpr hz
    exact ⟨w',x',y',z',⟨code.injective ((hlab _).symm.trans lw),
      code.injective ((hlab _).symm.trans lx),code.injective ((hlab _).symm.trans ly),
      code.injective ((hlab _).symm.trans lz)⟩,hq⟩
  · rintro ⟨w,x,y,z,⟨hw,hx,hy,hz⟩,hq⟩
    exact ⟨N.openedTipVertex w,N.openedTipVertex x,N.openedTipVertex y,N.openedTipVertex z,
      ⟨(N.opened_tip_degrees hl w).2,(N.opened_tip_degrees hl x).2,
        (N.opened_tip_degrees hl y).2,(N.opened_tip_degrees hl z).2⟩,
      ⟨(hlab _).trans (congrArg code hw),(hlab _).trans (congrArg code hx),
        (hlab _).trans (congrArg code hy),(hlab _).trans (congrArg code hz)⟩,hq⟩

theorem actual_displayed_iff_labelled (q : Fin 4 ↪ X) (r : Resolution) :
    r∈N.rawDisplayedQuartets q ↔
      match r with
      | .xy_zw => LabelledQuartet (N.openedHybridGraph hl) lab (code (q 0)) (code (q 1)) (code (q 2)) (code (q 3))
      | .xz_yw => LabelledQuartet (N.openedHybridGraph hl) lab (code (q 0)) (code (q 2)) (code (q 1)) (code (q 3))
      | .xw_yz => LabelledQuartet (N.openedHybridGraph hl) lab (code (q 0)) (code (q 3)) (code (q 1)) (code (q 2)) := by
  rw [N.actual_displayed_iff_occurrence_resolves hl q r]
  have mk (t : Fin 4 → N.OpenedTip) (ht : ∀ i, N.openedTipLabel hl (t i)=q i) :
      Function.Injective t := by
    intro i j hij
    exact q.injective ((ht i).symm.trans ((congrArg (N.openedTipLabel hl) hij).trans (ht j)))
  cases r <;> dsimp only <;> rw [N.labelled_quartet_iff_tip_witness hl code lab hlab]
  · constructor
    · rintro ⟨t,ht,hq⟩
      exact ⟨t 0,t 1,t 2,t 3,⟨ht 0,ht 1,ht 2,ht 3⟩,hq⟩
    · rintro ⟨w,x,y,z,⟨hw,hx,hy,hz⟩,hq⟩
      have ht : ∀ i, N.openedTipLabel hl (![w,x,y,z] i)=q i := by intro i; fin_cases i <;> simp_all
      exact ⟨⟨![w,x,y,z],mk _ ht⟩,ht,hq⟩
  · constructor
    · rintro ⟨t,ht,hq⟩
      exact ⟨t 0,t 2,t 1,t 3,⟨ht 0,ht 2,ht 1,ht 3⟩,hq⟩
    · rintro ⟨w,x,y,z,⟨hw,hx,hy,hz⟩,hq⟩
      have ht : ∀ i, N.openedTipLabel hl (![w,y,x,z] i)=q i := by intro i; fin_cases i <;> simp_all
      exact ⟨⟨![w,y,x,z],mk _ ht⟩,ht,hq⟩
  · constructor
    · rintro ⟨t,ht,hq⟩
      exact ⟨t 0,t 3,t 1,t 2,⟨ht 0,ht 3,ht 1,ht 2⟩,hq⟩
    · rintro ⟨w,x,y,z,⟨hw,hx,hy,hz⟩,hq⟩
      have ht : ∀ i, N.openedTipLabel hl (![w,y,z,x] i)=q i := by intro i; fin_cases i <;> simp_all
      exact ⟨⟨![w,y,z,x],mk _ ht⟩,ht,hq⟩

#print axioms actual_displayed_iff_labelled
end Nanuq.Source.RootedBinary
