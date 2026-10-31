import NamedBoundaryIncoming
import Schoenflies.Subarc
import Schoenflies.Concatenate

/-! UNCOMPILED. Literal original incoming half-edge tails, not an inferred
boundary interval between two isolated midpoint coordinates. -/
set_option debug.skipKernelTC false
noncomputable section
namespace Nanuq.OpenedCore
open Nanuq.Source Nanuq.RawBlock Nanuq.RawBlockSupplier
open G1OuterLabelledMultigraphCurves NanuqFaithfulSupplierDrawing Set Schoenflies
open Nanuq.CapCurves
open scoped Graph Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V]
variable (N : RootedBinary V E X) (D : PlanarCurves N.graph) (b : N.graph.Blob)

def incomingTail (e : CoreTip N b) : Set Schoenflies.Plane :=
  curve D e.val.val '' Icc (1/2 : ℝ) 1

private theorem half_curve (e : E) : curve D e (1/2 : ℝ)=coordinates (D.arc e oneHalf) := by
  simpa only [oneHalf] using curve_on_interval D e oneHalf

theorem incomingTail_arc (e : CoreTip N b) :
    IsArcBetween (incomingTail N D b e)
      (coordinates (D.arc e.val.val oneHalf))
      (coordinates (D.point (N.graph.target e.val.val))) := by
  have hd := (isDrawing D).edge_param (show e.val.val∈E(graph D) from Set.mem_univ _)
  have h := isArcBetween_subarc_of_injOn_I hd.1 hd.2.1
    (show (1/2:ℝ)∈unitInterval by norm_num [unitInterval])
    (show (1:ℝ)∈unitInterval by norm_num [unitInterval])
    (show (1/2:ℝ)≠1 by norm_num)
  rw [uIcc_of_le (show (1/2:ℝ)≤1 by norm_num),half_curve N D e.val.val,curve_one] at h
  exact h

/-- No core vertex occurs in an incoming tail except its own midpoint tip.
The common hybrid is absent from the core; ordinary attachments are nonhybrid. -/
theorem incoming_tail_parameter_only_core_tip (e : CoreTip N b) (v : CoreVertex N b)
    (t : unitInterval) (ht : (1/2:ℝ)≤(t:ℝ))
    (heq : D.arc e.val.val t=corePoint N D b v) : v=Sum.inr e := by
  have ht0 : t≠0 := by
    intro h
    have h' : (t : ℝ) = 0 := congrArg Subtype.val h
    linarith only [ht,h']
  rcases v with v | f
  · change D.arc e.val.val t=D.point v.val.val at heq
    rcases D.vertex_incidence e.val.val v.val.val t heq with hs | hd
    · apply False.elim
      apply ht0
      apply D.arc_injective e.val.val
      simpa only [hs,Path.source] using heq
    · exact False.elim (v.property (hd.symm ▸ e.property))
  · change D.arc e.val.val t=D.arc f.val.val oneHalf at heq
    by_cases hef : e.val.val=f.val.val
    · exact congrArg Sum.inr (Subtype.ext (Subtype.ext hef.symm))
    · rcases (D.edge_incidence e.val.val f.val.val hef t oneHalf heq).2 with h0 | h1
      · exact False.elim (half_ne_zero h0)
      · exact False.elim (half_ne_one h1)

theorem incomingTail_only_core_tip (e : CoreTip N b) (v : CoreVertex N b)
    (hv : coordinates (corePoint N D b v)∈incomingTail N D b e) : v=Sum.inr e := by
  obtain ⟨t,ht,heq⟩ := hv
  let tI : unitInterval := ⟨t,by constructor <;> linarith [ht.1,ht.2]⟩
  have hcurve := curve_on_interval D e.val.val tI
  have heq' : coordinates (D.arc e.val.val tI)=coordinates (corePoint N D b v) :=
    hcurve.symm.trans heq
  exact incoming_tail_parameter_only_core_tip N D b e v tI ht.1 (coordinates.injective heq')

theorem incomingTails_meet_only_target (e f : CoreTip N b) (hef : e≠f)
    {z : Schoenflies.Plane} (hz : z∈incomingTail N D b e)
    (hz' : z∈incomingTail N D b f) : z=coordinates (D.point (N.graph.target e.val.val)) := by
  obtain ⟨t,ht,het⟩ := hz
  obtain ⟨u,hu,hfu⟩ := hz'
  let tI : unitInterval := ⟨t,by constructor <;> linarith [ht.1,ht.2]⟩
  let uI : unitInterval := ⟨u,by constructor <;> linarith [hu.1,hu.2]⟩
  have het' : coordinates (D.arc e.val.val tI)=z := (curve_on_interval D e.val.val tI).symm.trans het
  have hfu' : coordinates (D.arc f.val.val uI)=z := (curve_on_interval D f.val.val uI).symm.trans hfu
  have hid : e.val.val≠f.val.val := fun h => hef (Subtype.ext (Subtype.ext h))
  have he := (D.edge_incidence e.val.val f.val.val hid tI uI
    (coordinates.injective (het'.trans hfu'.symm))).1
  rcases he with he | he
  · have hzero : t = (0:ℝ) := congrArg Subtype.val he
    linarith only [hzero,ht.1]
  · simpa only [he,Path.target] using het'.symm

/-- The two incoming tails concatenate at the SAME original hybrid, including
parallel-parent bigons. Their midpoint endpoints remain original occurrences. -/
theorem paired_incoming_tail_arc (e f : CoreTip N b) (hef : e≠f)
    (ht : N.graph.target e.val.val=N.graph.target f.val.val) :
    IsArcBetween (incomingTail N D b e ∪ incomingTail N D b f)
      (coordinates (D.arc e.val.val oneHalf))
      (coordinates (D.arc f.val.val oneHalf)) := by
  have hf := (incomingTail_arc N D b f).reverse
  have hend : coordinates (D.point (N.graph.target f.val.val)) =
      coordinates (D.point (N.graph.target e.val.val)) :=
    congrArg (fun v => coordinates (D.point v)) ht.symm
  rw [hend] at hf
  exact (incomingTail_arc N D b e).concatenate hf
    (fun z hz hz' => incomingTails_meet_only_target N D b e f hef hz hz')

#print axioms incomingTail_only_core_tip
#print axioms paired_incoming_tail_arc
end Nanuq.OpenedCore
