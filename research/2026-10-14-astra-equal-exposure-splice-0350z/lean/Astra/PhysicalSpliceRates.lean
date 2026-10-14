import G1SplicedSourceAdmission
import G7OriginalSurvivalCoverage

/-!
# Positive physical rates on the existing two-port graph splice

Proposed integration source, not yet compiled or admitted. This constructs a
positive scalar rate from the original path EXPOSURE and the actual endpoint
calendar span. Retained edge rates and the ancestral rate stay literal.
It proves no bank, protected-ID, observation-law or representative theorem.
-/
namespace Astra.PhysicalSpliceRates

set_option backward.isDefEq.respectTransparency false

open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativePairClockLaw
open G1ActualTwoPortBlob G1BigonSpliceGraph G1SplicedSourceAdmission
open GProgram.G7.OriginalSurvivalCoverage
open scoped Classical

variable {V E X : Type*}
variable [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]

noncomputable def collapsedDuration (N : RootedBinary V E X)
    (C : Calendar N.graph) (b : N.graph.Blob) (A : ActualBlobBigon N b) : ℝ :=
  C.age (N.graph.source A.entry) - C.age (N.graph.target A.child)

lemma collapsedDuration_pos (N : RootedBinary V E X)
    (C : Calendar N.graph) (b : N.graph.Blob) (A : ActualBlobBigon N b) :
    0 < collapsedDuration N C b A := by
  have he := C.edge_older A.entry
  have hp := C.edge_older A.fragment.parents.parent0
  have hd := C.edge_older A.child
  rw [A.entry_target] at he
  rw [show N.graph.source A.fragment.parents.parent0 = A.fragment.upper from
    A.fragment.arm_sources false, A.fragment.parents.target0] at hp
  rw [A.child_source] at hd
  exact sub_pos.mpr (hd.trans (hp.trans he))

noncomputable def collapsedExposure (N : RootedBinary V E X)
    (C : Calendar N.graph) (r : PositivePairRates E)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) : ℝ :=
  exposure N C r A.entry + exposure N C r A.fragment.parents.parent0 +
    exposure N C r A.child

lemma collapsedExposure_pos (N : RootedBinary V E X)
    (C : Calendar N.graph) (r : PositivePairRates E)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) :
    0 < collapsedExposure N C r b A :=
  add_pos (add_pos (exposure_pos N C r A.entry)
    (exposure_pos N C r A.fragment.parents.parent0))
    (exposure_pos N C r A.child)

/-- This rate construction makes no law-preservation claim when the arms differ.
The separate equal-arm premise below identifies the same exposure for either
original arm. No replacement edge rate is identified with a calendar duration. -/
noncomputable def splicedRates (N : RootedBinary V E X)
    (C : Calendar N.graph) (r : PositivePairRates E)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) :
    PositivePairRates (SplicedEdge N b A) where
  edge
    | .inl e => r.edge e.val
    | .inr _ => collapsedExposure N C r b A / collapsedDuration N C b A
  edge_pos e := by
    cases e with
    | inl e => exact r.edge_pos e.val
    | inr u =>
      exact div_pos (collapsedExposure_pos N C r b A) (collapsedDuration_pos N C b A)
  ancestral := r.ancestral
  ancestral_pos := r.ancestral_pos

lemma retained_rate (N : RootedBinary V E X)
    (C : Calendar N.graph) (r : PositivePairRates E)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) (e : RetainedEdge N b A) :
    (splicedRates N C r b A).edge (.inl e) = r.edge e.val := rfl

lemma ancestral_rate (N : RootedBinary V E X)
    (C : Calendar N.graph) (r : PositivePairRates E)
    (b : N.graph.Blob) (A : ActualBlobBigon N b) :
    (splicedRates N C r b A).ancestral = r.ancestral := rfl

lemma new_edge_duration (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (A : ActualBlobBigon N b) (C : Calendar N.graph) :
    (splicedCalendar N hc b hb A C).age
        ((splicedNetwork N hc b hb A).graph.source (.inr ())) -
      (splicedCalendar N hc b hb A C).age
        ((splicedNetwork N hc b hb A).graph.target (.inr ())) =
      collapsedDuration N C b A := rfl

lemma retained_exposure (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (A : ActualBlobBigon N b) (C : Calendar N.graph)
    (r : PositivePairRates E) (e : RetainedEdge N b A) :
    exposure (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
        (splicedRates N C r b A) (.inl e) = exposure N C r e.val := rfl

lemma new_edge_exposure (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (A : ActualBlobBigon N b) (C : Calendar N.graph) (r : PositivePairRates E) :
    exposure (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
        (splicedRates N C r b A) (.inr ()) = collapsedExposure N C r b A := by
  change (collapsedExposure N C r b A / collapsedDuration N C b A) *
    collapsedDuration N C b A = collapsedExposure N C r b A
  exact div_mul_cancel₀ _ (ne_of_gt (collapsedDuration_pos N C b A))

lemma retained_survival (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (A : ActualBlobBigon N b) (C : Calendar N.graph)
    (r : PositivePairRates E) (e : RetainedEdge N b A) :
    survival (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
        (splicedRates N C r b A) (.inl e) = survival N C r e.val := by
  rw [survival, survival, retained_exposure]

lemma new_edge_survival (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (A : ActualBlobBigon N b) (C : Calendar N.graph) (r : PositivePairRates E) :
    survival (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
        (splicedRates N C r b A) (.inr ()) =
      survival N C r A.entry * survival N C r A.fragment.parents.parent0 *
        survival N C r A.child := by
  simp only [survival, new_edge_exposure, collapsedExposure, neg_add_rev, Real.exp_add]
  ac_rfl

/-- Original false/true arm order is retained. Equal arm exposure is an actual
scalar premise, not a desired forest-law equality or a bounded target witness. -/
lemma new_edge_exposure_either_arm (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
    (A : ActualBlobBigon N b) (C : Calendar N.graph) (r : PositivePairRates E)
    (heq : exposure N C r A.fragment.parents.parent0 =
      exposure N C r A.fragment.parents.parent1) (arm : Bool) :
    exposure (splicedNetwork N hc b hb A) (splicedCalendar N hc b hb A C)
        (splicedRates N C r b A) (.inr ()) =
      exposure N C r A.entry +
        (if arm then exposure N C r A.fragment.parents.parent1
         else exposure N C r A.fragment.parents.parent0) + exposure N C r A.child := by
  rw [new_edge_exposure]
  cases arm <;> simp [collapsedExposure, heq]

-- Requests for the future actual type/axiom audit; no output is claimed here.
#check splicedRates
#check new_edge_exposure_either_arm
#print axioms collapsedDuration_pos
#print axioms collapsedExposure_pos
#print axioms retained_rate
#print axioms ancestral_rate
#print axioms new_edge_duration
#print axioms retained_exposure
#print axioms new_edge_exposure
#print axioms retained_survival
#print axioms new_edge_survival
#print axioms new_edge_exposure_either_arm

end Astra.PhysicalSpliceRates
