import Astra.PhysicalSpliceProtectedCoordinates
import Astra.PhysicalSpliceConfiguration
import Mathlib.Logic.Function.Basic

/-! Source-only external-mask interpretation for the exact retained labels.
The same external table is extended by none off the marked hybrid image.
This discharges an encoding identity, not expanded dependency eligibility,
an output law, a finite reduction or a representative bound. -/
namespace Astra.PhysicalSpliceExternalMasks

open Nanuq.Source GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.OriginalFixedIDControls
open G1ActualTwoPortBlob G1SplicedSourceAdmission
open Astra.PhysicalSpliceRegistry Astra.PhysicalSpliceProtectedCoordinates
open Astra.PhysicalSpliceConfiguration
open scoped Classical

/-- Interpret a fixed external table on labelled sites; every other site is
natural. This uses the existing extension operation, with no extra parameter. -/
noncomputable def labelMask {Label Site : Type*}
    (mark : Label → Site) (table : Label → Option Bool) : Site → Option Bool :=
  Function.extend mark table (fun _ => none)

theorem labelMask_at_label {Label Site : Type*}
    (mark : Label → Site) (hinj : Function.Injective mark)
    (table : Label → Option Bool) (a : Label) :
    labelMask mark table (mark a) = table a :=
  hinj.extend_apply table (fun _ => none) a

theorem labelMask_off_labels {Label Site : Type*}
    (mark : Label → Site) (table : Label → Option Bool) (s : Site)
    (h : ¬ ∃ a, mark a = s) : labelMask mark table s = none :=
  Function.extend_apply' table (fun _ => none) s h

/-- An injection-compatible external frame gives precisely the same mask
after restriction, including every none/false/true entry. -/
theorem labelMask_restrict {Label Old New : Type*}
    (J : New ↪ Old) (oldMark : Label → Old) (newMark : Label → New)
    (hinj : Function.Injective oldMark)
    (hframe : ∀ a, J (newMark a) = oldMark a) (table : Label → Option Bool) :
    (fun k => labelMask oldMark table (J k)) = labelMask newMark table := by
  have hnew : Function.Injective newMark := by
    intro a c h
    apply hinj
    rw [← hframe a, ← hframe c, h]
  funext k
  by_cases hk : ∃ a, newMark a = k
  · obtain ⟨a, rfl⟩ := hk
    rw [hframe a, labelMask_at_label oldMark hinj, labelMask_at_label newMark hnew]
  · have ho : ¬ ∃ a, oldMark a = J k := by
      rintro ⟨a, ha⟩
      exact hk ⟨a, J.injective ((hframe a).trans ha)⟩
    rw [labelMask_off_labels oldMark table (J k) ho,
      labelMask_off_labels newMark table k hk]

variable {V E X PH : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

/-- The actual constructed surviving-hybrid frame interprets the same fixed
external table before and after the splice. The representative tuple and
frame are chosen before the universally quantified table. -/
theorem splice_external_mask (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (mark : PH → Hybrid N) (hinj : Function.Injective mark)
    (avoid : ∀ a, mark a ≠ removedHybrid N b A) (table : PH → Option Bool) :
    restrictMask N hc b hb A (labelMask mark table) =
      labelMask (hybridMap N hc b hb A mark avoid) table := by
  exact labelMask_restrict (retainedHybrid N hc b hb A) mark
    (hybridMap N hc b hb A mark avoid) hinj
    (hybridMap_original N hc b hb A mark avoid) table

/-- All whole configurations keep the same external row table. No PMF is
altered, and the statement is not a product of sitewise marginal laws. -/
theorem splice_external_masks {Config : Type*}
    (N : RootedBinary V E X) (hc : CutChild N)
    (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root) (A : ActualBlobBigon N b)
    (mark : PH → Hybrid N) (hinj : Function.Injective mark)
    (avoid : ∀ a, mark a ≠ removedHybrid N b A)
    (tables : Config → PH → Option Bool) :
    restrictMasks N hc b hb A (fun cfg => labelMask mark (tables cfg)) =
      fun cfg => labelMask (hybridMap N hc b hb A mark avoid) (tables cfg) := by
  funext cfg
  exact splice_external_mask N hc b hb A mark hinj avoid (tables cfg)

-- Future actual type/axiom requests, not execution receipts.
#check splice_external_mask
#check splice_external_masks
#print axioms labelMask_at_label
#print axioms labelMask_off_labels
#print axioms labelMask_restrict
#print axioms splice_external_mask
#print axioms splice_external_masks

end Astra.PhysicalSpliceExternalMasks
