import KnownFiniteChannel
import ActualSourceCorruptionClasses

/-!
CLOUD-G6-SOL-ULTRA-20261007. Compiler UNCHECKED; outside179.
Bind ONE fixed finite channel to the actual native initialized/completed law
and derive the output wrong image from the SAME original-source witnesses.
No biological assay/channel identity, inverse or effective tables are proved.
-/
namespace CloudG6.ActualKnownFiniteChannel

open MeasureTheory CloudG6.ActualSourceCorruptionClasses
open UnifiedLean.G6.FiniteProbability UnifiedLean.G6.CorruptionClasses
open UnifiedLean.G6.KnownFiniteChannel
open scoped Classical
universe u v w x y z t
variable {Copy : Type w} {X : Type x} {Tag : Type y} {O : Type z} {B : Type t}
variable [Fintype Copy] [DecidableEq Copy] [Fintype X]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
variable [Fintype O] [Fintype B] {sample : Copy → X}

noncomputable def channelNativeLaw (mode : Bool) (bin : ℝ → Tag)
    (hbin : Measurable bin) (reader : NativeObservedRecord Copy Tag → O)
    (K : O → PMF B) (s : OriginalParameters.{u,v,w,x} Copy X sample) : PMF B :=
  (nativeLaw mode bin hbin reader s).bind K

/-- Labels are derived from each actual original graph; no output-law label
or hidden source identifier is exposed to the fixed observation channel. -/
noncomputable def wrongChannelNativeImage {Answer : Type*}
    (answer : OriginalTarget X → Answer) (wanted : Answer) (mode : Bool)
    (bin : ℝ → Tag) (hbin : Measurable bin)
    (reader : NativeObservedRecord Copy Tag → O) (K : O → PMF B) : Set (PMF B) :=
  {q | ∃ s : OriginalParameters.{u,v,w,x} Copy X sample,
    answer (sourceTarget s) ≠ wanted ∧ channelNativeLaw mode bin hbin reader K s = q}

theorem wrongChannelNativeImage_eq {Answer : Type*}
    (answer : OriginalTarget X → Answer) (wanted : Answer) (mode : Bool)
    (bin : ℝ → Tag) (hbin : Measurable bin)
    (reader : NativeObservedRecord Copy Tag → O) (K : O → PMF B) :
    wrongChannelNativeImage (sample := sample) answer wanted mode bin hbin reader K =
      channelImage K (wrongNativeImage (sample := sample) answer wanted mode bin hbin reader) := by
  ext q
  constructor
  · rintro ⟨s, hs, hsq⟩
    exact ⟨nativeLaw mode bin hbin reader s, ⟨s, hs, rfl⟩, hsq⟩
  · rintro ⟨p, ⟨s, hs, rfl⟩, hpq⟩
    exact ⟨s, hs, hpq⟩

theorem actual_channel_native_contraction (mode : Bool) (bin : ℝ → Tag)
    (hbin : Measurable bin) (reader : NativeObservedRecord Copy Tag → O)
    (K : O → PMF B) (s r : OriginalParameters.{u,v,w,x} Copy X sample) :
    pmfTV (channelNativeLaw mode bin hbin reader K s)
      (channelNativeLaw mode bin hbin reader K r) ≤
      pmfTV (nativeLaw mode bin hbin reader s) (nativeLaw mode bin hbin reader r) :=
  pmfTV_bind_contraction _ _ K

theorem actual_wrong_closure_boundary_pushes {Answer : Type*}
    (answer : OriginalTarget X → Answer) (s : OriginalParameters.{u,v,w,x} Copy X sample)
    (mode : Bool) (bin : ℝ → Tag) (hbin : Measurable bin)
    (reader : NativeObservedRecord Copy Tag → O) (K : O → PMF B) (beta : ℝ)
    (hboundary : ∃ q ∈ tvClosure (wrongNativeImage (sample := sample) answer
      (answer (sourceTarget s)) mode bin hbin reader),
      pmfTV (nativeLaw mode bin hbin reader s) q ≤ 2 * beta) :
    ∃ q ∈ tvClosure (wrongChannelNativeImage (sample := sample) answer
      (answer (sourceTarget s)) mode bin hbin reader K),
      pmfTV (channelNativeLaw mode bin hbin reader K s) q ≤ 2 * beta := by
  rw [wrongChannelNativeImage_eq]
  exact wrong_closure_boundary_pushes K _ _ beta hboundary

theorem actual_channel_separation_requires_clean {Answer : Type*}
    (answer : OriginalTarget X → Answer) (s : OriginalParameters.{u,v,w,x} Copy X sample)
    (mode : Bool) (bin : ℝ → Tag) (hbin : Measurable bin)
    (reader : NativeObservedRecord Copy Tag → O) (K : O → PMF B) (beta : ℝ)
    (houtput : allCorruptionsSeparated (channelNativeLaw mode bin hbin reader K s)
      (tvClosure (wrongChannelNativeImage (sample := sample) answer
        (answer (sourceTarget s)) mode bin hbin reader K)) beta) :
    allCorruptionsSeparated (nativeLaw mode bin hbin reader s)
      (tvClosure (wrongNativeImage (sample := sample) answer
        (answer (sourceTarget s)) mode bin hbin reader)) beta := by
  rw [wrongChannelNativeImage_eq] at houtput
  exact channel_separation_requires_clean_separation K _ _ beta houtput

#print axioms wrongChannelNativeImage_eq
#print axioms actual_channel_native_contraction
#print axioms actual_wrong_closure_boundary_pushes
#print axioms actual_channel_separation_requires_clean

end CloudG6.ActualKnownFiniteChannel
