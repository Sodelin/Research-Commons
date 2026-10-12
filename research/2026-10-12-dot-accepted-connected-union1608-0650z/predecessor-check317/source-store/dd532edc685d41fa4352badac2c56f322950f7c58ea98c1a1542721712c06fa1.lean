import G4ActualFirstMeetingEntrance
import G4SpecifiedCombSelectedObservation
import G1UnrankedActualFuture

/-!
# Actual fixed-bank completed comb mass at the physical first meeting

Contributor: dot (OpenAI), 12 October 2026. UNCOMPILED draft.
Reuses the checked physical entrance alternative, exact specified-comb
coefficient, unchanged COMMON completion reader and actual no-loss law.
The conclusion is the original full-calendar completed forest probability,
for one fixed original bank, not a conditional no-merger replacement law.
Exposure is still the original k-copy reference exposure. Cross-arity scaling,
strict positivity for distinct taxa and averaging the original bank are not
assumed or claimed here. No general G4 closure or novelty claim.
-/
namespace DotG4.ActualFirstMeetingCombMass
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1UnrankedActualFuture
open GProgram.G5.SafePrefixRouteBridge GProgram.G4.ActualCommonSelectorSupport
open DotG4.ActualBankFirstMeeting DotG4.ActualFirstMeetingEntrance
open DotG4.ActualColocatedCompletion DotG34.SpecifiedCombEvent
open DotG34.SpecifiedCombSelectedObservation
open scoped Classical NNReal ENNReal BigOperators
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy] [Nonempty Copy]

/-- Validity alone characterizes full-cardinality flatness; no epoch law or
new no-merger premise is required. -/
lemma flat_iff_full_card (s : State V E Copy) (hs : Valid s) :
    (∀ x, s.genealogy (s.ancestor x) = .leaf x) ↔
      s.live.card = Fintype.card Copy := by
  constructor
  · intro hf
    have hu : s.live = Finset.univ := by
      apply Finset.eq_univ_of_forall
      intro x
      have he := singleton_ancestor_eq s hs x (hf x)
      simpa only [he] using hs.ancestor_live x
    rw [hu,Finset.card_univ]
  · intro hc
    have hu := Finset.eq_univ_of_card s.live hc
    have ha : ∀ x, s.ancestor x = x := fun x =>
      hs.representative x (by rw [hu]; exact Finset.mem_univ x)
    intro x
    apply isolated_ancestor_singleton s hs x
    intro y hy
    simpa only [ha] using hy

lemma reader_forest_mass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (b : Copy)
    (target : UnrankedTree Copy) :
    completionReader N r Finset.univ unrankedViewForest s {target} =
      completionTreeLaw N r b (rootRepresentation N s) target := by
  unfold completionReader
  simp only [← actual_unranked_view_forest]
  exact actual_completed_forest_singleton_mass N r (rootRepresentation N s)
    (rootRepresentation_ancestral N s) b target

lemma reader_flat_comb_mass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (b : Copy) (as : List Copy)
    (hf : ∀ x, (state s).genealogy ((state s).ancestor x) = .leaf x)
    (hcover : ∀ x, x = b ∨ x ∈ as) (hnodup : as.Nodup) (hb : b ∉ as)
    (hnonempty : as ≠ []) :
    completionReader N r Finset.univ unrankedViewForest s {toUnranked (comb b as)} =
      ENNReal.ofReal (2^as.length /
        ((Nat.factorial (as.length+1) : ℝ) * (Nat.factorial as.length : ℝ))) := by
  rw [reader_forest_mass N r s b]
  apply actual_flat_specified_comb_probability N r (rootRepresentation N s) b as
    (rootRepresentation_ancestral N s) _ hcover hnodup hb hnonempty
  intro x
  have hl : (state s).ancestor x ∈ (state s).live := s.property.forest.ancestor_live x
  rw [rootRepresentation_ancestor, rootRepresentation_genealogy N s hl]
  exact hf x

lemma reader_obstructed_comb_mass (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (s : Code N sample) (b x : Copy) (as : List Copy)
    (hbad : hasBad b ((state s).genealogy ((state s).ancestor x))) :
    completionReader N r Finset.univ unrankedViewForest s
      {toUnranked (comb b as)} = 0 := by
  rw [reader_forest_mass N r s b, completionTreeLaw, PMF.map_apply]
  have hrootbad : codeBad N b x (rootRepresentation N s) := by
    unfold codeBad
    have hl : (state s).ancestor x ∈ (state s).live := s.property.forest.ancestor_live x
    rw [rootRepresentation_ancestor, rootRepresentation_genealogy N s hl]
    exact hbad
  apply ENNReal.tsum_eq_zero.mpr
  intro d
  by_cases hd : completionKernel N r (rootRepresentation N s) d = 0
  · simp only [hd,ite_self]
  · have hs := (PMF.mem_support_iff _ _).mpr hd
    have he := actual_completion_excludes_specified N r b x as
      (rootRepresentation N s) d (rootRepresentation_ancestral N s) hrootbad hs
    have hne : toUnranked (comb b as) ≠
        toUnranked ((state d).genealogy ((state d).ancestor b)) := by
      intro h; exact he h.symm
    simp only [if_neg hne]

/-- The actual entrance state is read as coefficient times the exact no-loss
indicator; no desired probability is supplied as an assumption. -/
theorem actual_cut_comb_row (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (r : PositivePairRates E) (coin : Hybrid N → Bool) (i j : X) (k : Nat)
    (as : List (Fin k ⊕ Unit))
    (hcover : ∀ x, x = Sum.inr () ∨ x ∈ as) (hnodup : as.Nodup)
    (hb : Sum.inr () ∉ as) (hnonempty : as ≠ [])
    {s : Code N (repeatedSample k i j)}
    (hs : s ∈ (sourceProgram N r
      ((compiledCalendarProgram N C H gamma (fun _ => true)).take
        (bankFirstMeetingIndex N C H gamma r coin i j))
      (initialCode N (repeatedSample k i j) (originalRegister N coin))).support) :
    completionReader N r Finset.univ unrankedViewForest s
      {toUnranked (comb (Sum.inr ()) as)} =
      if liveCard s = Fintype.card (Fin k ⊕ Unit) then
        ENNReal.ofReal (2^as.length /
          ((Nat.factorial (as.length+1) : ℝ) * (Nat.factorial as.length : ℝ))) else 0 := by
  by_cases hc : liveCard s = Fintype.card (Fin k ⊕ Unit)
  · rw [if_pos hc]
    apply reader_flat_comb_mass N r s (Sum.inr ()) as _ hcover hnodup hb hnonempty
    exact (flat_iff_full_card (state s) s.property.forest).mpr hc
  · rw [if_neg hc]
    rcases actual_first_meeting_flat_or_obstructed N C H gamma r coin i j k hs with hf | hb'
    · exact False.elim (hc ((flat_iff_full_card (state s) s.property.forest).mp hf))
    · obtain ⟨x,hx⟩ := hb'
      exact reader_obstructed_comb_mass N r s (Sum.inr ()) x as hx

/-- Pointwise fixed-bank, all-level source-law identity for one specified
labelled comb in the ORIGINAL completed unranked-forest observation. -/
theorem actual_fixed_bank_completed_comb_mass (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (r : PositivePairRates E)
    (coin : Hybrid N → Bool) (i j : X) (k : Nat)
    (as : List (Fin k ⊕ Unit))
    (hcover : ∀ x, x = Sum.inr () ∨ x ∈ as) (hnodup : as.Nodup)
    (hb : Sum.inr () ∉ as) (hnonempty : as ≠ []) :
    (((sourceProgram N r (compiledCalendarProgram N C H gamma (fun _ => true))
      (initialCode N (repeatedSample k i j) (originalRegister N coin))).bind
      (completionKernel N r)).map (fun d => sourceUnrankedForest (state d) Finset.univ))
      {toUnranked (comb (Sum.inr ()) as)} =
    ENNReal.ofReal (2^as.length /
      ((Nat.factorial (as.length+1) : ℝ) * (Nat.factorial as.length : ℝ))) *
      ENNReal.ofReal (Real.exp (-referenceExposure N r
        ((compiledCalendarProgram N C H gamma (fun _ => true)).take
          (bankFirstMeetingIndex N C H gamma r coin i j))
        (initialCode N (repeatedSample k i j) (originalRegister N coin)))) := by
  let P := compiledCalendarProgram N C H gamma (fun _ => true)
  let m := bankFirstMeetingIndex N C H gamma r coin i j
  let start := initialCode N (repeatedSample k i j) (originalRegister N coin)
  let c : ℝ≥0∞ := ENNReal.ofReal (2^as.length /
    ((Nat.factorial (as.length+1) : ℝ) * (Nat.factorial as.length : ℝ)))
  have hc : CommonOnlyWord N (P.take m) := by
    have h := actual_common_compiled_word_only N C H gamma
    change CommonOnlyWord N P at h
    rw [show P = P.take m ++ P.drop m from (List.take_append_drop m P).symm] at h
    exact ((commonOnlyWord_append N _ _).mp h).1
  have hcard : liveCard start = Fintype.card (Fin k ⊕ Unit) := by
    change (Finset.univ : Finset (Fin k ⊕ Unit)).card = _
    exact Finset.card_univ
  change (((sourceProgram N r P start).bind (completionKernel N r)).map _)
    {toUnranked (comb (Sum.inr ()) as)} = c * _
  conv_lhs => rw [show P = P.take m ++ P.drop m from (List.take_append_drop m P).symm]
  rw [sourceProgram_append, PMF.bind_bind, PMF.map_bind, PMF.bind_apply]
  rw [← actual_common_no_loss_exposure N r (P.take m) hc start,
    PMF.map_apply, ← ENNReal.tsum_mul_left]
  apply tsum_congr
  intro s
  by_cases hs : sourceProgram N r (P.take m) start s = 0
  · simp only [hs,zero_mul,ite_self,mul_zero]
  · have hsupport := (PMF.mem_support_iff _ _).mpr hs
    have hreader := actual_bank_first_meeting_completion N C H gamma r coin i j k
      Finset.univ unrankedViewForest hsupport
    simp only [← actual_unranked_view_forest] at hreader
    change ((sourceProgram N r (P.drop m) s).bind (completionKernel N r)).map
      (fun d => sourceUnrankedForest (state d) Finset.univ) =
      completionReader N r Finset.univ unrankedViewForest s at hreader
    rw [hreader, actual_cut_comb_row N C H gamma r coin i j k as hcover hnodup hb hnonempty hsupport]
    rw [hcard]
    by_cases he : liveCard s = Fintype.card (Fin k ⊕ Unit)
    · simp only [if_pos he,if_pos he.symm]
      exact mul_comm _ _
    · simp only [if_neg he,if_neg (Ne.symm he),mul_zero]

#print axioms actual_cut_comb_row
#print axioms actual_fixed_bank_completed_comb_mass
end DotG4.ActualFirstMeetingCombMass
