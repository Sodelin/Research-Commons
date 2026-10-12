import G4ActualBankFirstMeeting
import G4SpecifiedCombEvent
import G1OriginalCurrentRootReconstruction
import G5SourcePairPersistence

/-!
# The actual fixed-bank first meeting has a flat-or-obstructed entrance

Contributor: dot (OpenAI), 12 October 2026. UNCOMPILED draft.
Composition of the inherited first-meeting hand argument with accepted actual
source providers. No new meeting, no-loss probability or completion recurrence
is assumed. All repeated-copy arities and fixed original COMMON banks are kept.
The last first-meeting operation must be a boundary: an interval cannot change
reference locations. Before it, B is isolated; the actual boundary preserves
ancestry. Valid leaf fibres therefore keep B's genealogy a singleton at the cut.
Every nonflat alternative then contains a genuine nontrivial B-free clade.
Strict exposure positivity, cross-arity scaling and natural-bank averaging are
separate obligations; no general G4 closure is claimed.
-/
namespace DotG4.ActualFirstMeetingEntrance
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.SourceForestSilentPruning
open GProgram.G5.SafePrefixRouteBridge
open GProgram.G5.SourcePairPersistence
open GProgram.G4.ActualCommonSelectorSupport
open DotG4.ActualBankFirstMeeting DotG34.SpecifiedCombEvent
open scoped Classical NNReal ENNReal
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma isolated_ancestor_singleton (s : State V E Copy) (hs : Valid s) (b : Copy)
    (hb : ∀ x, s.ancestor x = s.ancestor b → x = b) :
    s.genealogy (s.ancestor b) = .leaf b := by
  apply G1OriginalCurrentRootReconstruction.wellLabelled_singleton_tree _
    (hs.wellLabelled _ (hs.ancestor_live b)) b
  ext x
  rw [hs.leaf_fiber _ (hs.ancestor_live b), Finset.mem_singleton]
  exact ⟨hb x, fun h => h ▸ rfl⟩

/-- This is a pointwise consequence of the accepted actual COMMON location
law, not a new induction over epoch dynamics or a no-merger assumption. -/
lemma before_first_meeting_B_isolated (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (r : PositivePairRates E)
    (coin : Hybrid N → Bool) (i j : X) (k q : Nat)
    (hq : q < bankFirstMeetingIndex N C H gamma r coin i j)
    {s : Code N (repeatedSample k i j)}
    (hs : s ∈ (sourceProgram N r
      ((compiledCalendarProgram N C H gamma (fun _ => true)).take q)
      (initialCode N (repeatedSample k i j) (originalRegister N coin))).support) :
    ∀ x, (state s).ancestor x = (state s).ancestor (.inr ()) → x = .inr () := by
  let P := compiledCalendarProgram N C H gamma (fun _ => true)
  have hc : CommonOnlyWord N (P.take q) := by
    have h := actual_common_compiled_word_only N C H gamma
    change CommonOnlyWord N P at h
    rw [show P = P.take q ++ P.drop q from (List.take_append_drop q P).symm] at h
    exact ((commonOnlyWord_append N _ _).mp h).1
  have hl := actual_common_program_copy_locations N r (P.take q) hc
    (initialCode N (repeatedSample k i j) (originalRegister N coin)) hs
  intro x hx
  cases x with
  | inr u => cases u; rfl
  | inl a =>
    have he : copyLocation (state s) (.inl a) = copyLocation (state s) (.inr ()) :=
      congrArg (state s).location hx
    rw [hl (.inl a), hl (.inr ())] at he
    have ha := initial_reference_location_cross_carrier N (repeatedSample k i j)
      (pairSample i j) (originalRegister N coin) (P.take q) (.inl a) true rfl
    have hb := initial_reference_location_cross_carrier N (repeatedSample k i j)
      (pairSample i j) (originalRegister N coin) (P.take q) (.inr ()) false rfl
    exact False.elim (before_bankFirstMeeting_separated N C H gamma r coin i j q hq
      (ha.symm.trans (he.trans hb)))

/-- The cut includes its final boundary, even inside a tied-date batch.
This avoids falsely applying the pre-cut separation theorem at the meeting. -/
theorem actual_first_meeting_B_isolated (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (r : PositivePairRates E)
    (coin : Hybrid N → Bool) (i j : X) (k : Nat)
    {s : Code N (repeatedSample k i j)}
    (hs : s ∈ (sourceProgram N r
      ((compiledCalendarProgram N C H gamma (fun _ => true)).take
        (bankFirstMeetingIndex N C H gamma r coin i j))
      (initialCode N (repeatedSample k i j) (originalRegister N coin))).support) :
    ∀ x, (state s).ancestor x = (state s).ancestor (.inr ()) → x = .inr () := by
  let P := compiledCalendarProgram N C H gamma (fun _ => true)
  generalize hm : bankFirstMeetingIndex N C H gamma r coin i j = m at hs
  cases m with
  | zero =>
    have he : s = initialCode N (repeatedSample k i j) (originalRegister N coin) := by
      simpa only [List.take_zero, sourceProgram, PMF.mem_support_pure_iff] using hs
    subst s
    exact fun x hx => hx
  | succ q =>
    have hbound := (bankFirstMeeting_spec N C H gamma r coin i j).1
    have hq : q < P.length := by dsimp [P]; omega
    have htake := List.take_succ_eq_append_getElem hq
    cases hop : P[q] with
    | interval t =>
      have he := (bankFirstMeeting_spec N C H gamma r coin i j).2
      have href : pairReference N C H gamma coin i j (q+1) =
          pairReference N C H gamma coin i j q := by
        unfold pairReference
        rw [htake, hop, fixedRegisterPrefix_append]
        rfl
      rw [hm, href] at he
      exact False.elim (before_bankFirstMeeting_separated N C H gamma r coin i j q
        (by omega) he)
    | boundary op =>
      rw [htake, hop, sourceProgram_append] at hs
      obtain ⟨z,hz,hsz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hs
      have hb : s ∈ (boundaryKernel N op z).support := by
        simpa only [sourceProgram, sourceProgramStep, PMF.bind_pure] using hsz
      intro x hx
      rw [boundary_ancestor_eq N op z s hb] at hx
      exact before_first_meeting_B_isolated N C H gamma r coin i j k q
        (by omega) hz x hx

/-- Pure source-forest fact: with B isolated, any nonflat genealogy itself
supplies a nontrivial B-free clade. Full selected A/B coverage is not needed
for this structural statement; it is needed to call the clade A-only. -/
lemma isolated_flat_or_bad (s : State V E Copy) (hs : Valid s) (b : Copy)
    (hb : ∀ x, s.ancestor x = s.ancestor b → x = b) :
    (∀ x, s.genealogy (s.ancestor x) = .leaf x) ∨
      ∃ x, hasBad b (s.genealogy (s.ancestor x)) := by
  by_cases hflat : ∀ x, s.genealogy (s.ancestor x) = .leaf x
  · exact Or.inl hflat
  · right
    push_neg at hflat
    obtain ⟨x,hx⟩ := hflat
    have hl := hs.ancestor_live x
    have hw := hs.wellLabelled _ hl
    have hself : x ∈ (s.genealogy (s.ancestor x)).leaves :=
      (hs.leaf_fiber _ hl x).mpr rfl
    have hnot : b ∉ (s.genealogy (s.ancestor x)).leaves := by
      intro hmem
      have he := (hs.leaf_fiber _ hl b).mp hmem
      have hxb := hb x he.symm
      subst x
      exact hx (isolated_ancestor_singleton s hs b hb)
    cases ht : s.genealogy (s.ancestor x) with
    | leaf y =>
      rw [ht] at hself
      have hxy := Finset.mem_singleton.mp hself
      exact False.elim (hx (ht.trans (congrArg Genealogy.leaf hxy.symm)))
    | graft l u =>
      rw [ht] at hw hnot
      obtain ⟨a,ha⟩ := genealogy_leaves_nonempty l
      obtain ⟨c,hc⟩ := genealogy_leaves_nonempty u
      have hne : a ≠ c := by
        intro he; subst c; exact Finset.disjoint_left.mp hw.2.2 ha hc
      have hsub : ({a,c} : Finset Copy) ⊆ l.leaves ∪ u.leaves := by
        intro z hz
        simp only [Finset.mem_insert, Finset.mem_singleton] at hz
        rcases hz with rfl | rfl
        · exact Finset.mem_union.mpr (Or.inl ha)
        · exact Finset.mem_union.mpr (Or.inr hc)
      have hcard : 2 ≤ (l.leaves ∪ u.leaves).card := by
        simpa only [Finset.card_pair hne] using Finset.card_le_card hsub
      refine ⟨x, ?_⟩
      rw [ht]
      exact Or.inl ⟨hcard,hnot⟩

/-- Actual all-level fixed-bank entrance alternative at the constructed cut.
No flatness or obstruction premise is supplied. -/
theorem actual_first_meeting_flat_or_obstructed (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (r : PositivePairRates E)
    (coin : Hybrid N → Bool) (i j : X) (k : Nat)
    {s : Code N (repeatedSample k i j)}
    (hs : s ∈ (sourceProgram N r
      ((compiledCalendarProgram N C H gamma (fun _ => true)).take
        (bankFirstMeetingIndex N C H gamma r coin i j))
      (initialCode N (repeatedSample k i j) (originalRegister N coin))).support) :
    (∀ x, (state s).genealogy ((state s).ancestor x) = .leaf x) ∨
      ∃ x, hasBad (.inr ()) ((state s).genealogy ((state s).ancestor x)) :=
  isolated_flat_or_bad (state s) s.property.forest (.inr ())
    (actual_first_meeting_B_isolated N C H gamma r coin i j k hs)

#print axioms actual_first_meeting_B_isolated
#print axioms actual_first_meeting_flat_or_obstructed
end DotG4.ActualFirstMeetingEntrance
