import NaturalCompletedAllPairs

/-!
Cloud Sol /root/source_backend_review_sol, 8 October 2026.
Authored SOURCE/HAND; all bodies compiler UNCHECKED/outside179/181.
The literal finite reader and fixed selected-panel tuple read the SAME whole
original source. One actual shared tree/decoration witnesses ALL selected bins.
No biological menu grammar, independently drawn panels, desired law equality
or independently initialized small-source tag law is an input/conclusion.
-/
namespace CloudG6.NativeFiniteReaderMenu

open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UnrankedGenealogyObservation
open GProgram.G2.FaithfulPairAgeDecoration
open CloudG6.SourceIndependentForestAlphabet CloudG6.ActualFiniteObservableRecord
open CloudG6.ActualPanelForestReadout CloudG6.NaturalCompletedAllPairs
open CloudG6.ActualSourceCorruptionClasses
open scoped Classical

universe u v w x y z
variable {Copy : Type w} {X : Type x} {Tag : Type y} {I : Type z}
variable [DecidableEq Copy] [Fintype Copy] [Fintype X] [Fintype Tag] [Fintype I]
variable [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
variable {sample : Copy → X}

theorem pruneForest_singleton (keep : Finset Copy) (q : UnrankedTree Copy) :
    pruneForest keep {q} = optionTreeSet (pruneTree keep q) := by
  simp [pruneForest]

/-- Necessary consistency of selected observable fields. The full genealogy
and real decoration are existential witnesses, never hidden observed data. -/
def SelectedPairBinWitness (leafAge : Copy → ℝ) (bin : ℝ → Tag)
    (keep : Finset Copy) (a : RawPanelRecord keep Tag) : Prop :=
  ∃ t : Genealogy Copy, ∃ d : Decoration t,
    t.WellLabelled ∧ t.leaves = Finset.univ ∧
      a.1 = optionTreeSet (pruneTree keep (toUnranked t)) ∧
        ∀ a' b' : PanelCopy keep, a' ≠ b' →
          a.2 a' b' = bin (pairAge leafAge t d a'.val b'.val)

theorem whole_witness_selected (leafAge : Copy → ℝ) (bin : ℝ → Tag)
    (a : RawObservedRecord Copy Tag) (h : WholePairBinWitness leafAge bin a)
    (keep : Finset Copy) : SelectedPairBinWitness leafAge bin keep (panelReadout keep a) := by
  obtain ⟨t, d, hW, hL, hF, hB⟩ := h
  refine ⟨t, d, hW, hL, ?_, ?_⟩
  · change pruneForest keep a.1 = _
    rw [hF, pruneForest_singleton]
  · intro x y hxy
    exact hB x.val y.val (fun he => hxy (Subtype.ext he))

/-- ALL full native finiteReader support atoms have the original actual
whole-tree/all-pair witness. Invalid unrestricted payloads are not fabricated. -/
theorem native_reader_support (mode : Bool) (bin : ℝ → Tag) (hbin : Measurable bin)
    (s : OriginalParameters.{u,v,w,x} Copy X sample)
    {o : Option (FiniteObservedRecord Copy Tag)}
    (ho : o ∈ (nativeLaw mode bin hbin finiteRecordReader s).support) :
    ∃ a : FiniteObservedRecord Copy Tag, o = some a ∧
      WholePairBinWitness (fun _ => 0) bin (forgetFiniteRecord a) := by
  rw [actual_native_law_finite_reader] at ho
  obtain ⟨a, ha, he⟩ := (PMF.mem_support_map_iff _ _ _).mp ho
  exact ⟨a, he.symm, native_finite_all_pairs_support mode bin hbin s ha⟩

theorem native_panel_support (mode : Bool) (bin : ℝ → Tag) (hbin : Measurable bin)
    (s : OriginalParameters.{u,v,w,x} Copy X sample) (keep : Finset Copy)
    {a : PanelCode keep Tag}
    (ha : a ∈ ((nativeFiniteLaw mode bin hbin s).map (finitePanelReadout keep)).support) :
    SelectedPairBinWitness (fun _ => 0) bin keep a.val := by
  obtain ⟨b, hb, he⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
  rw [← he]
  exact whole_witness_selected (fun _ => 0) bin (forgetFiniteRecord b)
    (native_finite_all_pairs_support mode bin hbin s hb) keep

/-- A fixed finite tuple of literal external Copy subsets. Finiteness comes
from the constructed PanelCode/Pi carriers. This does not specify an I_Z menu. -/
abbrev MenuCode (panels : I → Finset Copy) (Tag : Type y) [Fintype Tag] :=
  (i : I) → PanelCode (panels i) Tag

noncomputable def finiteMenuReadout (panels : I → Finset Copy)
    (a : FiniteObservedRecord Copy Tag) : MenuCode panels Tag :=
  fun i => finitePanelReadout (panels i) a

def SharedMenuWitness (leafAge : Copy → ℝ) (bin : ℝ → Tag)
    (panels : I → Finset Copy) (a : MenuCode panels Tag) : Prop :=
  ∃ t : Genealogy Copy, ∃ d : Decoration t,
    t.WellLabelled ∧ t.leaves = Finset.univ ∧
      ∀ i : I, (a i).val.1 = optionTreeSet (pruneTree (panels i) (toUnranked t)) ∧
        ∀ x' y' : PanelCopy (panels i), x' ≠ y' →
          (a i).val.2 x' y' = bin (pairAge leafAge t d x'.val y'.val)

theorem whole_witness_menu (leafAge : Copy → ℝ) (bin : ℝ → Tag)
    (panels : I → Finset Copy) (a : FiniteObservedRecord Copy Tag)
    (h : WholePairBinWitness leafAge bin (forgetFiniteRecord a)) :
    SharedMenuWitness leafAge bin panels (finiteMenuReadout panels a) := by
  obtain ⟨t, d, hW, hL, hF, hB⟩ := h
  refine ⟨t, d, hW, hL, ?_⟩
  intro i
  constructor
  · change pruneForest (panels i) (forgetFiniteRecord a).1 = _
    rw [hF, pruneForest_singleton]
  · intro x' y' hxy
    exact hB x'.val y'.val (fun he => hxy (Subtype.ext he))

noncomputable def nativeMenuLaw (mode : Bool) (bin : ℝ → Tag) (hbin : Measurable bin)
    (s : OriginalParameters.{u,v,w,x} Copy X sample) (panels : I → Finset Copy) :
    PMF (MenuCode panels Tag) :=
  (nativeFiniteLaw mode bin hbin s).map (finiteMenuReadout panels)

theorem native_menu_support (mode : Bool) (bin : ℝ → Tag) (hbin : Measurable bin)
    (s : OriginalParameters.{u,v,w,x} Copy X sample) (panels : I → Finset Copy)
    {a : MenuCode panels Tag} (ha : a ∈ (nativeMenuLaw mode bin hbin s panels).support) :
    SharedMenuWitness (fun _ => 0) bin panels a := by
  obtain ⟨b, hb, he⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
  rw [← he]
  exact whole_witness_menu (fun _ => 0) bin panels b
    (native_finite_all_pairs_support mode bin hbin s hb)

/-- The tuple is obtained from the SAME actual finiteReader output. Option
failure is retained in the map, and actual native support gives it zero mass. -/
theorem native_menu_from_actual_reader (mode : Bool) (bin : ℝ → Tag) (hbin : Measurable bin)
    (s : OriginalParameters.{u,v,w,x} Copy X sample) (panels : I → Finset Copy) :
    (nativeLaw mode bin hbin finiteRecordReader s).map
        (fun o => o.map (finiteMenuReadout panels)) =
      (nativeMenuLaw mode bin hbin s panels).map some := by
  rw [actual_native_law_finite_reader]
  unfold nativeMenuLaw
  rw [PMF.map_comp, PMF.map_comp]
  rfl

theorem shared_menu_coordinate (leafAge : Copy → ℝ) (bin : ℝ → Tag)
    (panels : I → Finset Copy) (a : MenuCode panels Tag)
    (ha : SharedMenuWitness leafAge bin panels a) (i : I) :
    SelectedPairBinWitness leafAge bin (panels i) (a i).val := by
  obtain ⟨t, d, hW, hL, hA⟩ := ha
  exact ⟨t, d, hW, hL, (hA i).1, (hA i).2⟩

end CloudG6.NativeFiniteReaderMenu
