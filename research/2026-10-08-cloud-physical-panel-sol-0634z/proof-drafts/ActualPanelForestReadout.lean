import ActualFiniteObservableRecord
import Mathlib.Data.Finset.Union

/-!
Cloud Sol /root/source_backend_review_sol, 8 October 2026.
Authored SOURCE/HAND candidate; every new body compiler UNCHECKED/outside179.
The actual source pruneTree suppresses empty/unary children. Retain only a
fixed external Copy panel and its SAME pair tags; hidden IDs/register absent.
No invented biological menu grammar, desired law or decoder field is input.
-/
namespace CloudG6.ActualPanelForestReadout

open MeasureTheory ProbabilityTheory GProgram.SourceForest Nanuq.Source GProgram.G5
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceCalendarCompiler
open CloudG3.ActualCutJointLaw CloudG3.ActualCalendarCutContext
open CloudG6.SourceIndependentForestAlphabet CloudG6.ActualFiniteObservableRecord
open CloudG6.ActualSourceCorruptionClasses CloudG6.ActualObservationCorruption
open CloudG6.NaturalPastCompleteObservation CloudG6.NaturalCalendarPastAdmission
open scoped Classical

universe u v w x y
variable {Copy : Type w} {Tag : Type y} [DecidableEq Copy] [Fintype Copy]

theorem genealogy_prune_univ (t : Genealogy Copy) : t.prune Finset.univ = some t := by
  induction t with
  | leaf x => simp [Genealogy.prune]
  | graft a b ha hb => simp [Genealogy.prune, ha, hb, Genealogy.joinPruned]

def optionTreeSet : Option (UnrankedTree Copy) → Finset (UnrankedTree Copy)
  | none => ∅
  | some q => {q}

noncomputable def pruneForest (keep : Finset Copy) (F : Finset (UnrankedTree Copy)) :
    Finset (UnrankedTree Copy) := F.biUnion (fun q => optionTreeSet (pruneTree keep q))

theorem mem_pruneForest (keep : Finset Copy) (F : Finset (UnrankedTree Copy))
    (r : UnrankedTree Copy) :
    r ∈ pruneForest keep F ↔ ∃ q ∈ F, pruneTree keep q = some r := by
  simp only [pruneForest, Finset.mem_biUnion]
  constructor
  · rintro ⟨q, hq, hr⟩
    cases hp : pruneTree keep q with
    | none => simp [hp, optionTreeSet] at hr
    | some t =>
        have htr : t = r := by simpa [hp, optionTreeSet, eq_comm] using hr
        exact ⟨q, hq, hp.trans (congrArg some htr)⟩
  · rintro ⟨q, hq, hp⟩
    exact ⟨q, hq, by simp [hp, optionTreeSet]⟩

/-- The observed whole unranked forest determines the ACTUAL selected forest.
The surviving source owner may lie outside keep; leaf fibres supply a genuine
selected witness in that same component. No representative-ID decoder. -/
theorem prune_actual_full_forest {V E : Type*} (s : State V E Copy) (hs : Valid s)
    (keep : Finset Copy) :
    pruneForest keep (sourceUnrankedForest s Finset.univ) = sourceUnrankedForest s keep := by
  apply Finset.ext
  intro r
  constructor
  · intro hr
    obtain ⟨q, hq, hp⟩ := (mem_pruneForest keep _ r).mp hr
    obtain ⟨l, hl, he⟩ := forest_member_live_witness s hs Finset.univ hq
    have heq : toUnranked (s.genealogy l) = q := by
      simpa [genealogy_prune_univ, optionUnranked] using he
    rw [← heq, prune_toUnranked] at hp
    cases ht : (s.genealogy l).prune keep with
    | none => simp [ht, optionUnranked] at hp
    | some t =>
        have htr : toUnranked t = r := by simpa [ht, optionUnranked] using hp
        obtain ⟨y, hy⟩ := genealogy_leaves_nonempty t
        have hleaves : t.leaves = (s.genealogy l).leaves ∩ keep := by
          simpa [ht, Genealogy.optionLeaves] using Genealogy.prune_leaves keep (s.genealogy l)
        rw [hleaves] at hy
        have hyl : s.ancestor y = l := (hs.leaf_fiber l hl y).mp (Finset.mem_inter.mp hy).1
        apply (mem_sourceUnrankedForest s keep r).mpr
        exact ⟨y, (Finset.mem_inter.mp hy).2, t, by rw [hyl]; exact ht, htr⟩
  · intro hr
    obtain ⟨x, hx, t, ht, htr⟩ := (mem_sourceUnrankedForest s keep r).mp hr
    apply (mem_pruneForest keep _ r).mpr
    refine ⟨toUnranked (s.genealogy (s.ancestor x)), ?_, ?_⟩
    · exact (mem_sourceUnrankedForest s Finset.univ _).mpr
        ⟨x, Finset.mem_univ x, s.genealogy (s.ancestor x), genealogy_prune_univ _, rfl⟩
    · rw [prune_toUnranked, ht]
      simpa [optionUnranked] using congrArg some htr

abbrev PanelCopy (keep : Finset Copy) := {x : Copy // x ∈ keep}
abbrev RawPanelRecord (keep : Finset Copy) (Tag : Type*) :=
  Finset (UnrankedTree Copy) × (PanelCopy keep → PanelCopy keep → Tag)

noncomputable instance panelRecordMeasurable (keep : Finset Copy) :
    MeasurableSpace (RawPanelRecord keep Tag) := ⊤

/-- A fixed literal panel readout, not a newly stipulated menu language. -/
noncomputable def panelReadout (keep : Finset Copy) (a : RawObservedRecord Copy Tag) :
    RawPanelRecord keep Tag := (pruneForest keep a.1, fun x y => a.2 x.val y.val)

noncomputable def sourcePanelRecord {V E : Type*} (keep : Finset Copy)
    (s : State V E Copy) (B : Copy → Copy → Tag) : RawPanelRecord keep Tag :=
  (sourceUnrankedForest s keep, fun x y => B x.val y.val)

theorem panelReadout_actual {V E : Type*} (keep : Finset Copy)
    (s : State V E Copy) (hs : Valid s) (B : Copy → Copy → Tag) :
    panelReadout keep (sourceUnrankedForest s Finset.univ, B) = sourcePanelRecord keep s B := by
  apply Prod.ext
  · exact prune_actual_full_forest s hs keep
  · rfl

variable [Fintype Tag]

/-- A DERIVED finite image of the previously constructed full observable
carrier. No enumerator or injection is an admission field. -/
noncomputable def panelAlphabet (keep : Finset Copy) : Finset (RawPanelRecord keep Tag) :=
  Finset.univ.image (fun a : FiniteObservedRecord Copy Tag => panelReadout keep (forgetFiniteRecord a))

abbrev PanelCode (keep : Finset Copy) (Tag : Type*) [Fintype Tag] :=
  {a : RawPanelRecord keep Tag // a ∈ panelAlphabet keep}

noncomputable instance panelCodeFintype (keep : Finset Copy) : Fintype (PanelCode keep Tag) :=
  Fintype.subtype (panelAlphabet keep) (fun _ => Iff.rfl)

theorem panelCode_val_injective (keep : Finset Copy) :
    Function.Injective (Subtype.val : PanelCode keep Tag → RawPanelRecord keep Tag) := by
  intro a b h
  exact Subtype.ext h

noncomputable def finitePanelReadout (keep : Finset Copy) (a : FiniteObservedRecord Copy Tag) :
    PanelCode keep Tag :=
  ⟨panelReadout keep (forgetFiniteRecord a), Finset.mem_image.mpr ⟨a, Finset.mem_univ a, rfl⟩⟩

theorem finitePanelReadout_forget (keep : Finset Copy) (a : FiniteObservedRecord Copy Tag) :
    (finitePanelReadout keep a).val = panelReadout keep (forgetFiniteRecord a) := rfl

variable {V : Type u} {E : Type v}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E]
variable {X : Type x} [Fintype X] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
variable {sample : Copy → X}

noncomputable def endpointPanelReadout (N : RootedBinary V E X) {sample : Copy → X}
    (keep : Finset Copy) (q : TaggedEndpoint (Tag := Tag) N sample) : RawPanelRecord keep Tag :=
  sourcePanelRecord keep (state q.1) q.2

/-- Every panel coordinate is read from the SAME whole original source. -/
theorem native_finite_panel_source (mode : Bool) (bin : ℝ → Tag) (hbin : Measurable bin)
    (s : OriginalParameters.{u,v,w,x} Copy X sample) (keep : Finset Copy) :
    ((nativeFiniteLaw mode bin hbin s).map (finitePanelReadout keep)).map Subtype.val =
      (naturalCompletedJoint s.original.network s.original.calendar sample s.inheritance
        s.rates bin hbin (compiledCalendarProgram s.original.network s.original.calendar
          s.registry (originalGamma s.inheritance) (fun _ => mode))).map
        (endpointPanelReadout s.original.network keep) := by
  unfold nativeFiniteLaw actualCompiledObservation
  rw [PMF.map_comp, PMF.map_comp]
  apply congrArg (PMF.map · _)
  funext q
  exact panelReadout_actual keep (state q.1) q.1.property.forest q.2

/-- The actual once-drawn register mixture is preserved; no independence or
desired entering law is supplied. Each term has the same physical program. -/
theorem native_finite_panel_initialized (mode : Bool) (bin : ℝ → Tag) (hbin : Measurable bin)
    (s : OriginalParameters.{u,v,w,x} Copy X sample) (keep : Finset Copy) :
    ((nativeFiniteLaw mode bin hbin s).map (finitePanelReadout keep)).map Subtype.val =
      (originalRegisterPMF s.original.network s.inheritance).bind (fun register =>
        (completedJoint s.original.network s.rates bin hbin
          (compiledCalendarProgram s.original.network s.original.calendar s.registry
            (originalGamma s.inheritance) (fun _ => mode))
          (initialCode s.original.network sample register) (firstOriginalDate s.original.network s.original.calendar)
          (fun a b => bin (leafAgeMatrix s.original.network s.original.calendar sample a b))).map
          (endpointPanelReadout s.original.network keep)) := by
  rw [native_finite_panel_source]
  unfold naturalCompletedJoint
  rw [PMF.map_bind]

end CloudG6.ActualPanelForestReadout
