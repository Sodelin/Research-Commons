import G7CompletedCalendarPolynomial
import G7ExactLawResourceGame

/-! Original unranked endpoint/readout and exact affine response integration.
The polynomial table is constructed from the actual controlled original
calendar law, not supplied as a hypothesis. All rows use the same source bank.
Interval survival coordinates retain their physical dependencies.
Attribution: accepted original G7 source compiler/F1/F2, GPT-6 Astra Pro;
formal source integration draft by dot / OpenAI, 2026-10-10.
DRAFT: uncompiled, not reviewed, not in the running frozen build. -/
namespace GProgram.G7.ActualExactLawResponses
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceFiniteProjection UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceAncestralCompletion UnifiedLean.Source.SourceCompletionHarmonic
open UnifiedLean.Source.OriginalFixedIDControls
open UnifiedLean.Source.ControlledUnrankedSourceProjectivity
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.G6.OriginalCalendarSchema UnifiedLean.G6.OriginalCalendarPattern
open GProgram.G7.SymbolicProgramPolynomial GProgram.G7.ControlledWordPolynomial
open GProgram.G7.CompletedCalendarPolynomial
open GProgram.G7.ExactLawResourceGame
open scoped Classical BigOperators NNReal

variable {J V E Copy X Obs Row Out Action Target : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy] [Nonempty Copy]

noncomputable def readoutPolynomial (N : RootedBinary V E X) {sample : Copy → X}
    (q : SelectedIndex N sample Finset.univ → MvPolynomial (WordVariable N J) ℚ)
    (observe : SelectedIndex N sample Finset.univ → Obs) (o : Obs) :=
  ∑ a, if observe a = o then q a else 0

theorem actual_readout_polynomial (N : RootedBinary V E X) {sample : Copy → X}
    (law : PMF (SelectedIndex N sample Finset.univ))
    (q : SelectedIndex N sample Finset.univ → MvPolynomial (WordVariable N J) ℚ)
    (r : PositivePairRates E) (gamma : Hybrid N → unitInterval) (dur : J → ℝ≥0)
    (hq : ∀ a, wordEval N r gamma dur (q a) = (law a).toReal)
    (observe : SelectedIndex N sample Finset.univ → Obs) (o : Obs) :
    wordEval N r gamma dur (readoutPolynomial N q observe o) = ((law.map observe) o).toReal := by
  rw [map_probability_real]
  simp only [readoutPolynomial,wordEval,MvPolynomial.eval₂_sum]
  apply Finset.sum_congr rfl
  intro a _
  by_cases ha : observe a = o
  · simp only [if_pos ha,mul_one]
    exact hq a
  · simp [ha]

/-- The original readout discards hidden registers, populations and current
survivor IDs. Rooted/unrooted finite topology encoders can act on this forest. -/
noncomputable def unrankedPolynomial (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (common : Hybrid N → Bool) (mask : OriginalMask N)
    (observe : Finset (UnrankedTree Copy) → Obs) (o : Obs) :=
  readoutPolynomial N
    (completedPolynomial N (controlledWordPolynomial N sample H common mask
      (indexedSymbols (calendarSchema N C))))
    (fun a => observe (unrankedForest a.val)) o

theorem actual_controlled_unranked_readout_polynomial (N : RootedBinary V E X)
    (C D : Calendar N.graph) (h : SameOrder C.age D.age) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (mask : OriginalMask N) (r : PositivePairRates E)
    (observe : Finset (UnrankedTree Copy) → Obs) (o : Obs) :
    wordEval N r (originalGamma p) (duration N D (calendarSchema N C))
      (unrankedPolynomial N C sample H common mask observe o) =
      (((controlledCompletedUnrankedLaw N D sample H p common r mask).map observe) o).toReal := by
  have he := actual_readout_polynomial N
    ((controlledCompletedLaw N D sample H p common r mask).map (projection N Finset.univ))
    (completedPolynomial N (controlledWordPolynomial N sample H common mask
      (indexedSymbols (calendarSchema N C)))) r (originalGamma p)
    (duration N D (calendarSchema N C))
    (fun a => actual_controlled_completed_calendar_polynomial N C D h sample H p common mask r a)
    (fun a => observe (unrankedForest a.val)) o
  simpa only [unrankedPolynomial,controlledCompletedUnrankedLaw,PMF.map_comp,
    Function.comp_def,projection,sourceUnrankedForest] using he

/-- One point includes the actual calendar, strict natural inheritance and
positive original rates. It is reused unchanged across every response row. -/
structure SourcePoint (N : RootedBinary V E X) (C : Calendar N.graph) where
  calendar : Calendar N.graph
  sameOrder : SameOrder C.age calendar.age
  inheritance : HybridProbabilities N
  rates : PositivePairRates E

variable [Fintype Row] [Fintype Obs]

noncomputable def actualBaseVector (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (common : Hybrid N → Bool) (rows : Row → OriginalMask N)
    (observe : Finset (UnrankedTree Copy) → Obs) (s : SourcePoint N C) : Row × Obs → ℝ :=
  fun ro => (((controlledCompletedUnrankedLaw N s.calendar sample H s.inheritance
    common s.rates (rows ro.1)).map observe) ro.2).toReal

noncomputable def polynomialBaseVector (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (common : Hybrid N → Bool) (rows : Row → OriginalMask N)
    (observe : Finset (UnrankedTree Copy) → Obs) (s : SourcePoint N C) : Row × Obs → ℝ :=
  fun ro => wordEval N s.rates (originalGamma s.inheritance)
    (duration N s.calendar (calendarSchema N C))
    (unrankedPolynomial N C sample H common (rows ro.1) observe ro.2)

theorem actual_base_vector_eq_polynomial (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (common : Hybrid N → Bool) (rows : Row → OriginalMask N)
    (observe : Finset (UnrankedTree Copy) → Obs) (s : SourcePoint N C) :
    actualBaseVector N C sample H common rows observe s =
      polynomialBaseVector N C sample H common rows observe s := by
  funext ro
  exact (actual_controlled_unranked_readout_polynomial N C s.calendar s.sameOrder sample
    H s.inheritance common (rows ro.1) s.rates observe ro.2).symm

/-- Affine exact-law programme semantics. Pooling and label-retaining action
matrices are both included; admissibility of a matrix is a separate contract. -/
def affineResponse (coefficient : Action → Out → Row × Obs → ℝ)
    (offset : Action → Out → ℝ) (z : Row × Obs → ℝ) (a : Action) : Out → ℝ :=
  fun o => (∑ i, coefficient a o i * z i) + offset a o

theorem actual_affine_response_eq_polynomial (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (common : Hybrid N → Bool) (rows : Row → OriginalMask N)
    (observe : Finset (UnrankedTree Copy) → Obs) (s : SourcePoint N C)
    (coefficient : Action → Out → Row × Obs → ℝ) (offset : Action → Out → ℝ)
    (a : Action) :
    affineResponse coefficient offset (actualBaseVector N C sample H common rows observe s) a =
      affineResponse coefficient offset (polynomialBaseVector N C sample H common rows observe s) a := by
  rw [actual_base_vector_eq_polynomial]

/-- Exact-response semantics for this actual original source family. A complete
finite graph census must separately assemble its finitely many such charts.
Legal programme matrices and the resource transition remain explicit inputs. -/
noncomputable def actualExperiment {Resource : Type*} (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (H : OriginalParentRegistry N)
    (common : Hybrid N → Bool) (rows : Row → OriginalMask N)
    (observe : Finset (UnrankedTree Copy) → Obs)
    (target : SourcePoint N C → Target)
    (coefficient : Action → Out → Row × Obs → ℝ) (offset : Action → Out → ℝ)
    (legal : Resource → Action → Prop) (update : Resource → Action → Resource) :
    Experiment (SourcePoint N C) Action (Out → ℝ) Target Resource where
  admitted := fun _ => True
  target := target
  response := fun s => affineResponse coefficient offset
    (actualBaseVector N C sample H common rows observe s)
  legal := legal
  update := update

/-- The SAME source point must satisfy every exact affine response equation.
There is no independent refitting of rates/gamma between history rows. -/
theorem actual_history_consistency_iff_polynomial {Resource : Type*}
    (N : RootedBinary V E X) (C : Calendar N.graph) (sample : Copy → X)
    (H : OriginalParentRegistry N) (common : Hybrid N → Bool)
    (rows : Row → OriginalMask N) (observe : Finset (UnrankedTree Copy) → Obs)
    (target : SourcePoint N C → Target)
    (coefficient : Action → Out → Row × Obs → ℝ) (offset : Action → Out → ℝ)
    (legal : Resource → Action → Prop) (update : Resource → Action → Resource)
    (h : History Action (Out → ℝ)) (s : SourcePoint N C) :
    Consistent (actualExperiment N C sample H common rows observe target coefficient offset legal update) h s ↔
      ∀ ay ∈ h, affineResponse coefficient offset
        (polynomialBaseVector N C sample H common rows observe s) ay.1 = ay.2 := by
  simp only [Consistent,actualExperiment,true_and,actual_base_vector_eq_polynomial]

end GProgram.G7.ActualExactLawResponses
