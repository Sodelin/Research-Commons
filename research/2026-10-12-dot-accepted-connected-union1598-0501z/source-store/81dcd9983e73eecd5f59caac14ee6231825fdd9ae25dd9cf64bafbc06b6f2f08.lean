import G7OriginalFamilyStrategy
import G7OriginalSurvivalCoverage

/-!
# Supplied-calendar normalization of the actual original reset family

Attribution: the original whole-edge realization/frontier argument and the
original exact-law reset strategy are due to the accepted G7 research; their
source formalizations are by dot / OpenAI. This separate compatibility
consumer is by Codex / lean_reuse_successor, 2026-10-10.

Use one supplied strict comparison calendar per original graph. The rates are
constructed once from each original source's whole-edge survival bank, before
any control row, programme or reset history. The graph, complete original-ID
registry, natural inheritance bank, COMMON/INDEPENDENT mode and source point
are retained. The response and resource-state fields of the actual reset
experiment therefore agree.

This proposal does not decode a native source, refine a polynomial compiler,
select a policy, run QE/CAD, or preserve a timed/binned observation. The
admitted source predicate, target and allowed programme family remain supplied
inputs. DRAFT: no compiler acceptance is asserted by this source text.
-/

namespace GProgram.G7.OriginalFamilyCalendarNormalization
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.OriginalFixedIDControls
open UnifiedLean.Source.ControlledUnrankedSourceProjectivity
open UnifiedLean.Source.UnrankedGenealogyObservation
open GProgram.G7.ExactLawResourceGame
open GProgram.G7.OriginalFamilyStrategy
open GProgram.G7.OriginalSurvivalCoverage
open scoped Classical

variable {S V E X ID Copy Row Obs Out A T : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype ID] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable [Fintype Row] [Fintype Obs] [Fintype Out]

/-- One normalized positive rate bank for each original source point. No row
or programme argument occurs in this construction. -/
noncomputable def normalizedFamily (F : OriginalFamily S V E X ID)
    (C₀ : ∀ s, Calendar (F.network s).graph) : OriginalFamily S V E X ID where
  network := F.network
  calendar := C₀
  ids := F.ids
  parents := F.parents
  inheritance := F.inheritance
  common := F.common
  rates s := ratesFromSurvival (F.network s) (C₀ s)
    (survival (F.network s) (F.calendar s) (F.rates s))
    (physical_survival_open_cube (F.network s) (F.calendar s) (F.rates s))

variable (F : OriginalFamily S V E X ID)
variable (C₀ : ∀ s, Calendar (F.network s).graph)

theorem actual_normalized_family_survival (s : S) :
    survival ((normalizedFamily F C₀).network s)
      ((normalizedFamily F C₀).calendar s) ((normalizedFamily F C₀).rates s) =
    survival (F.network s) (F.calendar s) (F.rates s) :=
  ratesFromSurvival_survival (F.network s) (C₀ s)
    (survival (F.network s) (F.calendar s) (F.rates s))
    (physical_survival_open_cube (F.network s) (F.calendar s) (F.rates s))

/-- The inherited chart supplies the equality for every full original mask
using the same normalized rate bank and original natural register. -/
theorem actual_normalized_family_completed_law (sample : Copy → X) (s : S)
    (mask : OriginalMask (F.network s)) :
    controlledCompletedLaw (F.network s) (F.calendar s) sample (F.parents s)
      (F.inheritance s) (fun _ => F.common s) (F.rates s) mask =
    controlledCompletedLaw ((normalizedFamily F C₀).network s)
      ((normalizedFamily F C₀).calendar s) sample ((normalizedFamily F C₀).parents s)
      ((normalizedFamily F C₀).inheritance s) (fun _ => (normalizedFamily F C₀).common s)
      ((normalizedFamily F C₀).rates s) mask := by
  exact ((actual_source_survival_chart (F.network s) (C₀ s) sample (F.parents s)
    (F.inheritance s) (fun _ => F.common s)
    (survival (F.network s) (F.calendar s) (F.rates s))
    (physical_survival_open_cube (F.network s) (F.calendar s) (F.rates s))).2
      (F.calendar s) (F.rates s) rfl).2 mask

variable (sample : Copy → X) (rows : Row → ID → Option Bool)
variable (observe : Finset (UnrankedTree Copy) → Obs)

/-- Every finite original-ID row has the same entire observed law. -/
theorem actual_original_row_normalization (s : S) (row : Row) :
    rowLaw F sample rows observe s row =
      rowLaw (normalizedFamily F C₀) sample rows observe s row := by
  exact congrArg
    (fun law : PMF (Code (F.network s) sample) =>
      (law.map (fun d => sourceUnrankedForest (state d) Finset.univ)).map observe)
    (actual_normalized_family_completed_law F C₀ sample s
      (fun h => rows row ((F.ids s).symm h)))

/-- Pre-source row randomization and every declared observation channel are
the unchanged programme definition; no response-law premise is supplied. -/
theorem actual_original_programme_normalization
    (programme : A → Programme Row Obs Out) (s : S) (a : A) :
    programmeLaw F sample rows observe programme s a =
      programmeLaw (normalizedFamily F C₀) sample rows observe programme s a := by
  exact congrArg ((programme a).weights.bind) (funext fun row =>
    congrArg (fun law : PMF Obs => law.bind ((programme a).channel row))
      (actual_original_row_normalization F C₀ sample rows observe s row))

variable [DecidableEq Row] [DecidableEq ID] [DecidableEq A]

/-- The full exact-law response function agrees for every original point and
action, so one source continues to fit the whole reset history. -/
theorem actual_original_reset_response_normalization
    (programme : A → Programme Row Obs Out)
    (admitted : S → Prop) (target : S → T) (allowed : A → Prop) (budget : Budget) :
    (experiment F sample rows observe programme admitted target allowed budget).response =
      (experiment (normalizedFamily F C₀) sample rows observe programme
        admitted target allowed budget).response := by
  funext s a o
  exact congrArg (fun law : PMF Out => (law o).toReal)
    (actual_original_programme_normalization F C₀ sample rows observe programme s a)

/-- Admission, target, legal trajectory resources and reset state updates are
unchanged fields, and the response equality above gives the full experiment. -/
theorem actual_original_reset_experiment_normalization
    (programme : A → Programme Row Obs Out)
    (admitted : S → Prop) (target : S → T) (allowed : A → Prop) (budget : Budget) :
    experiment F sample rows observe programme admitted target allowed budget =
      experiment (normalizedFamily F C₀) sample rows observe programme
        admitted target allowed budget := by
  have h := actual_original_reset_response_normalization F C₀ sample rows observe
    programme admitted target allowed budget
  unfold experiment at h ⊢
  congr 1 <;> exact h

/-- Entire-history consistency is preserved, with the same original source
point on both sides of every executed response. -/
theorem actual_original_reset_history_normalization
    (programme : A → Programme Row Obs Out)
    (admitted : S → Prop) (target : S → T) (allowed : A → Prop) (budget : Budget)
    (history : History A (Out → ℝ)) (s : S) :
    Consistent (experiment F sample rows observe programme admitted target allowed budget)
      history s ↔
    Consistent (experiment (normalizedFamily F C₀) sample rows observe programme
      admitted target allowed budget) history s := by
  rw [actual_original_reset_experiment_normalization F C₀ sample rows observe
    programme admitted target allowed budget]

end GProgram.G7.OriginalFamilyCalendarNormalization
