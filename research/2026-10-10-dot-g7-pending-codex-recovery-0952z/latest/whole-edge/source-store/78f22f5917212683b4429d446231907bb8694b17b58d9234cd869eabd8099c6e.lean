import G7OriginalFamilyStrategy
import G7OriginalFiniteEncoding
import G7OriginalControlRelabelling
import G1ActualGraphNormalization

/-! Original registry census -> fixed finite carriers -> same actual response.
No padding, bounded-graph replacement, deleted parallel arcs, renamed user IDs,
refitted bank, or supplied desired law equality. The exact old relabelling
providers are instantiated at the actual census-derived equivalences.
Outer-labelled planarity admission and independent algebraic source parameters
are separate obligations; they are not asserted by this carrier adapter.
Contributor: dot / OpenAI, 2026-10-10, reusing accepted prior source proofs.
DRAFT: uncompiled and unreviewed. -/
namespace GProgram.G7.OriginalCarrierCoverage
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.ControlledUnrankedSourceProjectivity
open UnifiedLean.Source.UnrankedGenealogyObservation
open GProgram.G7.OriginalFiniteEncoding GProgram.G7.OriginalRelabelling
open GProgram.G7.OriginalFamilyStrategy
open scoped Classical
universe u v w
variable {X : Type w} {ID : Type*} [Fintype X] [Fintype ID]

/-- An actual original source point may use arbitrary finite carrier types.
All original IDs are present; the bank/calendar are shared across all rows. -/
structure OriginalPoint (X : Type w) (ID : Type*) [Fintype X] where
  source : G1ActualGraphNormalization.Source.{u,v,w} X
  ids : ID ≃ Hybrid source.network
  parents : OriginalParentRegistry source.network
  inheritance : HybridProbabilities source.network
  common : Bool
  rates : PositivePairRates source.Edge

noncomputable def fixedFamily :
    OriginalFamily (OriginalPoint.{u,v,w} X ID)
      (Fin (vertexCount (Fintype.card X) (Fintype.card ID)))
      (Fin (edgeCount (Fintype.card X) (Fintype.card ID))) X ID where
  network s := numberedSource s.source.network s.ids
  calendar s := calendar s.source.network (vertexNumbering s.source.network s.ids)
    (edgeNumbering s.source.network s.ids) s.source.calendar
  ids s := s.ids.trans (hybrids s.source.network (vertexNumbering s.source.network s.ids)
    (edgeNumbering s.source.network s.ids))
  parents s := registry s.source.network (vertexNumbering s.source.network s.ids)
    (edgeNumbering s.source.network s.ids) s.parents
  inheritance s := inheritance s.source.network (vertexNumbering s.source.network s.ids)
    (edgeNumbering s.source.network s.ids) s.inheritance
  common s := s.common
  rates s := rates (edgeNumbering s.source.network s.ids) s.rates

variable {Copy Row Obs Out A : Type*} [Fintype Copy] [DecidableEq Copy] [Nonempty Copy]
variable [Fintype Row] [Fintype Obs] [Fintype Out]

noncomputable def originalRowLaw (sample : Copy → X) (rows : Row → ID → Option Bool)
    (observe : Finset (UnrankedTree Copy) → Obs) (s : OriginalPoint.{u,v,w} X ID)
    (row : Row) : PMF Obs :=
  (controlledCompletedUnrankedLaw s.source.network s.source.calendar sample s.parents
    s.inheritance (fun _ => s.common) s.rates (fun h => rows row (s.ids.symm h))).map observe

/-- Every original source law on arbitrary finite carriers is represented on
the exact V/E census carriers, simultaneously for every same original-ID row.
The finite carrier bound is derived; it is not a hidden model restriction. -/
theorem every_original_row_has_fixed_carrier_response (sample : Copy → X)
    (rows : Row → ID → Option Bool) (observe : Finset (UnrankedTree Copy) → Obs)
    (s : OriginalPoint.{u,v,w} X ID) (row : Row) :
    originalRowLaw sample rows observe s row =
      rowLaw fixedFamily sample rows observe s row := by
  have he := GProgram.G7.OriginalControlRelabelling.controlled_completed_unranked
    s.source.network (vertexNumbering s.source.network s.ids)
    (edgeNumbering s.source.network s.ids) s.source.calendar sample s.parents
    s.inheritance (fun _ => s.common) s.rates (fun h => rows row (s.ids.symm h))
  have mapped := congrArg (fun law => law.map observe) he
  simpa only [originalRowLaw,rowLaw,fixedFamily,numberedSource,
    GProgram.G7.CalendarNodeRelabelling.common,
    GProgram.G7.OriginalControlRelabelling.named_mask] using mapped

noncomputable def originalProgrammeLaw (sample : Copy → X)
    (rows : Row → ID → Option Bool) (observe : Finset (UnrankedTree Copy) → Obs)
    (programme : A → Programme Row Obs Out) (s : OriginalPoint.{u,v,w} X ID) (a : A) : PMF Out :=
  ((programme a).weights).bind fun row =>
    (originalRowLaw sample rows observe s row).bind ((programme a).channel row)

/-- Literal pre-source programme randomization and the complete output law
are preserved for every original parameter point, with one shared bank. -/
theorem every_original_programme_has_fixed_carrier_response (sample : Copy → X)
    (rows : Row → ID → Option Bool) (observe : Finset (UnrankedTree Copy) → Obs)
    (programme : A → Programme Row Obs Out) (s : OriginalPoint.{u,v,w} X ID) (a : A) :
    originalProgrammeLaw sample rows observe programme s a =
      programmeLaw fixedFamily sample rows observe programme s a := by
  simp only [originalProgrammeLaw,programmeLaw,every_original_row_has_fixed_carrier_response]

end GProgram.G7.OriginalCarrierCoverage
