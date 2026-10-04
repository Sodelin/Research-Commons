import G1UnrankedActualBoundary

/-! The SAME original future process factors through the complete rooted
UNRANKED causal interface. Contributor: dot, 2026-10-03. -/
namespace G1UnrankedActualFuture
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceForestSilentPruning
open UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.UnrankedGenealogyObservation
open G1UnrankedSourceView G1UnrankedActualGenerator G1UnrankedActualEpoch G1UnrankedActualBoundary
open scoped Classical NNReal
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

noncomputable def unrankedProgramStep (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (op : ProgramStep N)
    (v : UnrankedIndex N sample keep) : PMF (UnrankedIndex N sample keep) :=
  match op with
  | .interval t => unrankedTimeKernel N r keep t v
  | .boundary b => unrankedBoundary N keep b v

theorem actual_unranked_program_step (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (op : ProgramStep N) (s : Code N sample) :
    (sourceProgramStep N r op s).map (unrankedProjection N keep) =
      unrankedProgramStep N r keep op (unrankedProjection N keep s) := by
  cases op with
  | interval t => exact actual_unranked_time_kernel N r keep t s
  | boundary b => exact actual_unranked_source_boundary N keep b s

noncomputable def unrankedProgram (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) :
    List (ProgramStep N) → UnrankedIndex N sample keep → PMF (UnrankedIndex N sample keep)
  | [], v => PMF.pure v
  | op :: ops, v => (unrankedProgramStep N r keep op v).bind (unrankedProgram N r keep ops)

/-- Full original rates, parents, private current-owner coin laws and SAME
common register are retained through EVERY actual original future operation. -/
theorem actual_unranked_source_program (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (keep : Finset Copy) (future : List (ProgramStep N)) (s : Code N sample) :
    (sourceProgram N r future s).map (unrankedProjection N keep) =
      unrankedProgram N r keep future (unrankedProjection N keep s) := by
  induction future generalizing s with
  | nil => simp [sourceProgram,unrankedProgram,PMF.pure_map]
  | cons op ops ih =>
      rw [sourceProgram,PMF.map_bind]
      simp_rw [ih]
      change (sourceProgramStep N r op s).bind (unrankedProgram N r keep ops ∘ unrankedProjection N keep) = _
      rw [← PMF.bind_map,actual_unranked_program_step]
      rfl

/-- Actual future row invariance under only the exact rooted UNRANKED
clade/population/register interface. Hidden current IDs and child orientations
cannot influence any subsequent allowed unranked observer. -/
theorem actual_unranked_future_row_independent {Obs : Type*} (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (future : List (ProgramStep N)) (s z : Code N sample)
    (h : unrankedView (selectedView (state s) keep) = unrankedView (selectedView (state z) keep))
    (readout : UnrankedView V E Copy → Obs) :
    (sourceProgram N r future s).map (fun d => readout (unrankedView (selectedView (state d) keep))) =
      (sourceProgram N r future z).map (fun d => readout (unrankedView (selectedView (state d) keep))) := by
  have he : unrankedProjection N keep s = unrankedProjection N keep z := Subtype.ext h
  have hs := congrArg (fun p => p.map (fun v : UnrankedIndex N sample keep => readout v.val))
    (actual_unranked_source_program N r keep future s)
  have hz := congrArg (fun p => p.map (fun v : UnrankedIndex N sample keep => readout v.val))
    (actual_unranked_source_program N r keep future z)
  simp only [PMF.map_comp,Function.comp_def] at hs hz
  rw [he] at hs
  exact hs.trans hz.symm

noncomputable def unrankedViewForest (v : UnrankedView V E Copy) : Finset (UnrankedTree Copy) :=
  Finset.univ.biUnion (fun x => match v.genealogy x with | none => ∅ | some q => {q})

theorem actual_unranked_view_forest (v : SelectedView V E Copy) :
    unrankedForest v = unrankedViewForest (unrankedView v) := by
  unfold unrankedForest unrankedViewForest
  congr 1
  funext x
  cases hx : v.genealogy x <;> simp [unrankedView,optionUnranked,hx]

theorem actual_same_original_unranked_forest_future (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (future : List (ProgramStep N)) (s z : Code N sample)
    (h : unrankedView (selectedView (state s) keep) = unrankedView (selectedView (state z) keep)) :
    (sourceProgram N r future s).map (fun d => sourceUnrankedForest (state d) keep) =
      (sourceProgram N r future z).map (fun d => sourceUnrankedForest (state d) keep) := by
  simpa only [sourceUnrankedForest,actual_unranked_view_forest] using
    actual_unranked_future_row_independent N r keep future s z h unrankedViewForest

#print axioms actual_unranked_source_program
#print axioms actual_same_original_unranked_forest_future
end G1UnrankedActualFuture
