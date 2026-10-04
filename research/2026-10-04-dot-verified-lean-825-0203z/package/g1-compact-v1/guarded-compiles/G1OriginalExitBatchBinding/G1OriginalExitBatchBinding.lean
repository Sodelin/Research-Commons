import G1OriginalNodeBatchBinding

/-! Exact original edge-exit batch binding, including both parallel arms.
Contributor: dot, 2026-10-03. The original whole source processes every exit;
its inside genealogy/register is unchanged and all inside labels arrive at
the SAME original upper node. Equality to canonical exits is DERIVED. -/
namespace G1OriginalExitBatchBinding
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceBoundaryLocations
open UnifiedLean.Source.SourceBoundaryProjection UnifiedLean.Source.SourceFiniteProjection
open UnifiedLean.Source.SourceForestSilentPruning
open G1OriginalEpochPanelSilence G1OriginalNodeBatchBinding
open scoped Classical
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

noncomputable def exitCodeList (N : RootedBinary V E X) {sample : Copy → X} :
    List E → Code N sample → Code N sample
  | [],s => s
  | e::es,s => exitCodeList N es (exitCode N s e)

noncomputable def exitLocationList (N : RootedBinary V E X) : List E → Location V E → Location V E
  | [],p => p
  | e::es,p => exitLocationList N es (exitLocation N e p)

lemma actual_exit_list_program (N : RootedBinary V E X) {sample : Copy → X}
    (r : UnifiedLean.Source.NativePairClockLaw.PositivePairRates E) (es : List E) (s : Code N sample) :
    sourceProgram N r (es.map (fun e => .boundary (.exit e))) s = PMF.pure (exitCodeList N es s) := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih => simpa [sourceProgram,sourceProgramStep,boundaryKernel,exitCodeList] using ih (exitCode N s e)

lemma actual_exit_list_copy_location (N : RootedBinary V E X) {sample : Copy → X}
    (es : List E) (s : Code N sample) (x : Copy) :
    copyLocation (state (exitCodeList N es s)) x = exitLocationList N es (copyLocation (state s) x) := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
      simp only [exitCodeList,exitLocationList]
      rw [ih,exitCode_copyLocation]

lemma actual_exit_location_list_node (N : RootedBinary V E X) (es : List E) (v : V) :
    exitLocationList N es (.node v) = .node v := by
  induction es with
  | nil => rfl
  | cons e es ih => simpa [exitLocationList,exitLocation] using ih

lemma actual_exit_location_list_hit (N : RootedBinary V E X) (es : List E) (e : E) (he : e ∈ es) :
    exitLocationList N es (.edge e) = .node (N.graph.source e) := by
  induction es with
  | nil => exact False.elim (List.not_mem_nil he)
  | cons f fs ih =>
      by_cases hf : f = e
      · subst f
        simp [exitLocationList,exitLocation,actual_exit_location_list_node]
      · have hm : e ∈ fs := (List.mem_cons.mp he).resolve_left (Ne.symm hf)
        simpa [exitLocationList,exitLocation,Ne.symm hf] using ih hm

lemma actual_exit_list_genealogy (N : RootedBinary V E X) {sample : Copy → X}
    (es : List E) (s : Code N sample) (keep : Finset Copy) :
    (selectedView (state (exitCodeList N es s)) keep).genealogy = (selectedView (state s) keep).genealogy := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
      simp only [exitCodeList]
      rw [ih,exitCode_view]
      rfl

lemma actual_exit_list_register (N : RootedBinary V E X) {sample : Copy → X}
    (es : List E) (s : Code N sample) (keep : Finset Copy) :
    (selectedView (state (exitCodeList N es s)) keep).register = (selectedView (state s) keep).register := by
  induction es generalizing s with
  | nil => rfl
  | cons e es ih =>
      simp only [exitCodeList]
      rw [ih,exitCode_view]
      rfl

lemma actual_exit_list_same_upper (N : RootedBinary V E X) {sample : Copy → X}
    (es : List E) (s : Code N sample) (keep : Finset Copy) (edges : Finset E) (U : V)
    (hs : AtEdgePanel (state s) keep edges) (hsource : ∀ e ∈ edges, N.graph.source e = U)
    (hcover : ∀ e ∈ edges, e ∈ es) :
    selectedView (state (exitCodeList N es s)) keep =
      transportView (selectedView (state s) keep) (fun _ => .node U) := by
  apply SelectedView.ext
  · exact actual_exit_list_genealogy N es s keep
  · funext x
    by_cases hx : x ∈ keep
    · obtain ⟨e,he,hpop⟩ := hs x hx
      have hnew : copyLocation (state (exitCodeList N es s)) x = .node U := by
        rw [actual_exit_list_copy_location,hpop,actual_exit_location_list_hit N es e (hcover e he),hsource e he]
      simp [transportView,selectedView,selectedLocation,hx,hnew]
    · simp [transportView,selectedView,selectedLocation,hx]
  · exact actual_exit_list_register N es s keep

/-- Any complete ORIGINAL exit batch has the exact inside selected-state law
of any canonical exit list hitting all occupied original edges. It retains
whole genealogy/population/SAME-register data, not only scalar counts. -/
theorem actual_complete_exit_batch_inside_law (N : RootedBinary V E X) {sample : Copy → X}
    (r : UnifiedLean.Source.NativePairClockLaw.PositivePairRates E) (es canonical : List E)
    (s : Code N sample) (keep : Finset Copy) (edges : Finset E) (U : V)
    (hs : AtEdgePanel (state s) keep edges) (hsource : ∀ e ∈ edges, N.graph.source e = U)
    (hcover : ∀ e ∈ edges, e ∈ es) (hcanonical : ∀ e ∈ edges, e ∈ canonical) :
    (sourceProgram N r (es.map (fun e => .boundary (.exit e))) s).map (projection N keep) =
      (sourceProgram N r (canonical.map (fun e => .boundary (.exit e))) s).map (projection N keep) := by
  rw [actual_exit_list_program,actual_exit_list_program,PMF.pure_map,PMF.pure_map]
  congr 1
  apply Subtype.ext
  exact (actual_exit_list_same_upper N es s keep edges U hs hsource hcover).trans
    (actual_exit_list_same_upper N canonical s keep edges U hs hsource hcanonical).symm

end G1OriginalExitBatchBinding
