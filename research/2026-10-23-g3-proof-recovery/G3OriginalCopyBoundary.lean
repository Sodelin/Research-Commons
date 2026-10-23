import G3OriginalCopyEquivalence
import UnifiedLean.Source.SourceProgramTransport
import UnifiedLean.Source.SourceAncestralCompletion
import G2SourceFiniteHistory

/-!
UNCOMPILED source candidate, existing G3 owner,22October2026.
The literal original boundary/current-owner coin/word transport under a
copy bijection. Original vertices, edge occurrences, parent orientation,
rates, register and chronological word are fixed. This is not numerical
M/Phi identification, a fresh-source construction, or an observation claim.
-/
namespace G3OriginalCopyBoundary
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest MeasureTheory
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceForestPulseMeasure
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceEmbeddedJumpLaw UnifiedLean.Source.SourceAncestralCompletion
open GProgram.G2.SourceFiniteHistory G3OriginalCopyEquivalence
open scoped Classical NNReal

variable {A B V E X : Type*}
variable [DecidableEq A] [DecidableEq B] [Fintype A] [Fintype B]
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]

/-- The actual CURRENT AtNode roots are reindexed. An earlier merger gives
one owner and one coin, regardless of its number of original descendants. -/
noncomputable def fieldsAtNodeEquiv (e : A ≃ B) (u : State V E A) (v : State V E B)
    (h : CopyFields e u v) (node : V) : AtNode u node ≃ AtNode v node where
  toFun a := ⟨e a.val,by
    constructor
    · apply (copy_fields_live_iff e u v h _).mpr
      simpa only [Equiv.symm_apply_apply] using a.property.1
    · rw [h.location_eq,Equiv.symm_apply_apply]
      exact a.property.2⟩
  invFun b := ⟨e.symm b.val,
    ⟨(copy_fields_live_iff e u v h _).mp b.property.1,
      (h.location_eq b.val).symm.trans b.property.2⟩⟩
  left_inv a := by
    apply Subtype.ext
    exact e.symm_apply_apply a.val
  right_inv b := by
    apply Subtype.ext
    exact e.apply_symm_apply b.val

noncomputable def fieldsCoin (e : A ≃ B) (u : State V E A) (v : State V E B)
    (h : CopyFields e u v) (node : V) (coin : AtNode u node → Bool) :
    AtNode v node → Bool := fun b => coin ((fieldsAtNodeEquiv e u v h node).symm b)

theorem population_transport_copy_fields (e : A ≃ B)
    (u : State V E A) (v : State V E B) (h : CopyFields e u v)
    (f : Location V E → Location V E)
    (eventA : SourceEvent V E A) (eventB : SourceEvent V E B) :
    CopyFields e (transport u (f ∘ u.location) eventA)
      (transport v (f ∘ v.location) eventB) := by
  exact ⟨h.live_eq,h.ancestor_eq,h.genealogy_eq,
    fun b => congrArg f (h.location_eq b),h.register_eq⟩

/-- Deterministic original pulse commutation on actual fields, including
the dependent proof that each coin belongs to a CURRENT root at H.hybrid. -/
theorem pulse_copy_fields (N : RootedBinary V E X) (e : A ≃ B)
    (u : State V E A) (v : State V E B) (h : CopyFields e u v)
    (H : GProgram.G2.OriginalHybridParents N) (coin : AtNode u H.hybrid → Bool) :
    CopyFields e (pulse H u coin)
      (pulse H v (fieldsCoin e u v h H.hybrid coin)) := by
  constructor
  · exact h.live_eq
  · exact h.ancestor_eq
  · exact h.genealogy_eq
  · intro b
    change (if hv : b ∈ v.live ∧ v.location b = .node H.hybrid then
        .edge (H.parent (fieldsCoin e u v h H.hybrid coin ⟨b,hv⟩)) else v.location b) =
      (if hu : e.symm b ∈ u.live ∧ u.location (e.symm b) = .node H.hybrid then
        .edge (H.parent (coin ⟨e.symm b,hu⟩)) else u.location (e.symm b))
    have hm : (b ∈ v.live ∧ v.location b = .node H.hybrid) ↔
        (e.symm b ∈ u.live ∧ u.location (e.symm b) = .node H.hybrid) := by
      rw [copy_fields_live_iff e u v h b,h.location_eq b]
    by_cases hb : b ∈ v.live ∧ v.location b = .node H.hybrid
    · rw [dif_pos hb,dif_pos (hm.mp hb)]
      rfl
    · have ha : ¬ (e.symm b ∈ u.live ∧ u.location (e.symm b) = .node H.hybrid) :=
        fun ha => hb (hm.mpr ha)
      rw [dif_neg hb,dif_neg ha]
      exact h.location_eq b
  · exact h.register_eq

noncomputable def originalAtNodeEquiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (node : V) :
    AtNode (state s) node ≃ AtNode (state (originalCodeEquiv N e sample s)) node :=
  fieldsAtNodeEquiv e _ _ (decode_copy_fields N.root e s.val) node

noncomputable def originalCoin (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (node : V)
    (coin : AtNode (state s) node → Bool) :
    AtNode (state (originalCodeEquiv N e sample s)) node → Bool :=
  fieldsCoin e _ _ (decode_copy_fields N.root e s.val) node coin

theorem original_exitCode_copy_equiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (edge : E) :
    originalCodeEquiv N e sample (exitCode N s edge) =
      exitCode N (originalCodeEquiv N e sample s) edge := by
  apply original_admittedCode_copy_equiv
  exact population_transport_copy_fields e _ _ (decode_copy_fields N.root e s.val)
    (exitLocation N edge) (.edgeExit edge) (.edgeExit edge)

theorem original_ordinaryCode_copy_equiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (edge : E) :
    originalCodeEquiv N e sample (ordinaryCode N s edge) =
      ordinaryCode N (originalCodeEquiv N e sample s) edge := by
  apply original_admittedCode_copy_equiv
  exact population_transport_copy_fields e _ _ (decode_copy_fields N.root e s.val)
    (ordinaryLocation N edge) (.ordinaryEntry edge) (.ordinaryEntry edge)

theorem original_rootCode_copy_equiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) :
    originalCodeEquiv N e sample (rootCode N s) =
      rootCode N (originalCodeEquiv N e sample s) := by
  apply original_admittedCode_copy_equiv
  exact population_transport_copy_fields e _ _ (decode_copy_fields N.root e s.val)
    (rootLocation N) (.rootEntry N.root) (.rootEntry N.root)

theorem original_pulseCode_copy_equiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (H : GProgram.G2.OriginalHybridParents N)
    (coin : AtNode (state s) H.hybrid → Bool) :
    originalCodeEquiv N e sample (pulseCode H s coin) =
      pulseCode H (originalCodeEquiv N e sample s)
        (originalCoin N e sample s H.hybrid coin) := by
  apply original_admittedCode_copy_equiv
  exact pulse_copy_fields N e _ _ (decode_copy_fields N.root e s.val) H coin

/-- Exact product-Bernoulli reindexing from the existing Pi measure theorem.
The original natural parameter gamma and current-owner count are retained. -/
theorem coin_reindex_measurePreserving {U W : Type*} [Fintype U] [Fintype W]
    (f : U ≃ W) (gamma : unitInterval) :
    MeasurePreserving (fun c : U → Bool => fun w : W => c (f.symm w))
      (independentCoinMeasure U gamma) (independentCoinMeasure W gamma) := by
  have he : (⇑(MeasurableEquiv.piCongrLeft (fun _ : W => Bool) f)) =
      (fun c : U → Bool => fun w : W => c (f.symm w)) := by
    funext c w
    simp [MeasurableEquiv.coe_piCongrLeft,Equiv.piCongrLeft_apply]
  have h := measurePreserving_piCongrLeft (fun _ : W => bitMeasure gamma) f
  rw [he] at h
  exact h

theorem currentCoinPMF_reindex {U W : Type*} [Fintype U] [Fintype W]
    (f : U ≃ W) (gamma : unitInterval) :
    (currentCoinPMF U gamma).map (fun c : U → Bool => fun w : W => c (f.symm w)) =
      currentCoinPMF W gamma := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  simp only [currentCoinPMF,Measure.toPMF_toMeasure]
  exact (coin_reindex_measurePreserving f gamma).map_eq

theorem original_independentPulse_copy_equiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (H : GProgram.G2.OriginalHybridParents N)
    (gamma : unitInterval) :
    (independentPulseKernel H gamma s).map (originalCodeEquiv N e sample) =
      independentPulseKernel H gamma (originalCodeEquiv N e sample s) := by
  have hc : (currentCoinPMF (AtNode (state s) H.hybrid) gamma).map
      (originalCoin N e sample s H.hybrid) =
      currentCoinPMF (AtNode (state (originalCodeEquiv N e sample s)) H.hybrid) gamma :=
    currentCoinPMF_reindex (originalAtNodeEquiv N e sample s H.hybrid) gamma
  simp only [independentPulseKernel,PMF.map_comp]
  rw [← hc,PMF.map_comp]
  congr 1
  funext coin
  exact original_pulseCode_copy_equiv N e sample s H coin

/-- ALL literal original boundary operations. COMMON uses the same stored
original bit; its constant coin function is reindexed, never resampled. -/
theorem original_boundaryKernel_copy_equiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (op : BoundaryOperation N) :
    (boundaryKernel N op s).map (originalCodeEquiv N e sample) =
      boundaryKernel N op (originalCodeEquiv N e sample s) := by
  cases op with
  | exit edge =>
      simp only [boundaryKernel,PMF.pure_map]
      exact congrArg PMF.pure (original_exitCode_copy_equiv N e sample s edge)
  | ordinary edge hd =>
      simp only [boundaryKernel,PMF.pure_map]
      exact congrArg PMF.pure (original_ordinaryCode_copy_equiv N e sample s edge)
  | root =>
      simp only [boundaryKernel,PMF.pure_map]
      exact congrArg PMF.pure (original_rootCode_copy_equiv N e sample s)
  | independent H gamma =>
      exact original_independentPulse_copy_equiv N e sample s H gamma
  | common H =>
      simp only [boundaryKernel,PMF.pure_map]
      exact congrArg PMF.pure (original_pulseCode_copy_equiv N e sample s H
        (fun _ => (state s).register H.hybrid))

theorem original_programStep_copy_equiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (r : PositivePairRates E) (op : ProgramStep N) :
    (sourceProgramStep N r op s).map (originalCodeEquiv N e sample) =
      sourceProgramStep N r op (originalCodeEquiv N e sample s) := by
  cases op with
  | interval t => exact original_sourceTimeKernel_copy_equiv N e sample s r t
  | boundary b => exact original_boundaryKernel_copy_equiv N e sample s b

/-- The SAME original chronological word, full raw output law and register.
No operation reordering, fresh ID, graph reduction or word bound is used. -/
theorem original_program_copy_equiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (r : PositivePairRates E)
    (ops : List (ProgramStep N)) :
    (sourceProgram N r ops s).map (originalCodeEquiv N e sample) =
      sourceProgram N r ops (originalCodeEquiv N e sample s) := by
  induction ops generalizing s with
  | nil => simp only [sourceProgram,PMF.pure_map]
  | cons op ops ih =>
      simp only [sourceProgram,PMF.map_bind]
      simp_rw [ih]
      change (sourceProgramStep N r op s).bind
          ((sourceProgram N r ops) ∘ originalCodeEquiv N e sample) =
        (sourceProgramStep N r op (originalCodeEquiv N e sample s)).bind (sourceProgram N r ops)
      rw [← PMF.bind_map,original_programStep_copy_equiv]

/-- Existing finite endpoint-history transport, supplied by the actual rows
above. This does not expose a private register or marked clock as an observer. -/
theorem original_sourceHistory_copy_equiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (r : PositivePairRates E)
    (ops : List (ProgramStep N)) :
    (sourceHistoryLaw N r ops s).map (historyProjection (originalCodeEquiv N e sample)) =
      sourceHistoryLaw N r ops (originalCodeEquiv N e sample s) := by
  exact history_projection (sourceProgramStep N r) (sourceProgramStep N r)
    (originalCodeEquiv N e sample)
    (fun op d => original_programStep_copy_equiv N e sample d r op) ops s

/-- Actual embedded real-merger weights, including genuine zero-rate
absorption. These are not uniformization holding counts. -/
theorem original_jumpMass_copy_equiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (r : PositivePairRates E)
    (q : Option (Choice N s)) :
    jumpMass N r (originalCodeEquiv N e sample s)
      (originalOptionChoiceEquiv N e sample s q) = jumpMass N r s q := by
  cases q with
  | none =>
      change (if totalRate N r (originalCodeEquiv N e sample s) = 0 then 1 else 0) =
        (if totalRate N r s = 0 then 1 else 0)
      rw [original_totalRate_copy_equiv]
  | some p =>
      change (pairRate r p.1/2)/totalRate N r (originalCodeEquiv N e sample s) =
        (pairRate r p.1/2)/totalRate N r s
      rw [original_totalRate_copy_equiv]

theorem original_sourceJumpChoice_copy_equiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (r : PositivePairRates E) :
    (sourceJumpChoice N r s).map (originalOptionChoiceEquiv N e sample s) =
      sourceJumpChoice N r (originalCodeEquiv N e sample s) := by
  apply PMF.ext
  intro q
  rw [pmf_map_equiv_apply,sourceJumpChoice_apply,sourceJumpChoice_apply]
  have hm := original_jumpMass_copy_equiv N e sample s r
    ((originalOptionChoiceEquiv N e sample s).symm q)
  rw [Equiv.apply_symm_apply] at hm
  exact congrArg ENNReal.ofReal hm.symm

theorem original_sourceJumpStep_copy_equiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (r : PositivePairRates E) :
    (sourceJumpStep N r s).map (originalCodeEquiv N e sample) =
      sourceJumpStep N r (originalCodeEquiv N e sample s) := by
  simp only [sourceJumpStep,PMF.map_comp]
  rw [← original_sourceJumpChoice_copy_equiv N e sample s r,PMF.map_comp]
  congr 1
  funext q
  exact original_stepDestination_copy_equiv N e sample s q

theorem original_ancestralCompletion_copy_equiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (r : PositivePairRates E) (k : Nat) :
    (ancestralCompletion N r k s).map (originalCodeEquiv N e sample) =
      ancestralCompletion N r k (originalCodeEquiv N e sample s) := by
  induction k generalizing s with
  | zero => simp only [ancestralCompletion,PMF.pure_map]
  | succ k ih =>
      simp only [ancestralCompletion,PMF.map_bind]
      simp_rw [ih]
      change (sourceJumpStep N r s).bind
          ((ancestralCompletion N r k) ∘ originalCodeEquiv N e sample) =
        (sourceJumpStep N r (originalCodeEquiv N e sample s)).bind (ancestralCompletion N r k)
      rw [← PMF.bind_map,original_sourceJumpStep_copy_equiv]

/-- The supplied finite completion budget is identical. A copy bijection
preserves the total carrier size when the existing finish uses that budget. -/
theorem original_completedProgram_copy_equiv (N : RootedBinary V E X) (e : A ≃ B)
    (sample : A → X) (s : Code N sample) (r : PositivePairRates E)
    (ops : List (ProgramStep N)) (k : Nat) :
    ((sourceProgram N r ops s).bind (ancestralCompletion N r k)).map
        (originalCodeEquiv N e sample) =
      (sourceProgram N r ops (originalCodeEquiv N e sample s)).bind
        (ancestralCompletion N r k) := by
  rw [PMF.map_bind]
  simp_rw [original_ancestralCompletion_copy_equiv N e sample]
  change (sourceProgram N r ops s).bind
      ((ancestralCompletion N r k) ∘ originalCodeEquiv N e sample) = _
  rw [← PMF.bind_map,original_program_copy_equiv]

#print axioms original_pulseCode_copy_equiv
#print axioms currentCoinPMF_reindex
#print axioms original_boundaryKernel_copy_equiv
#print axioms original_program_copy_equiv
#print axioms original_sourceHistory_copy_equiv
#print axioms original_ancestralCompletion_copy_equiv
#print axioms original_completedProgram_copy_equiv
end G3OriginalCopyBoundary
