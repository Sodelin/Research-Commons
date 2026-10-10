import G6OriginalParallelArmTransport
import G6OriginalPopulationExposure
import G6OriginalCommonPrefix
import PrivateSeedHistoryFactorization
import ActualUnusedSeedConditioning
import G1ActualJointProgram
import UnifiedLean.Source.SourceEpochSemigroup

/-!
Codex Lean reuse, 10 October 2026. PROPOSAL; no kernel receipt yet.

Finite actual original COMMON factorization at a local nonroot parallel bigon.
The initializer is the unchanged original natural register draw. Its stored
bit remains the COMMON selector through the actual prefix; it is not redrawn.
The entire erased initialized endpoint vector (including its entering Code)
is retained as Old. Its product with the unused seed is the accepted actual
private-seed history theorem, not an independence premise.

This is a LOCAL carrier theorem: every live owner on the actual entering-law
support is at the named original hybrid. Full carried rooted labelled unranked
genealogy and all other register slots are retained. Applying it to one cohort
of a larger source requires the accepted restricted-copy/context replacement
interface; other active populations are never silently rescaled.

Both positive arm exposures are moved to a unit-rate reference population by
the accepted full-Code exposure theorem and exact original arm automorphism.
The minimum exposure is a positive baseline. The residual can be zero, where
the epoch is algebraic identity; this does not construct a positive physical
identity edge. The output forgets the private seed before reading a full forest.
Further COMMON reads of it are excluded by the separately stated no-read
future guard. Global positive-chain construction, timed histories and arbitrary
bin grammars are not consequences of this endpoint factorization.
-/
namespace GProgram.G6.NaturalCommonForestFactorization

set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5
open G1NonrootBigonKernel G1ContextualForestReplacement G1ActualJointProgram
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceEpochSemigroup
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceForestPulseMeasure
open UnifiedLean.Source.UnrankedGenealogyObservation
open UnifiedLean.G6.PrivateRegisterErasure UnifiedLean.G6.PrivateRegisterBoundary
open UnifiedLean.G6.PrivateRegisterProgram UnifiedLean.G6.PrivateRegisterHistory
open GProgram.G2.SourceFiniteHistory
open CloudG6.PrivateSeedFactorization CloudG6.PrivateSeedHistoryFactorization
open DotG34.ActualUnusedSeedConditioning
open MeasureTheory ProbabilityTheory
open GProgram.G7.SinglePopulationPolynomialKernel
open GProgram.G6.OriginalParallelArmTransport GProgram.G6.OriginalPopulationExposure
open GProgram.G6.OriginalCommonPrefix
open scoped Classical NNReal

variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq V] [DecidableEq E]
variable [Fintype Copy] [DecidableEq Copy]

/-- A reader of the already defined finite endpoint record, not a new process. -/
def recordEnd {A : Type*} : (n : Nat) → A → (Fin n → A) → A
  | 0, s, _ => s
  | n + 1, _, z => z (Fin.last n)

theorem recordEnd_map {A D : Type*} (f : A → D) (n : Nat) (s : A) (z : Fin n → A) :
    recordEnd n (f s) (historyProjection f z) = f (recordEnd n s z) := by
  cases n <;> rfl

noncomputable def erasedRecord (N : RootedBinary V E X) {sample : Copy → X}
    (P : Finset V) {n : Nat} (a : Code N sample × (Fin n → Code N sample)) :=
  (erasePrivateCode N P a.1, historyProjection (erasePrivateCode N P) a.2)

noncomputable def forestRegister (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) : (V → Bool) × Finset (UnrankedTree Copy) :=
  ((state s).register, rootForest N s)

noncomputable def erasedForestRegister (N : RootedBinary V E X) {sample : Copy → X}
    (P : Finset V) (s : Code N sample) : (V → Bool) × Finset (UnrankedTree Copy) :=
  forestRegister N (erasePrivateCode N P s)

noncomputable def unitRates : PositivePairRates E :=
  ⟨fun _ => 1, fun _ => zero_lt_one, 1, zero_lt_one⟩

noncomputable def armExposure (N : RootedBinary V E X) (B : NonrootBigon N)
    (r : PositivePairRates E) (t : ℝ≥0) (b : Bool) : ℝ≥0 :=
  ⟨r.edge (B.parents.parent b) * (t : ℝ), mul_nonneg (r.edge_pos _).le t.nonneg⟩

noncomputable def referencePulse (N : RootedBinary V E X) (B : NonrootBigon N)
    {sample : Copy → X} (s : Code N sample) : Code N sample :=
  pulseCode B.parents s (fun _ => false)

noncomputable def residualEpoch (N : RootedBinary V E X) {sample : Copy → X}
    (delta : ℝ≥0) (longArm b : Bool) (s : Code N sample) : PMF (Code N sample) :=
  if b = longArm then sourceTimeKernel N unitRates delta s else PMF.pure s

theorem actual_arm_exposure_positive (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : NonrootBigon N) (r : PositivePairRates E) (b : Bool) :
    0 < armExposure N B r (bigonDuration N C B) b := by
  change 0 < r.edge (B.parents.parent b) * (bigonDuration N C B : ℝ)
  exact mul_pos (r.edge_pos _) (NNReal.coe_pos.mpr (actual_bigon_duration_positive N C B))

private theorem constant_pulse_coLocated (N : RootedBinary V E X)
    (B : NonrootBigon N) {sample : Copy → X} (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node B.parents.hybrid)
    (b : Bool) : CoLocated N (pulseCode B.parents s (fun _ => b)) (some (B.parents.parent b)) := by
  intro x
  have hx : (state s).ancestor x ∈ (state s).live ∧
      (state s).location ((state s).ancestor x) = .node B.parents.hybrid :=
    ⟨s.property.forest.ancestor_live x, hinput _ (s.property.forest.ancestor_live x)⟩
  change copyLocation (state (pulseCode B.parents s (fun _ => b))) x = .edge (B.parents.parent b)
  rw [show copyLocation (state (pulseCode B.parents s (fun _ => b))) x =
      copyLocation (pulse B.parents (state s) (fun _ => b)) x from
    decode_encode_copyLocation N.root _ (pulse_source_valid B.parents sample _ s.property _).forest x]
  exact pulse_routes_current_ancestor B.parents (state s) (fun _ => b)
    ⟨(state s).ancestor x, hx⟩

private theorem unit_rate_swap (N : RootedBinary V E X) (B : NonrootBigon N) :
    GProgram.G7.OriginalRelabelling.rates (edgeSwap N B) (unitRates : PositivePairRates E) =
      unitRates := by
  rfl

/-- Every original conditional arm, arbitrary carried genealogy, exact erased
full register, and its physical exposure share ONE reference population name. -/
theorem actual_arm_erased_reference (N : RootedBinary V E X) (B : NonrootBigon N)
    {sample : Copy → X} (P : Finset V) (r : PositivePairRates E) (t : ℝ≥0)
    (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node B.parents.hybrid)
    (b : Bool) :
    (sourceTimeKernel N r t (pulseCode B.parents s (fun _ => b))).map
        (erasedForestRegister N P) =
      (sourceTimeKernel N unitRates (armExposure N B r t b)
        (referencePulse N B (erasePrivateCode N P s))).map (forestRegister N) := by
  have hi : ∀ l ∈ (state (erasePrivateCode N P s)).live,
      (state (erasePrivateCode N P s)).location l = .node B.parents.hybrid := hinput
  have he := original_epoch_eq_of_exposure_eq N
    (pulseCode B.parents (erasePrivateCode N P s) (fun _ => b))
    (some (B.parents.parent b)) (constant_pulse_coLocated N B _ hi b)
    r unitRates t (armExposure N B r t b) (by
      simp only [pairRate, unitRates, armExposure, one_mul])
  change ((sourceTimeKernel N r t (pulseCode B.parents s (fun _ => b))).map
    ((forestRegister N) ∘ erasePrivateCode N P)) = _
  rw [← PMF.map_comp, actual_sourceTimeKernel_erasure, erase_pulseCode, he]
  cases b with
  | false => rfl
  | true =>
      have h := actual_parallel_arm_full_forest_transport N B unitRates
        (armExposure N B r t true) (erasePrivateCode N P s) hi true
      rw [unit_rate_swap] at h
      exact h

private theorem exit_forest_register (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e : E) : forestRegister N (exitCode N s e) = forestRegister N s := by
  apply Prod.ext
  · rfl
  · change rootForest N (exitCode N s e) = rootForest N s
    unfold rootForest
    change (state s).live.image (fun l => toUnranked ((state (exitCode N s e)).genealogy l)) = _
    apply Finset.image_congr
    intro l hl
    congr 1
    change (decodeSnapshot N.root (encodeSnapshot (exitEdge N (state s) e) _)).genealogy l = _
    exact decode_encode_live_genealogy N.root (exitEdge N (state s) e) _ hl

private theorem exit_erased_forest_register (N : RootedBinary V E X) {sample : Copy → X}
    (P : Finset V) (s : Code N sample) (e : E) :
    erasedForestRegister N P (exitCode N s e) = erasedForestRegister N P s := by
  unfold erasedForestRegister
  rw [erase_exitCode, exit_forest_register]

/-- A fixed input executes its stored COMMON bit. There is no Bernoulli
mixture for this fixed Code; the natural mixture is derived below. -/
theorem actual_common_erased_reference (N : RootedBinary V E X)
    (C : Calendar N.graph) (B : NonrootBigon N) {sample : Copy → X}
    (P : Finset V) (r : PositivePairRates E) (gamma : unitInterval) (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node B.parents.hybrid) :
    (sourceProgram N r (bigonProgram N C B gamma true) s).map (erasedForestRegister N P) =
      (sourceTimeKernel N unitRates
        (armExposure N B r (bigonDuration N C B) ((state s).register B.parents.hybrid))
        (referencePulse N B (erasePrivateCode N P s))).map (forestRegister N) := by
  rw [actual_bigon_program_kernel]
  simp only [bigonPulse, ite_true, boundaryKernel, PMF.pure_bind, PMF.map_comp]
  have hf : (fun d : Code N sample => erasedForestRegister N P
      (exitCode N (exitCode N d B.parents.parent0) B.parents.parent1)) =
        erasedForestRegister N P := by
    funext d
    rw [exit_erased_forest_register, exit_erased_forest_register]
  change (sourceTimeKernel N r (bigonDuration N C B)
    (pulseCode B.parents s (fun _ => (state s).register B.parents.hybrid))).map
      (fun d => erasedForestRegister N P
        (exitCode N (exitCode N d B.parents.parent0) B.parents.parent1)) = _
  rw [hf]
  exact actual_arm_erased_reference N B P r (bigonDuration N C B) s hinput _

private theorem source_history_register_support (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (ops : List (ProgramStep N))
    (s : Code N sample) {z : Fin ops.length → Code N sample}
    (hz : z ∈ (sourceHistoryLaw N r ops s).support) :
    ∀ i, (state (z i)).register = (state s).register := by
  unfold sourceHistoryLaw at hz
  induction ops generalizing s with
  | nil => intro i; exact Fin.elim0 i
  | cons op ops ih =>
      obtain ⟨d, hd, hz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hz
      obtain ⟨tr, ht, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
      have hr : (state d).register = (state s).register := by
        cases op with
        | interval t => exact actual_time_register_support N r t s hd
        | boundary op => exact actual_boundary_register_support N op s hd
      intro i
      refine Fin.cases hr (fun j => ?_) i
      exact (ih d ht j).trans hr

private theorem recordEnd_register_support (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E) (ops : List (ProgramStep N))
    (s : Code N sample) {z : Fin ops.length → Code N sample}
    (hz : z ∈ (sourceHistoryLaw N r ops s).support) :
    (state (recordEnd ops.length s z)).register = (state s).register := by
  cases ops with
  | nil => rfl
  | cons op ops => exact source_history_register_support N r (op :: ops) s hz _

/-- Explicit binding from the actual original initializer to its SAME stored
COMMON selector at the end of the prefix, including the empty prefix. -/
theorem actual_natural_stored_selector (N : RootedBinary V E X) (h : Hybrid N)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (prefix : List (ProgramStep N))
    {a : (PrivateHybrid N {h.val} → Bool) ×
      (Code N sample × (Fin prefix.length → Code N sample))}
    (ha : a ∈ (initializedSourceHistory N r prefix
      (naturalInitialJoint N {h.val} sample p)).support) :
    (state (recordEnd prefix.length a.2.1 a.2.2)).register h.val =
      a.1 ⟨h, Finset.mem_singleton_self _⟩ := by
  obtain ⟨a0, h0, ha⟩ := (PMF.mem_support_bind_iff _ _ _).mp ha
  obtain ⟨z, hz, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp ha
  obtain ⟨coin, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h0
  rw [recordEnd_register_support N r prefix _ hz]
  change originalRegister N coin h.val = coin h
  simp only [originalRegister, dif_pos h.property]

/-- The original private bit, marginalized rather than exposed as an observed
register, retains original gamma=P(true/parent1). -/
theorem actual_private_bit_law (N : RootedBinary V E X) (h : Hybrid N)
    (p : HybridProbabilities N) :
    (privateSeedPMF N {h.val} p).map (fun c => c ⟨h, Finset.mem_singleton_self _⟩) =
      (bitMeasure (originalGamma p h)).toPMF := by
  apply PMF.toMeasure_injective
  rw [← PMF.toMeasure_map _ _ (measurable_of_countable _)]
  unfold privateSeedPMF
  rw [MeasureTheory.Measure.toPMF_toMeasure, MeasureTheory.Measure.toPMF_toMeasure]
  apply MeasureTheory.Measure.ext_of_singleton
  intro b
  rw [MeasureTheory.Measure.map_apply (measurable_of_countable _) (measurableSet_singleton b)]
  exact private_seed_bit_mass N {h.val} p ⟨h, Finset.mem_singleton_self _⟩ b

private theorem actual_arm_baseline_residual (N : RootedBinary V E X)
    (B : NonrootBigon N) {sample : Copy → X} (r : PositivePairRates E) (t : ℝ≥0)
    (s : Code N sample) (longArm b : Bool)
    (hle : armExposure N B r t (!longArm) ≤ armExposure N B r t longArm) :
    sourceTimeKernel N unitRates (armExposure N B r t b) (referencePulse N B s) =
      (sourceTimeKernel N unitRates (armExposure N B r t (!longArm))
        (referencePulse N B s)).bind
          (residualEpoch N (armExposure N B r t longArm - armExposure N B r t (!longArm))
            longArm b) := by
  by_cases hb : b = longArm
  · subst b
    unfold residualEpoch
    rw [if_pos rfl, ← actual_source_time_add]
    rw [add_tsub_cancel_of_le hle]
  · have hb' : b = !longArm := by cases b <;> cases longArm <;> simp_all
    rw [hb']
    have hne : (!longArm) ≠ longArm := by cases longArm <;> decide
    simp only [residualEpoch, if_neg hne, PMF.bind_pure]

/-- Natural once-drawn COMMON, erased entire past, and complete forest/register
factorization. ONE positive minimum-exposure epoch precedes the original seed's
mixture of identity and the residual epoch. Old may be any reader of the whole
erased initialized vector; no observed-menu admission is inferred.

The local co-located support premise is explicit. It is not a claim that all
copies of an arbitrary whole network have reached this hybrid. -/
theorem actual_natural_common_erased_full_forest_factorization {Old : Type*}
    (N : RootedBinary V E X) (C : Calendar N.graph) (B : NonrootBigon N)
    (h : Hybrid N) (hsite : B.parents.hybrid = h.val)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (prefix : List (ProgramStep N)) (hprefix : NoPrivateWordRead N {h.val} prefix)
    (hinput : ∀ a ∈ (initializedSourceHistory N r prefix
      (naturalInitialJoint N {h.val} sample p)).support,
      ∀ l ∈ (state (recordEnd prefix.length a.2.1 a.2.2)).live,
        (state (recordEnd prefix.length a.2.1 a.2.2)).location l = .node B.parents.hybrid)
    (old : Code N sample × (Fin prefix.length → Code N sample) → Old)
    (longArm : Bool)
    (hle : armExposure N B r (bigonDuration N C B) (!longArm) ≤
      armExposure N B r (bigonDuration N C B) longArm) :
    (initializedSourceHistory N r prefix (naturalInitialJoint N {h.val} sample p)).bind
      (fun a => (sourceProgram N r (bigonProgram N C B (originalGamma p h) true)
        (recordEnd prefix.length a.2.1 a.2.2)).map
          (fun d => (old (erasedRecord N {h.val} a.2), erasedForestRegister N {h.val} d))) =
    (initializedEndpointLaw N r prefix (outsideInitialCodeLaw N {h.val} sample p)).bind
      (fun a => (sourceTimeKernel N unitRates
        (armExposure N B r (bigonDuration N C B) (!longArm))
        (referencePulse N B (recordEnd prefix.length a.1 a.2))).bind
          (fun z => ((bitMeasure (originalGamma p h)).toPMF).bind
            (fun b => (residualEpoch N
              (armExposure N B r (bigonDuration N C B) longArm -
                armExposure N B r (bigonDuration N C B) (!longArm))
              longArm b z).map
                (fun d => (old a, forestRegister N d))))) := by
  let J := initializedSourceHistory N r prefix (naturalInitialJoint N {h.val} sample p)
  let eraseJoint := fun a : (PrivateHybrid N {h.val} → Bool) ×
      (Code N sample × (Fin prefix.length → Code N sample)) =>
    (a.1, erasedRecord N {h.val} a.2)
  let row := fun a : (PrivateHybrid N {h.val} → Bool) ×
      (Code N sample × (Fin prefix.length → Code N sample)) =>
    (sourceTimeKernel N unitRates
      (armExposure N B r (bigonDuration N C B) (a.1 ⟨h, Finset.mem_singleton_self _⟩))
      (referencePulse N B (recordEnd prefix.length a.2.1 a.2.2))).map
        (fun d => (old a.2, forestRegister N d))
  have hrow : J.bind (fun a => (sourceProgram N r
        (bigonProgram N C B (originalGamma p h) true)
        (recordEnd prefix.length a.2.1 a.2.2)).map
          (fun d => (old (erasedRecord N {h.val} a.2), erasedForestRegister N {h.val} d))) =
      J.bind (row ∘ eraseJoint) := by
    apply bind_eq_of_eq_on_support
    intro a ha
    have he := actual_common_erased_reference N C B {h.val} r (originalGamma p h)
      (recordEnd prefix.length a.2.1 a.2.2) (hinput a ha)
    have hb := actual_natural_stored_selector N h sample p r prefix ha
    rw [← hsite] at hb
    rw [hb] at he
    have hp := congrArg (PMF.map (Prod.mk (old (erasedRecord N {h.val} a.2)))) he
    simp only [PMF.map_comp, Function.comp_def] at hp
    simpa only [row, eraseJoint, Function.comp_def, erasedRecord, recordEnd_map] using hp
  change J.bind _ = _
  rw [hrow, ← PMF.bind_map]
  have hj := actual_private_seed_erased_history_product N {h.val} sample p r prefix hprefix
  change J.map eraseJoint = _ at hj
  rw [hj]
  simp only [independentPMF, PMF.bind_bind, PMF.bind_map, Function.comp_def]
  rw [PMF.bind_comm (privateSeedPMF N {h.val} p)
    (initializedEndpointLaw N r prefix (outsideInitialCodeLaw N {h.val} sample p))]
  apply congrArg (PMF.bind (initializedEndpointLaw N r prefix
    (outsideInitialCodeLaw N {h.val} sample p)))
  funext a
  unfold row
  have hsplit (coin : PrivateHybrid N {h.val} → Bool) :=
    actual_arm_baseline_residual N B r (bigonDuration N C B)
      (recordEnd prefix.length a.1 a.2) longArm
      (coin ⟨h, Finset.mem_singleton_self _⟩) hle
  simp_rw [hsplit, PMF.map_bind]
  rw [PMF.bind_comm (privateSeedPMF N {h.val} p)
    (sourceTimeKernel N unitRates (armExposure N B r (bigonDuration N C B) (!longArm))
      (referencePulse N B (recordEnd prefix.length a.1 a.2)))]
  apply congrArg (PMF.bind (sourceTimeKernel N unitRates
    (armExposure N B r (bigonDuration N C B) (!longArm))
      (referencePulse N B (recordEnd prefix.length a.1 a.2))))
  funext z
  change (privateSeedPMF N {h.val} p).bind
    ((fun b : Bool => (residualEpoch N
      (armExposure N B r (bigonDuration N C B) longArm -
        armExposure N B r (bigonDuration N C B) (!longArm)) longArm b z).map
          (fun d => (old a, forestRegister N d))) ∘
      (fun coin => coin ⟨h, Finset.mem_singleton_self _⟩)) = _
  rw [← PMF.bind_map, actual_private_bit_law]

/-- A literal split of the actual tied-date node list supplies no-read at the
natural entering prefix. The chosen COMMON operation is the SAME registry
entry. The local entering population support is still an explicit construction
premise, as is the comparison of the two physical exposures. -/
theorem actual_tied_calendar_common_factorization {Old : Type*}
    (N : RootedBinary V E X) (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (B : NonrootBigon N) (h : Hybrid N) (hparents : H.parents h = B.parents)
    (sample : Copy → X) (p : HybridProbabilities N) (common : Hybrid N → Bool)
    (hc : common h = true) (r : PositivePairRates E)
    (pre post : List ℝ) (nodesBefore nodesAfter : List V)
    (hdates : UnifiedLean.Source.SourceCalendarCompiler.sortedOriginalDates N C =
      pre ++ C.age h.val :: post)
    (hnodes : (Finset.univ.filter (fun v : V => C.age v = C.age h.val)).toList =
      nodesBefore ++ h.val :: nodesAfter) :
    let prefix := beforeNodeWord N C H (originalGamma p) common h.val pre nodesBefore
    ∀ (hinput : ∀ a ∈ (initializedSourceHistory N r prefix
      (naturalInitialJoint N {h.val} sample p)).support,
      ∀ l ∈ (state (recordEnd prefix.length a.2.1 a.2.2)).live,
        (state (recordEnd prefix.length a.2.1 a.2.2)).location l = .node B.parents.hybrid)
    (old : Code N sample × (Fin prefix.length → Code N sample) → Old)
    (longArm : Bool)
    (hle : armExposure N B r (bigonDuration N C B) (!longArm) ≤
      armExposure N B r (bigonDuration N C B) longArm),
    UnifiedLean.Source.SourceCalendarCompiler.compiledCalendarProgram N C H (originalGamma p) common =
      prefix ++ [.boundary (.common B.parents)] ++
        nodesAfter.map (fun v => .boundary
          (UnifiedLean.Source.SourceCalendarCompiler.originalNodeOperation N H (originalGamma p) common v)) ++
        UnifiedLean.Source.SourceCalendarCompiler.calendarTail N C H (originalGamma p) common
          (C.age h.val) post ∧
    (initializedSourceHistory N r prefix (naturalInitialJoint N {h.val} sample p)).bind
      (fun a => (sourceProgram N r (bigonProgram N C B (originalGamma p h) true)
        (recordEnd prefix.length a.2.1 a.2.2)).map
          (fun d => (old (erasedRecord N {h.val} a.2), erasedForestRegister N {h.val} d))) =
    (initializedEndpointLaw N r prefix (outsideInitialCodeLaw N {h.val} sample p)).bind
      (fun a => (sourceTimeKernel N unitRates
        (armExposure N B r (bigonDuration N C B) (!longArm))
        (referencePulse N B (recordEnd prefix.length a.1 a.2))).bind
          (fun z => ((bitMeasure (originalGamma p h)).toPMF).bind
            (fun b => (residualEpoch N
              (armExposure N B r (bigonDuration N C B) longArm -
                armExposure N B r (bigonDuration N C B) (!longArm)) longArm b z).map
                (fun d => (old a, forestRegister N d))))) := by
  dsimp only
  intro hinput old longArm hle
  let prefix := beforeNodeWord N C H (originalGamma p) common h.val pre nodesBefore
  constructor
  · have hs := actual_compiled_before_common_split N C H (originalGamma p) common h hc
      pre post nodesBefore nodesAfter hdates hnodes
    rw [hparents] at hs
    exact hs
  · have hsite : B.parents.hybrid = h.val := by
      rw [← hparents]
      exact H.original_site h
    exact actual_natural_common_erased_full_forest_factorization N C B h hsite sample p r
      prefix (actual_before_node_noPrivateWordRead N C H (originalGamma p) common h.val
        pre post nodesBefore nodesAfter hdates hnodes) hinput old longArm hle

/-- Erasing the private bit before a permitted SAME-source future preserves
its endpoint readout. It does not identify arbitrary exterior inputs solely
from a forest; that step uses the accepted physical exit/context interface. -/
theorem actual_no_read_future_erased_full_forest (N : RootedBinary V E X)
    {sample : Copy → X} (P : Finset V) (r : PositivePairRates E)
    (future : List (ProgramStep N)) (hf : NoPrivateWordRead N P future)
    (s : Code N sample) :
    (sourceProgram N r future s).map (erasedForestRegister N P) =
      (sourceProgram N r future (erasePrivateCode N P s)).map (forestRegister N) := by
  change (sourceProgram N r future s).map ((forestRegister N) ∘ erasePrivateCode N P) = _
  rw [← PMF.map_comp, actual_sourceProgram_erasure N r P future hf s]

#print axioms actual_arm_exposure_positive
#print axioms actual_arm_erased_reference
#print axioms actual_common_erased_reference
#print axioms actual_natural_stored_selector
#print axioms actual_private_bit_law
#print axioms actual_natural_common_erased_full_forest_factorization
#print axioms actual_tied_calendar_common_factorization
#print axioms actual_no_read_future_erased_full_forest

end GProgram.G6.NaturalCommonForestFactorization
