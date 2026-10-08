import NaturalCalendarPastAdmission
import G1NonrootBigonKernel

/-!
Contributor: CLOUD-G6-SOL-ULTRA-20261007, delegated structural lane.
8 October 2026. UNCHECKED additive source, outside actual179.

The first two bodies specialize the actual naturally initialized guard-past
product to exact joint atom weights. They do not posit entering independence.
The final three bodies show that a COMMON pulse uses one stored ORIGINAL bit
and that the actual positive epoch preserves that selected original arm.
No cross-graph Code cast, word-kernel equality, compiler or master claim.
The required Natural provider is the explicit c2066c3e derivative, not an
unchecked historical namespace header; SOURCE-PINS.json identifies its bytes.
-/
namespace UnifiedLean.G6.GuardedCommonSeedFibre
set_option backward.isDefEq.respectTransparency false

open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.SourceNaturalInitialization UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.G6.PrivateRegisterErasure
open CloudG6.PrivateSeedFactorization CloudG6.PrivateSeedHistoryFactorization
open CloudG6.NaturalCalendarPastAdmission
open CloudG3.ActualCutJointLaw CloudG3.ActualObservationCutRefinement
open CloudG3.ActualCalendarEndpointHistory CloudG3.CompleteCalendarBinReadout
open G1NonrootBigonKernel
open scoped Classical NNReal

variable {V E Copy X Tag : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]

/-- The actual initial original compiler through the ENTIRE guard batch. -/
noncomputable def guardOps (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (guard : ℝ) (pre : List ℝ) : List (ProgramStep N) :=
  match pre ++ [guard] with
  | [] => []
  | a :: dates => boundaryOperations N C H (originalGamma p) common a ++
      calendarTail N C H (originalGamma p) common a dates

/-- This law keeps whole original Code and old tags, erasing only unused
private register slots. It is derived from the actual initializer/calendar. -/
noncomputable def outsideGuardLaw (N : RootedBinary V E X) (C : Calendar N.graph)
    (P : Finset V) (sample : Copy → X) (p : HybridProbabilities N)
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) : PMF (TaggedEndpoint (Tag := Tag) N sample) :=
  (outsideInitialCodeLaw N P sample p).bind (fun s =>
    calendarJointPMF N r bin hbin ops s
      (UnifiedLean.Source.SourceCalendarCompatibility.firstOriginalDate N C)
      (leafAgeMatrix N C sample))

noncomputable def guardedSeedTaggedLaw (N : RootedBinary V E X)
    (C : Calendar N.graph) (P : Finset V) (sample : Copy → X)
    (p : HybridProbabilities N) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) (ops : List (ProgramStep N)) :
    PMF ((PrivateHybrid N P → Bool) × TaggedEndpoint (Tag := Tag) N sample) :=
  (naturalSeedPastJoint N C P sample p r bin hbin ops).map
    (fun a => (a.1, (erasePrivateCode N P a.2.1, a.2.2)))

/-- A physical age guard and the actual sorted compiler derive the product.
Refinement and one-bin word contracts are the existing literal grammar gates. -/
theorem actual_guarded_seed_tag_product (N : RootedBinary V E X)
    (C : Calendar N.graph) (P : Finset V) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) (guard : ℝ) (pre post : List ℝ)
    (hprivate : ∀ v ∈ P, guard < C.age v)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: post)
    (word : List (ProgramStep N × Tag))
    (href : CutRefines N (guardOps N C H p common guard pre) (physicalOps N word))
    (hword : wordBinContract N bin word
      (UnifiedLean.Source.SourceCalendarCompatibility.firstOriginalDate N C)) :
    guardedSeedTaggedLaw N C P sample p r bin hbin
        (guardOps N C H p common guard pre) =
      independentPMF (privateSeedPMF N P p)
        (outsideGuardLaw N C P sample p r bin hbin
          (guardOps N C H p common guard pre)) := by
  exact actual_guarded_private_seed_old_bin_product N C P sample H p common r
    bin hbin guard pre post hprivate hsplit word href hword

/-- The exact unnormalized causal fibre weight. At zero-mass old states this
still reads 0=0; no conditioning on a null state or private-bit revelation. -/
theorem actual_guarded_seed_tag_atom (N : RootedBinary V E X)
    (C : Calendar N.graph) (P : Finset V) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) (guard : ℝ) (pre post : List ℝ)
    (hprivate : ∀ v ∈ P, guard < C.age v)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: post)
    (word : List (ProgramStep N × Tag))
    (href : CutRefines N (guardOps N C H p common guard pre) (physicalOps N word))
    (hword : wordBinContract N bin word
      (UnifiedLean.Source.SourceCalendarCompatibility.firstOriginalDate N C))
    (coin : PrivateHybrid N P → Bool) (q : TaggedEndpoint (Tag := Tag) N sample) :
    guardedSeedTaggedLaw N C P sample p r bin hbin
        (guardOps N C H p common guard pre) (coin, q) =
      privateSeedPMF N P p coin *
        outsideGuardLaw N C P sample p r bin hbin
          (guardOps N C H p common guard pre) q := by
  rw [actual_guarded_seed_tag_product N C P sample H p common r bin hbin
    guard pre post hprivate hsplit word href hword]
  exact independentPMF_apply _ _ coin q

/-- COMMON is deterministic on the FULL stored register. Every original copy
uses its actual current live owner, not a new per-copy coin. -/
theorem actual_common_pulse_exact_arm (N : RootedBinary V E X)
    {sample : Copy → X} (H : GProgram.G2.OriginalHybridParents N)
    (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node H.hybrid)
    (x : Copy) :
    copyLocation (state (pulseCode H s (fun _ => (state s).register H.hybrid))) x =
      .edge (H.parent ((state s).register H.hybrid)) := by
  let coin : AtNode (state s) H.hybrid → Bool :=
    fun _ => (state s).register H.hybrid
  have hx : (state s).ancestor x ∈ (state s).live ∧
      (state s).location ((state s).ancestor x) = .node H.hybrid :=
    ⟨s.property.forest.ancestor_live x,
      hinput _ (s.property.forest.ancestor_live x)⟩
  rw [show copyLocation (state (pulseCode H s coin)) x =
      copyLocation (pulse H (state s) coin) x from
    decode_encode_copyLocation N.root _
      (pulse_source_valid H sample _ s.property coin).forest x]
  exact pulse_routes_current_ancestor H (state s) coin ⟨(state s).ancestor x, hx⟩

theorem actual_common_pulse_support_exact_arm (N : RootedBinary V E X)
    {sample : Copy → X} (H : GProgram.G2.OriginalHybridParents N)
    (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node H.hybrid)
    {d : Code N sample} (hd : d ∈ (boundaryKernel N (.common H) s).support)
    (x : Copy) :
    copyLocation (state d) x = .edge (H.parent ((state s).register H.hybrid)) := by
  have he : d = pulseCode H s (fun _ => (state s).register H.hybrid) := by
    simpa only [boundaryKernel, PMF.mem_support_pure_iff] using hd
  subst d
  exact actual_common_pulse_exact_arm N H s hinput x

/-- The actual positive interval preserves the chosen ORIGINAL arm population.
All merger pairs therefore use that arm's actual rho/2 clock convention. -/
theorem actual_common_arm_epoch_support (N : RootedBinary V E X)
    {sample : Copy → X} (r : PositivePairRates E)
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node H.hybrid)
    {p d : Code N sample} (hp : p ∈ (boundaryKernel N (.common H) s).support)
    (t : ℝ≥0) (hd : d ∈ (sourceTimeKernel N r t p).support) (x : Copy) :
    copyLocation (state d) x = .edge (H.parent ((state s).register H.hybrid)) := by
  rw [actual_time_copy_population N r t p hd x]
  exact actual_common_pulse_support_exact_arm N H s hinput hp x

#print axioms actual_guarded_seed_tag_product
#print axioms actual_guarded_seed_tag_atom
#print axioms actual_common_pulse_exact_arm
#print axioms actual_common_pulse_support_exact_arm
#print axioms actual_common_arm_epoch_support

end UnifiedLean.G6.GuardedCommonSeedFibre
