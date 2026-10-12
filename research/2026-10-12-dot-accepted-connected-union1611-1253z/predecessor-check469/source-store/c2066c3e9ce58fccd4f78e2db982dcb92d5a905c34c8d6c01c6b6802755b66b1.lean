import ActualObservationCutRefinement
import PrivateSeedHistoryFactorization
import UnifiedLean.G6.PrivateRegisterCalendarPrefix

/-!
Contributor: CLOUD-CALENDAR-REVIEW-SOL, 8 October 2026.
UNCHECKED additive ORIGINAL leaf/register/clock-past consumer, outside165.
The original leaf ages and once-drawn hybrid register initialize the Code
and matrix. The actual clock calendar derives their entering joint law.
Legal interval refinement and fixed-bin contracts remain explicit grammar
properties. No desired Gamma/old-law, independent entering law, rational
bank, chronology success, pruning or cross-graph substitution is assumed.
-/
namespace CloudG6.NaturalCalendarPastAdmission
set_option backward.isDefEq.respectTransparency false

universe u v w x y

open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.NativeIndependentPairMixture
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceProgramTransport UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarTiming UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceNaturalInitialization
open UnifiedLean.Source.SourceCalendarCompatibility
open GProgram.G2.LiteralMarkedClockTrace GProgram.G2.ActualCalendarTrace
open GProgram.G2.CalendarDecoration GProgram.G2.SourceGraftDecoration
open GProgram.G2.ChronologicalPathReadout GProgram.G2.SourceFiniteHistory
open UnifiedLean.G6.BinHistory
open UnifiedLean.G6.PrivateRegisterErasure UnifiedLean.G6.PrivateRegisterProgram
open UnifiedLean.G6.PrivateRegisterHistory UnifiedLean.G6.PrivateRegisterCalendarPrefix
open CloudG3.CompleteCalendarBinReadout CloudG3.CompleteCalendarJointLaw
open CloudG3.ActualCalendarCutContext CloudG3.ActualCalendarEndpointHistory
open CloudG3.ActualObservationCutRefinement
open CloudG3.ActualCutJointLaw
open CloudG6.PrivateSeedFactorization CloudG6.PrivateSeedHistoryFactorization
open scoped Classical NNReal ENNReal BigOperators

variable {V : Type u} {E : Type v} {Copy : Type w} {X : Type x} {Tag : Type y}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]
variable [Fintype Tag] [MeasurableSpace Tag] [MeasurableSingletonClass Tag]
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

/-- Each initial singleton has its actual original sampled-leaf age. Off-block
entries are inert until the actual ancestral-pair update first writes them. -/
noncomputable def leafAgeMatrix (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) : Copy → Copy → ℝ :=
  fun a _ => C.age (N.leaf (sample a))

/-- Derived decoration of the admitted ORIGINAL initial Code. No initial
matrix correctness or old subtree law is supplied as a premise. -/
theorem actual_leaf_initialCode_decorates (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool) :
    ForestDecorates (fun a => C.age (N.leaf (sample a)))
      (leafAgeMatrix N C sample) (state (initialCode N sample register)) := by
  exact snapshot_preserves_decorates N.root (initial N sample register)
    (initial_source_valid N sample register).forest
    (fun a => C.age (N.leaf (sample a))) (leafAgeMatrix N C sample)
    (initial_forest_decorates N sample register (fun a => C.age (N.leaf (sample a))))

/-- Every actual recorded clock prefix carries its SAME old real decoration
of the actual live forest. All Copy counts and every earlier graft remain. -/
theorem actual_leaf_calendar_matrix_decorates (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (r : PositivePairRates E) (ops : List (ProgramStep N)) :
    ∀ᵐ past ∂actualCalendarTraceLaw N r ops (initialCode N sample register),
      ForestDecorates (fun a => C.age (N.leaf (sample a)))
        (calendarMatrix N ops (initialCode N sample register) (firstOriginalDate N C)
          (leafAgeMatrix N C sample) past)
        (state (calendarEnd N ops (initialCode N sample register) past)) := by
  exact actual_calendar_matrix_decorates N r (fun a => C.age (N.leaf (sample a)))
    ops (initialCode N sample register) (firstOriginalDate N C)
    (leafAgeMatrix N C sample) (actual_leaf_initialCode_decorates N C sample register)

/-- Natural joint entering Code and old tags, constructed from the original
register PMF and ACTUAL finite clock calendar. The register is drawn once. -/
noncomputable def naturalPastJoint (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (p : HybridProbabilities N) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) (ops : List (ProgramStep N)) :
    PMF (TaggedEndpoint (Tag := Tag) N sample) :=
  (originalRegisterPMF N p).bind (fun register =>
    calendarJointPMF N r bin hbin ops (initialCode N sample register)
      (firstOriginalDate N C) (leafAgeMatrix N C sample))

/-- The latent private seed is retained jointly with the SAME physical old
past. This internal label does not enlarge the observed biological menu. -/
noncomputable def naturalSeedPastJoint (N : RootedBinary V E X) (C : Calendar N.graph)
    (P : Finset V) (sample : Copy → X) (p : HybridProbabilities N)
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) :
    PMF ((PrivateHybrid N P → Bool) × TaggedEndpoint (Tag := Tag) N sample) :=
  (naturalInitialJoint N P sample p).bind (fun a =>
    (calendarJointPMF N r bin hbin ops a.2 (firstOriginalDate N C)
      (leafAgeMatrix N C sample)).map (Prod.mk a.1))

/-- Forgetting the latent seed returns EXACTLY the same naturally initialized
clock-past joint law. The seed label causes no independent resampling. -/
theorem actual_natural_seed_past_marginal (N : RootedBinary V E X)
    (C : Calendar N.graph) (P : Finset V) (sample : Copy → X)
    (p : HybridProbabilities N) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) (ops : List (ProgramStep N)) :
    (naturalSeedPastJoint N C P sample p r bin hbin ops).map Prod.snd =
      naturalPastJoint N C sample p r bin hbin ops := by
  have hrow (a : (PrivateHybrid N P → Bool) × Code N sample) :
      ((calendarJointPMF N r bin hbin ops a.2 (firstOriginalDate N C)
        (leafAgeMatrix N C sample)).map (Prod.mk a.1)).map Prod.snd =
      calendarJointPMF N r bin hbin ops a.2 (firstOriginalDate N C)
        (leafAgeMatrix N C sample) := by
    rw [PMF.map_comp]
    exact PMF.map_id _
  rw [naturalSeedPastJoint, PMF.map_bind]
  simp_rw [hrow]
  unfold naturalInitialJoint naturalPastJoint originalRegisterPMF
  simp only [PMF.bind_map, Function.comp_def]

/-- The natural entering joint PMF is the original register mixture of the
SAME recorded endpoint and binned real matrix. No marginal tags are redrawn. -/
theorem actual_natural_past_joint_toMeasure (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (p : HybridProbabilities N)
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) :
    (naturalPastJoint N C sample p r bin hbin ops).toMeasure =
      ∑ register : V → Bool, originalRegisterPMF N p register •
        (actualCalendarTraceLaw N r ops (initialCode N sample register)).map
          (fun past => (calendarEnd N ops (initialCode N sample register) past,
            fun a b => bin (calendarMatrix N ops (initialCode N sample register)
              (firstOriginalDate N C) (leafAgeMatrix N C sample) past a b))) := by
  have hrow (register : V → Bool) :
      (calendarJointPMF N r bin hbin ops (initialCode N sample register)
        (firstOriginalDate N C) (leafAgeMatrix N C sample)).toMeasure =
      (actualCalendarTraceLaw N r ops (initialCode N sample register)).map
        (fun past => (calendarEnd N ops (initialCode N sample register) past,
          fun a b => bin (calendarMatrix N ops (initialCode N sample register)
            (firstOriginalDate N C) (leafAgeMatrix N C sample) past a b))) := by
    rw [calendar_joint_pmf_toMeasure, calendarJointLaw]
    apply congrArg (fun f => (actualCalendarTraceLaw N r ops
      (initialCode N sample register)).map f)
    funext past
    exact Prod.ext rfl (map_calendar_matrix N bin ops (initialCode N sample register)
      (firstOriginalDate N C) (leafAgeMatrix N C sample) past).symm
  unfold naturalPastJoint
  apply Measure.ext
  intro S hS
  rw [PMF.toMeasure_bind_apply _ _ _ hS, tsum_fintype, Measure.finsetSum_apply]
  simp only [Measure.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro register _
  rw [hrow]

/-- Source admission of the complete old-bin matrix: actual natural Gamma
is a reader of the naturally initialized joint original endpoint history.
Only legal subdivision and fixed-bin grammar contracts are premises. -/
theorem actual_natural_past_endpoint_history (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (p : HybridProbabilities N)
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (word : List (ProgramStep N × Tag))
    (href : CutRefines N ops (physicalOps N word))
    (hword : wordBinContract N bin word (firstOriginalDate N C)) :
    naturalPastJoint N C sample p r bin hbin ops =
      (initializedEndpointLaw N r (physicalOps N word)
        (naturalInitialCodeLaw N sample p)).map (fun a =>
          endpointHistoryReadout N word a.1
            (fun x y => bin (leafAgeMatrix N C sample x y)) a.2) := by
  have hgamma (s : Code N sample) :=
    original_gamma_refined_endpoint_history N r bin hbin ops word href s
      (firstOriginalDate N C) (leafAgeMatrix N C sample) hword
  unfold naturalPastJoint
  simp_rw [hgamma]
  unfold initializedEndpointLaw naturalInitialCodeLaw
  rw [PMF.map_bind, PMF.bind_map]
  simp only [PMF.map_comp, Function.comp_def]

/-- Exact conditional continuation from this derived joint past. The entering
Code and all old bins are kept correlated under the original source bank. -/
theorem actual_natural_past_append (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (p : HybridProbabilities N)
    (r : PositivePairRates E) (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops more : List (ProgramStep N)) :
    naturalPastJoint N C sample p r bin hbin (ops ++ more) =
      (naturalPastJoint N C sample p r bin hbin ops).bind (fun q =>
        calendarJoint N r bin hbin more q.1
          (firstOriginalDate N C + (programDuration N ops : ℝ)) q.2) := by
  have hrow (steps : List (ProgramStep N)) (s : Code N sample) :
      calendarJointPMF N r bin hbin steps s (firstOriginalDate N C)
        (leafAgeMatrix N C sample) =
      calendarJoint N r bin hbin steps s (firstOriginalDate N C)
        (fun a b => bin (leafAgeMatrix N C sample a b)) := by
    apply PMF.toMeasure_injective
    rw [calendar_joint_pmf_toMeasure, calendar_joint_toMeasure]
    rfl
  unfold naturalPastJoint
  simp_rw [hrow, calendar_joint_append]
  rw [PMF.bind_bind]

/-- Legal source refinement inserts only intervals and preserves boundaries;
the actual operation no-read property is transported, not assumed anew. -/
theorem cutRefines_noPrivateWordRead (N : RootedBinary V E X) (P : Finset V)
    {ops refined : List (ProgramStep N)} (href : CutRefines N ops refined) :
    NoPrivateWordRead N P ops → NoPrivateWordRead N P refined := by
  induction href with
  | refl ops => exact fun h => h
  | split pre post t v =>
      intro hops op hop
      rcases List.mem_append.mp hop with hp | hp
      · exact hops op (List.mem_append.mpr (Or.inl hp))
      · rcases List.mem_cons.mp hp with he | hp
        · subst op
          trivial
        · rcases List.mem_cons.mp hp with he | hp
          · subst op
            trivial
          · exact hops op (List.mem_append.mpr
              (Or.inr (List.mem_cons_of_mem (.interval (t + v)) hp)))
  | trans h₁ h₂ ih₁ ih₂ => exact fun h => ih₂ (ih₁ h)

/-- Register-only erasure never changes either old/destination ancestry used
by tagUpdate; interval and boundary readouts retain the same old tags. -/
theorem endpointStepTags_erasure (N : RootedBinary V E X) {sample : Copy → X}
    (P : Finset V) (op : ProgramStep N) (tag : Tag) (s d : Code N sample)
    (B : Copy → Copy → Tag) :
    endpointStepTags N op tag (erasePrivateCode N P s) (erasePrivateCode N P d) B =
      endpointStepTags N op tag s d B := by
  cases op <;> rfl

/-- Erase ONLY the private register. The full old-bin matrix, live genealogy,
ancestry, population and original ownership remain in the joint reader. -/
theorem endpointHistoryReadout_erasure (N : RootedBinary V E X) {sample : Copy → X}
    (P : Finset V) (word : List (ProgramStep N × Tag)) (s : Code N sample)
    (B : Copy → Copy → Tag) (h : Fin (physicalOps N word).length → Code N sample) :
    endpointHistoryReadout N word (erasePrivateCode N P s) B
        (historyProjection (erasePrivateCode N P) h) =
      (erasePrivateCode N P (endpointHistoryReadout N word s B h).1,
        (endpointHistoryReadout N word s B h).2) := by
  induction word generalizing s B with
  | nil => rfl
  | cons q word ih =>
      change Fin ((physicalOps N word).length + 1) → Code N sample at h
      change endpointHistoryReadout N word (erasePrivateCode N P (h 0))
        (endpointStepTags N q.1 q.2 (erasePrivateCode N P s)
          (erasePrivateCode N P (h 0)) B)
        (historyProjection (erasePrivateCode N P) (Fin.tail h)) = _
      rw [endpointStepTags_erasure]
      exact ih (h 0) _ (Fin.tail h)

private theorem independentPMF_map_second {A B D : Type*}
    (p : PMF A) (q : PMF B) (f : B → D) :
    (independentPMF p q).map (fun a => (a.1, f a.2)) =
      independentPMF p (q.map f) := by
  simp only [independentPMF, PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- PRIVATE latent seed times the ACTUAL complete entering old-bin matrix and
erased original Code. The no-read restriction concerns actual operations;
the initializer product and Gamma/history law are both derived beforehand. -/
theorem actual_private_seed_old_bin_product (N : RootedBinary V E X)
    (C : Calendar N.graph) (P : Finset V) (sample : Copy → X)
    (p : HybridProbabilities N) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin)
    (ops : List (ProgramStep N)) (word : List (ProgramStep N × Tag))
    (href : CutRefines N ops (physicalOps N word))
    (hword : wordBinContract N bin word (firstOriginalDate N C))
    (hops : NoPrivateWordRead N P ops) :
    (naturalSeedPastJoint N C P sample p r bin hbin ops).map
        (fun a => (a.1, (erasePrivateCode N P a.2.1, a.2.2))) =
      independentPMF (privateSeedPMF N P p)
        ((outsideInitialCodeLaw N P sample p).bind (fun s =>
          calendarJointPMF N r bin hbin ops s (firstOriginalDate N C)
            (leafAgeMatrix N C sample))) := by
  let read := fun a : Code N sample ×
      (Fin (physicalOps N word).length → Code N sample) =>
    endpointHistoryReadout N word a.1
      (fun x y => bin (leafAgeMatrix N C sample x y)) a.2
  have hgamma (s : Code N sample) :=
    original_gamma_refined_endpoint_history N r bin hbin ops word href s
      (firstOriginalDate N C) (leafAgeMatrix N C sample) hword
  have hn : naturalSeedPastJoint N C P sample p r bin hbin ops =
      (initializedSourceHistory N r (physicalOps N word)
        (naturalInitialJoint N P sample p)).map (fun a => (a.1, read a.2)) := by
    unfold naturalSeedPastJoint initializedSourceHistory
    rw [PMF.map_bind]
    simpa only [hgamma, PMF.map_comp, Function.comp_def, read]
  have hout : (initializedEndpointLaw N r (physicalOps N word)
        (outsideInitialCodeLaw N P sample p)).map read =
      (outsideInitialCodeLaw N P sample p).bind (fun s =>
        calendarJointPMF N r bin hbin ops s (firstOriginalDate N C)
          (leafAgeMatrix N C sample)) := by
    unfold initializedEndpointLaw
    rw [PMF.map_bind]
    simpa only [hgamma, PMF.map_comp, Function.comp_def, read]
  calc
    _ = (initializedSourceHistory N r (physicalOps N word)
        (naturalInitialJoint N P sample p)).map
      ((fun a => (a.1, read a.2)) ∘ (fun a =>
        (a.1, (erasePrivateCode N P a.2.1,
          historyProjection (erasePrivateCode N P) a.2.2)))) := by
      rw [hn, PMF.map_comp]
      congr 1
      funext a
      exact Prod.ext rfl (endpointHistoryReadout_erasure N P word a.2.1
        (fun x y => bin (leafAgeMatrix N C sample x y)) a.2.2).symm
    _ = (independentPMF (privateSeedPMF N P p)
        (initializedEndpointLaw N r (physicalOps N word)
          (outsideInitialCodeLaw N P sample p))).map (fun a => (a.1, read a.2)) := by
      rw [← PMF.map_comp, actual_private_seed_erased_history_product N P sample p r
        (physicalOps N word) (cutRefines_noPrivateWordRead N P href hops)]
    _ = _ := by rw [independentPMF_map_second, hout]

/-- Physical lower-prefix specialization. Its word is the native initialized
sorted ORIGINAL agenda through the complete guard batch, and its bank uses
SAME originalGamma p at every original hybrid occurrence. No desired no-read
word/kernel law is a premise. Strict private ages exclude all guard ties. -/
theorem actual_guarded_private_seed_old_bin_product (N : RootedBinary V E X)
    (C : Calendar N.graph) (P : Finset V) (sample : Copy → X)
    (H : OriginalParentRegistry N) (p : HybridProbabilities N)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    (bin : ℝ → Tag) (hbin : Measurable bin) (guard : ℝ) (pre post : List ℝ)
    (hprivate : ∀ v ∈ P, guard < C.age v)
    (hsplit : sortedOriginalDates N C = pre ++ guard :: post)
    (word : List (ProgramStep N × Tag))
    (href : CutRefines N
      (match pre ++ [guard] with
       | [] => []
       | a :: dates => boundaryOperations N C H (originalGamma p) common a ++
           calendarTail N C H (originalGamma p) common a dates)
      (physicalOps N word))
    (hword : wordBinContract N bin word (firstOriginalDate N C)) :
    (naturalSeedPastJoint N C P sample p r bin hbin
      (match pre ++ [guard] with
       | [] => []
       | a :: dates => boundaryOperations N C H (originalGamma p) common a ++
           calendarTail N C H (originalGamma p) common a dates)).map
        (fun a => (a.1, (erasePrivateCode N P a.2.1, a.2.2))) =
      independentPMF (privateSeedPMF N P p)
        ((outsideInitialCodeLaw N P sample p).bind (fun s =>
          calendarJointPMF N r bin hbin
            (match pre ++ [guard] with
             | [] => []
             | a :: dates => boundaryOperations N C H (originalGamma p) common a ++
                 calendarTail N C H (originalGamma p) common a dates)
            s (firstOriginalDate N C) (leafAgeMatrix N C sample))) := by
  exact actual_private_seed_old_bin_product N C P sample p r bin hbin _ word
    href hword (actual_calendar_initial_prefix_noPrivateWordRead N C H
      (originalGamma p) common P guard pre post hprivate hsplit)

#print axioms actual_leaf_initialCode_decorates
#print axioms actual_leaf_calendar_matrix_decorates
#print axioms actual_natural_seed_past_marginal
#print axioms actual_natural_past_joint_toMeasure
#print axioms actual_natural_past_endpoint_history
#print axioms actual_natural_past_append
#print axioms cutRefines_noPrivateWordRead
#print axioms endpointStepTags_erasure
#print axioms endpointHistoryReadout_erasure
#print axioms actual_private_seed_old_bin_product
#print axioms actual_guarded_private_seed_old_bin_product

end CloudG6.NaturalCalendarPastAdmission
