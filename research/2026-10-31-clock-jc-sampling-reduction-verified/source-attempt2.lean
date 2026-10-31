import ResearchCommons.MSCI.JC69SamplingPrefix
import ResearchCommons.MSCI.JC69SupportedStateBound

/-! WORKING UNCOMPILED. Actual post-sampling representative and original
backward-recursion cut. Dot (OpenAI), 31 October 2026.
No raw endpoint Code identity, new normalization or finite-window claim. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69SamplingReduction
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable
  GProgram.G2.LiteralMarkedClockTrace.codeOptionMeasurable
open MeasureTheory ProbabilityTheory Set Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceInitializedCalendar UnifiedLean.Source.SourceCalendarCompiler
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceCalendarPhysicalSupport
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.SourceBoundaryKernels
open GProgram.G2.ActualCalendarTrace GProgram.G2.CalendarDecoration
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69CurrentPartition
open ResearchCommons.MSCI.JC69EndpointWeight ResearchCommons.MSCI.JC69FixedBankBoundary
open ResearchCommons.MSCI.JC69WeightedCalendar ResearchCommons.MSCI.JC69GuardedCalendarQuotient
open ResearchCommons.MSCI.JC69ActivatedPrefix ResearchCommons.MSCI.JC69SupportedStateBound
open ResearchCommons.MSCI.JC69SamplingPrefix ResearchCommons.MSCI.JC69ObservedFourier
open scoped Classical BigOperators ENNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

lemma directed_equal_age (N : RootedBinary V E X) (C : Calendar N.graph)
    {a b : V} (hp : N.graph.DReach a b) (he : C.age a = C.age b) : a = b := by
  induction hp with
  | refl => rfl
  | tail path step ih =>
      obtain ⟨e,hs,ht⟩ := step
      have hl := C.edge_older e
      rw [hs,ht] at hl
      have hab := C.age_le_of_directed path
      exact False.elim ((ne_of_lt (hl.trans_le hab)) he.symm)

lemma leaf_before_root (N : RootedBinary V E X) (C : Calendar N.graph) (x : X) :
    C.age (N.leaf x) < C.age N.root := by
  have hp := N.rooted (N.leaf x)
  apply lt_of_le_of_ne (C.age_le_of_directed hp)
  intro he
  exact N.leaf_ne_root x (directed_equal_age N C hp he.symm).symm

def sampleEdge (N : RootedBinary V E X) (x : X) : E :=
  (defaultSelector N).edge ⟨N.leaf x,N.leaf_ne_root x⟩

lemma sampleEdge_target (N : RootedBinary V E X) (x : X) :
    N.graph.target (sampleEdge N x) = N.leaf x := (defaultSelector N).target _

lemma unique_leaf_edge (N : RootedBinary V E X) (x : X) (e : E)
    (he : N.graph.target e = N.leaf x) : e = sampleEdge N x := by
  have hc := (N.leaf_degrees x).1
  unfold EdgeGraph.inDegree at hc
  obtain ⟨f,hf⟩ := Finset.card_eq_one.mp hc
  have hm : e ∈ Finset.univ.filter (fun e => N.graph.target e = N.leaf x) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩
  have hn : sampleEdge N x ∈ Finset.univ.filter (fun e => N.graph.target e = N.leaf x) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _,sampleEdge_target N x⟩
  rw [hf,Finset.mem_singleton] at hm hn
  exact hm.trans hn.symm

/-- Count/rate-independent admitted representative; no reachability asserted. -/
def activatedState (N : RootedBinary V E X) (sample : Copy → X) (register : V → Bool) :
    State V E Copy := { initial N sample register with location := fun x => .edge (sampleEdge N (sample x)) }

lemma activated_valid (N : RootedBinary V E X) (sample : Copy → X) (register : V → Bool) :
    SourceValid N sample (activatedState N sample register) := by
  have hi := initial_valid N sample register
  refine ⟨⟨hi.ancestor_live,hi.representative,hi.leaf_fiber,hi.wellLabelled⟩,?_⟩
  intro x
  change N.graph.DReach (N.graph.target (sampleEdge N (sample x))) (N.leaf (sample x))
  rw [sampleEdge_target]
  exact Relation.ReflTransGen.refl

def activatedCode (N : RootedBinary V E X) (sample : Copy → X) (register : V → Bool) : Code N sample :=
  admittedCode N sample (activatedState N sample register) (activated_valid N sample register)

lemma activated_observation (N : RootedBinary V E X) (sample : Copy → X) (register : V → Bool) :
    observeCode N (activatedCode N sample register) =
      (currentBlocks (initial N sample register),fun x => .edge (sampleEdge N (sample x))) := by
  rw [activatedCode,admitted_observation]
  rfl

lemma activated_register (N : RootedBinary V E X) (sample : Copy → X) (register : V → Bool) :
    (state (activatedCode N sample register)).register = register := rfl

lemma singleton_blocks_initial (N : RootedBinary V E X) (sample : Copy → X) (register : V → Bool)
    (s : State V E Copy) (hs : Valid s) (hb : SingletonBlocks s) :
    currentBlocks s = currentBlocks (initial N sample register) := by
  ext B
  constructor
  · intro hB
    obtain ⟨x,rfl⟩ := hb B hB
    exact Finset.mem_image.mpr ⟨x,Finset.mem_univ _,rfl⟩
  · intro hB
    obtain ⟨x,_,hx⟩ := Finset.mem_image.mp hB
    have hBl : (s.genealogy (s.ancestor x)).leaves ∈ currentBlocks s :=
      Finset.mem_image.mpr ⟨s.ancestor x,hs.ancestor_live x,rfl⟩
    obtain ⟨y,hy⟩ := hb _ hBl
    have hxy : x = y := Finset.mem_singleton.mp (by
      rw [← hy]; exact (hs.leaf_fiber _ (hs.ancestor_live x) x).mpr rfl)
    have hBx : B = ({x} : Finset Copy) := hx.symm
    simpa only [hy,← hxy,← hBx] using hBl

/-- Actual physical support at c determines the original deterministic
singleton population observation, using strict age/ancestry and leaf degree. -/
theorem actual_sampling_observation (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (c : ℝ) (hc : ∀ x : Copy, C.age (N.leaf (sample x)) = c) (k : ℕ)
    (hcut : prefixDate N C k = c) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (initializedPrefix N C H gamma common k)
      (initialCode N sample register)).support) :
    observeCode N d = observeCode N (activatedCode N sample register) := by
  rw [activated_observation]
  apply Prod.ext
  · exact singleton_blocks_initial N sample register (state d) d.property.forest
      (actual_sampling_prefix_support N C sample register H gamma common r c hc k hcut.le hd).1
  · funext x
    have hbefore : prefixDate N C k < C.age N.root := by
      rw [hcut,← hc x]; exact leaf_before_root N C (sample x)
    obtain ⟨e,he,ha⟩ := actual_initialized_prefix_active N C sample register H gamma common r c hc k
      hcut.ge hbefore hd x
    have hp := d.property.original_descendant x
    change DescendsTo N (copyLocation (state d) x) (sample x) at hp
    rw [he] at hp
    change N.graph.DReach (N.graph.target e) (N.leaf (sample x)) at hp
    have hage : C.age (N.graph.target e) = C.age (N.leaf (sample x)) := by
      apply le_antisymm
      · rw [hc x,← hcut]; exact ha.1
      · exact C.age_le_of_directed hp
    have ht := directed_equal_age N C hp hage
    have hed := unique_leaf_edge N (sample x) e ht
    simpa only [hed] using he

lemma program_support_register (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (s : Code N sample)
    {d : Code N sample} (hd : d ∈ (sourceProgram N r ops s).support) :
    (state d).register = (state s).register := by
  induction ops generalizing s with
  | nil =>
      have he : d = s := by simpa only [sourceProgram,PMF.mem_support_pure_iff] using hd
      rw [he]
  | cons op ops ih =>
      obtain ⟨m,hm,hmd⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      exact (ih m hmd).trans (program_step_support_register N r op s m hm)

lemma tail_take_drop (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (dates : List ℝ) (a : ℝ) (k : ℕ) :
    calendarTail N C H gamma common a dates =
      calendarTail N C H gamma common a (dates.take k) ++
        calendarTail N C H gamma common (finalDate a (dates.take k)) (dates.drop k) := by
  induction dates generalizing a k with
  | nil => simp [calendarTail,finalDate]
  | cons b bs ih =>
      cases k with
      | zero => simp [calendarTail,finalDate]
      | succ k =>
          simp only [List.take_succ_cons,List.drop_succ_cons,calendarTail,finalDate,List.cons_append]
          rw [ih b k]
          simp only [List.append_assoc]

def samplingSuffix (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (k : ℕ) : List (ProgramStep N) :=
  match sortedOriginalDates N C with
  | [] => []
  | a::dates => calendarTail N C H gamma common (finalDate a (dates.take k)) (dates.drop k)

/-- The actual full program splits after the COMPLETE date block, without
replaying that block or introducing a new time schedule. -/
theorem actual_calendar_sampling_split (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (k : ℕ) :
    compiledCalendarProgram N C H gamma common =
      initializedPrefix N C H gamma common k ++ samplingSuffix N C H gamma common k := by
  cases he : sortedOriginalDates N C with
  | nil => simp [compiledCalendarProgram,initializedPrefix,samplingSuffix,he]
  | cons a dates =>
      simp only [compiledCalendarProgram,initializedPrefix,samplingSuffix,he]
      rw [tail_take_drop N C H gamma common dates a k]
      exact (List.append_assoc _ _ _).symm

lemma calendar_value_append (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (terminal : Code N sample → ℝ≥0∞) (xs ys : List (ProgramStep N)) (s : Code N sample) :
    calendarValue N r L q terminal (xs++ys) s =
      calendarValue N r L q (calendarValue N r L q terminal ys) xs s := by
  induction xs generalizing s with
  | nil => rfl
  | cons op xs ih =>
      change (∑ d, segmentFibreWeight N r L q op s d * calendarValue N r L q terminal (xs++ys) d) = _
      simp only [calendarValue,ih]

lemma actual_sampling_observation_bank_ae (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (r : PositivePairRates E)
    (c : ℝ) (hc : ∀ x : Copy, C.age (N.leaf (sample x)) = c) (k : ℕ)
    (hcut : prefixDate N C k = c) :
    let ops := initializedPrefix N C H gamma common k
    let s := initialCode N sample register
    ∀ᵐ past ∂actualCalendarTraceLaw N r ops s,
      observeCode N (calendarEnd N ops s past) = observeCode N (activatedCode N sample register) ∧
        (state (calendarEnd N ops s past)).register = (state (activatedCode N sample register)).register := by
  let ops := initializedPrefix N C H gamma common k
  let s := initialCode N sample register
  let p := sourceProgram N r ops s
  have hs : ∀ᵐ d ∂p.toMeasure, d ∈ p.support := by
    rw [← p.restrict_toMeasure_support]
    exact ae_restrict_mem p.support_countable.measurableSet
  have ha : ∀ᵐ d ∂p.toMeasure,
      observeCode N d = observeCode N (activatedCode N sample register) ∧
        (state d).register = (state (activatedCode N sample register)).register := by
    filter_upwards [hs] with d hd
    refine ⟨actual_sampling_observation N C sample register H gamma common r c hc k hcut hd,?_⟩
    exact program_support_register N r ops s hd
  change ∀ᵐ d ∂(sourceProgram N r ops s).toMeasure, _ at ha
  rw [← actual_calendar_endpoint_law N r ops s] at ha
  exact ae_of_ae_map (calendar_end_measurable N ops s).aemeasurable ha

/-- Actual initialization cancellation is now spliced into the ORIGINAL
full backward recursion. SAME bank, labels, balanced site family and source. -/
theorem actual_sampling_backward_reduction [Nonempty Copy] (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (hbal : ∀ j, ∑ x, q j x = 0) (c : ℝ)
    (hc : ∀ x : Copy, C.age (N.leaf (sample x)) = c) (k : ℕ)
    (hcut : prefixDate N C k = c) :
    initialPotentialWeight N C sample register L q *
      calendarValue N r L q (guardedRoot N r L q) (compiledCalendarProgram N C H gamma common)
        (initialCode N sample register) =
      calendarValue N r L q (guardedRoot N r L q) (samplingSuffix N C H gamma common k)
        (activatedCode N sample register) := by
  let pre := initializedPrefix N C H gamma common k
  let post := samplingSuffix N C H gamma common k
  let s := initialCode N sample register
  let d := activatedCode N sample register
  let I := initialPotentialWeight N C sample register L q
  let F : Code N sample → ℝ≥0∞ := calendarValue N r L q (guardedRoot N r L q) post
  letI := actual_calendar_trace_probability N r pre s
  rw [actual_calendar_sampling_split N C H gamma common k,calendar_value_append]
  change I * calendarValue N r L q F pre s = F d
  rw [← actual_calendar_weighted_recursion N r L q F pre s]
  calc
    I * (∫⁻ past, calendarWeight N L q pre s past * F (calendarEnd N pre s past)
      ∂actualCalendarTraceLaw N r pre s) =
      ∫⁻ past, I * (calendarWeight N L q pre s past * F (calendarEnd N pre s past))
        ∂actualCalendarTraceLaw N r pre s :=
      (lintegral_const_mul I (weighted_readout_measurable N L q F pre s)).symm
    _ = ∫⁻ _past, F d ∂actualCalendarTraceLaw N r pre s := by
      apply lintegral_congr_ae
      filter_upwards [actual_initial_factor_cancellation N C sample register H gamma common r L q c hc k hcut,
        actual_sampling_observation_bank_ae N C sample register H gamma common r c hc k hcut] with past hi hd
      have hf := actual_guarded_calendar_quotient N r L q hbal post (calendarEnd N pre s past) d hd.1 hd.2
      rw [← mul_assoc,hi,one_mul]
      exact hf
    _ = F d := by simp

/-- Equality for the original full-labelled observed Fourier coefficient,
not a newly invented reduced observation or a supplied likelihood law. -/
theorem actual_observed_sampling_reduction [Nonempty Copy] (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (hbal : ∀ j, ∑ x, q j x = 0) (c : ℝ)
    (hc : ∀ x : Copy, C.age (N.leaf (sample x)) = c) :
    ∃ k : ℕ, prefixDate N C k = c ∧
      observedFourier L N C sample register H gamma common r q =
        (calendarValue N r L q (guardedRoot N r L q) (samplingSuffix N C H gamma common k)
          (activatedCode N sample register)).toReal := by
  obtain ⟨k,hk⟩ := actual_sampling_cut_exists N C sample c hc
  refine ⟨k,hk,?_⟩
  rw [actual_observed_guarded_calendar N C sample register H gamma common r L q hbal,
    actual_sampling_backward_reduction N C sample register H gamma common r L q hbal c hc k hk]

#print axioms actual_sampling_observation
#print axioms actual_calendar_sampling_split
#print axioms actual_sampling_backward_reduction
#print axioms actual_observed_sampling_reduction
end ResearchCommons.MSCI.JC69SamplingReduction
