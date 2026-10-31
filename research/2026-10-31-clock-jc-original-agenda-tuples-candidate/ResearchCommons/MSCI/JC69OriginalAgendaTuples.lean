import ResearchCommons.MSCI.JC69GlobalStageTuples
import ResearchCommons.MSCI.JC69SamplingReduction

/-! WORKING UNCOMPILED. Original agenda/sampling instantiation of the actual
supported tuple expansion. Dot (OpenAI), 31 October 2026. No common denominator,
finite-window theorem or broader finite-schedule admission is asserted. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69OriginalAgendaTuples
open MeasureTheory Set Nanuq.Source GProgram.SourceForest GProgram.G5
open UnifiedLean.Source.FiniteSourceSnapshot UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.NativePairClockLaw UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarTiming
open UnifiedLean.Source.SourceCalendarCompatibility UnifiedLean.Source.SourceCalendarPhysicalSupport
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69CurrentPartition
open ResearchCommons.MSCI.JC69EndpointWeight ResearchCommons.MSCI.JC69FixedBankBoundary
open ResearchCommons.MSCI.JC69WeightedCalendar ResearchCommons.MSCI.JC69GuardedCalendarQuotient
open ResearchCommons.MSCI.JC69ActivatedPrefix ResearchCommons.MSCI.JC69SupportedStateBound
open ResearchCommons.MSCI.JC69SamplingPrefix ResearchCommons.MSCI.JC69SamplingReduction
open ResearchCommons.MSCI.JC69ObservedFourier ResearchCommons.MSCI.JC69ActiveStage
open ResearchCommons.MSCI.JC69GlobalStageTuples
open scoped Classical BigOperators ENNReal
universe uV uE uCopy uX
variable {V : Type uV} {E : Type uE} {Copy : Type uCopy} {X : Type uX}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

def originalPostDates (N : RootedBinary V E X) (C : Calendar N.graph) (k : ℕ) : List ℝ :=
  (sortedOriginalDates N C).tail.drop k

lemma original_dates_nonempty (N : RootedBinary V E X) (C : Calendar N.graph) :
    sortedOriginalDates N C ≠ [] := by
  intro h
  have hm := original_date_scheduled N C N.root
  simpa only [h,List.not_mem_nil] using hm

lemma original_date_upper (N : RootedBinary V E X) (C : Calendar N.graph)
    {b : ℝ} (hb : b ∈ sortedOriginalDates N C) : b ≤ C.age N.root := by
  rw [sortedOriginalDates,Finset.mem_sort] at hb
  obtain ⟨v,_,hv⟩ := Finset.mem_image.mp hb
  rw [← hv]
  exact original_root_latest N C v

lemma original_initial_suffix (N : RootedBinary V E X) (C : Calendar N.graph)
    {a : ℝ} {dates : List ℝ} (he : sortedOriginalDates N C = a::dates) :
    SourceSuffix N C a dates := by
  have hp := original_dates_strict N C
  rw [he,List.pairwise_cons] at hp
  refine ⟨original_date_upper N C (by simp [he]),hp.2,?_,?_⟩
  · intro b hb
    exact ⟨hp.1 b hb,original_date_upper N C (by simp [he,hb])⟩
  · intro v hv
    have hm := original_date_scheduled N C v
    rw [he,List.mem_cons] at hm
    exact hm.resolve_left (ne_of_gt hv)

lemma source_suffix_take_drop (N : RootedBinary V E X) (C : Calendar N.graph)
    (a : ℝ) (dates : List ℝ) (h : SourceSuffix N C a dates) (k : ℕ) :
    SourceSuffix N C (finalDate a (dates.take k)) (dates.drop k) := by
  induction k generalizing a dates with
  | zero => simpa only [List.take_zero,List.drop_zero,finalDate] using h
  | succ k ih =>
      cases dates with
      | nil => simpa only [List.take_nil,List.drop_nil,finalDate] using h
      | cons b dates =>
          simpa only [List.take_succ_cons,List.drop_succ_cons,finalDate] using
            ih b dates (source_suffix_cons N C a b dates h).2.2.2

/-- Completeness and chronology are DERIVED from the actual sorted agenda. -/
theorem actual_original_post_suffix (N : RootedBinary V E X) (C : Calendar N.graph) (k : ℕ) :
    SourceSuffix N C (prefixDate N C k) (originalPostDates N C k) := by
  obtain ⟨a,dates,he⟩ := List.exists_cons_of_ne_nil (original_dates_nonempty N C)
  simpa only [prefixDate,originalPostDates,he,List.tail_cons] using
    source_suffix_take_drop N C a dates (original_initial_suffix N C he) k

lemma sampling_suffix_original (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (k : ℕ) :
    samplingSuffix N C H gamma common k =
      calendarTail N C H gamma common (prefixDate N C k) (originalPostDates N C k) := by
  obtain ⟨a,dates,he⟩ := List.exists_cons_of_ne_nil (original_dates_nonempty N C)
  simp only [samplingSuffix,originalPostDates,prefixDate,he,List.tail_cons]

lemma actual_post_dates_length (N : RootedBinary V E X) (C : Calendar N.graph) (k : ℕ) :
    (originalPostDates N C k).length ≤ (originalDates N C).card - 1 := by
  simp only [originalPostDates,List.length_drop,List.length_tail,sortedOriginalDates,Finset.length_sort]
  exact Nat.sub_le _ _

/-- This reference is fixed before any bank, rate, site family or count vector. -/
def samplingReference (N : RootedBinary V E X) (sample : Copy → X) : Code N sample :=
  activatedCode N sample (fun _ => false)

lemma reference_rebank_observation (N : RootedBinary V E X) (sample : Copy → X)
    (sigma : V → Bool) :
    observeCode N (reBank N (samplingReference N sample) sigma) =
      observeCode N (activatedCode N sample sigma) ∧
      (state (reBank N (samplingReference N sample) sigma)).register =
        (state (activatedCode N sample sigma)).register := by
  refine ⟨?_,?_⟩
  · rw [(actual_reBank_observation N (samplingReference N sample) sigma).1]
    simp only [samplingReference,activated_observation]
    rfl
  · rw [(actual_reBank_observation N (samplingReference N sample) sigma).2,activated_register]

lemma sampling_reference_active (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (c : ℝ) (hc : ∀ x : Copy, C.age (N.leaf (sample x)) = c) :
    ∀ x : Copy, copyLocation (state (samplingReference N sample)) x ∈ stageLocations N C c := by
  intro x
  have hbefore : c < C.age N.root := by rw [← hc x]; exact leaf_before_root N C (sample x)
  rw [stageLocations,if_pos hbefore]
  apply (mem_activeLocations N C c _).mpr
  refine ⟨sampleEdge N (sample x),?_,?_⟩
  · have h := congrArg (fun o => o.2 x) (activated_observation N sample (fun _=>false))
    exact h
  · constructor
    · rw [sampleEdge_target,hc x]
    · have h := C.edge_older (sampleEdge N (sample x))
      simpa only [sampleEdge_target,hc x] using h

/-- A scientific global active-population bound already forces P>=1 at sampling. -/
lemma actual_population_bound_positive [Nonempty Copy] (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (c : ℝ)
    (hc : ∀ x : Copy, C.age (N.leaf (sample x)) = c) (P : ℕ)
    (hP : ∀ t : ℝ, c ≤ t → t < C.age N.root → (Finset.univ.filter (C.Active t)).card ≤ P) :
    1 ≤ P := by
  let x : Copy := Classical.choice inferInstance
  have hbefore : c < C.age N.root := by rw [← hc x]; exact leaf_before_root N C (sample x)
  have ha := sampling_reference_active N C sample c hc x
  rw [stageLocations,if_pos hbefore] at ha
  obtain ⟨edge,_,he⟩ := (mem_activeLocations N C c _).mp ha
  have hone : 1 ≤ (Finset.univ.filter (C.Active c)).card :=
    Finset.one_le_card.mpr ⟨edge,Finset.mem_filter.mpr ⟨Finset.mem_univ _,he⟩⟩
  exact hone.trans (hP c le_rfl hbefore)

/-- The exact scientific P bound specializes to every actual suffix carrier;
root-date active edges are empty, and the root carrier is one population. -/
theorem actual_original_tuple_card [Nonempty Copy]
    (e : Copy ≃ Fin (Fintype.card Copy)) (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (c : ℝ)
    (hc : ∀ x : Copy, C.age (N.leaf (sample x)) = c) (k : ℕ)
    (hk : prefixDate N C k = c) (P : ℕ)
    (hP : ∀ t : ℝ, c ≤ t → t < C.age N.root → (Finset.univ.filter (C.Active t)).card ≤ P) :
    let n := Fintype.card Copy
    let B := ∑ j ∈ Finset.range n, (n.choose 2)^j
    let S := BellCount n * P^n
    Fintype.card (TupleIndex e N C (originalPostDates N C k) (samplingReference N sample)) ≤
      B * (n*B*S)^(originalPostDates N C k).length := by
  apply actual_tuple_index_card e N C (originalPostDates N C k) (samplingReference N sample) P
    (actual_population_bound_positive N C sample c hc P hP)
  intro b hb
  have hs := actual_original_post_suffix N C k
  rw [hk] at hs
  have hbc := hs.2.2.1 b hb
  by_cases hbefore : b < C.age N.root
  · exact hP b hbc.1.le hbefore
  · have heq : b = C.age N.root := le_antisymm hbc.2 (le_of_not_gt hbefore)
    have hempty : Finset.univ.filter (C.Active b) = ∅ := by
      apply Finset.eq_empty_iff_forall_not_mem.mpr
      intro edge he
      have ha := (Finset.mem_filter.mp he).2
      have hu := original_root_latest N C (N.graph.source edge)
      rw [heq] at ha
      exact (not_lt_of_ge hu) ha.2
    simp only [hempty,Finset.card_empty,Nat.zero_le]

/-- The original observed coefficient, simultaneously for every unchanged
bank and balanced site family; no register-dependent index choice. -/
theorem actual_original_observed_tuple [Nonempty Copy]
    (e : Copy ≃ Fin (Fintype.card Copy)) (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (c : ℝ)
    (hc : ∀ x : Copy, C.age (N.leaf (sample x)) = c) :
    ∃ k : ℕ, prefixDate N C k = c ∧
      ∀ (sigma : V → Bool) (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
        (common : Hybrid N → Bool) (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base),
      (∀ j, ∑ x, q j x = 0) →
      observedFourier L N C sample sigma H gamma common r q =
        ∑ t : TupleIndex e N C (originalPostDates N C k) (samplingReference N sample),
          tupleTerm e N C H gamma common r L q sigma c (originalPostDates N C k)
            (samplingReference N sample) t := by
  obtain ⟨k,hk⟩ := actual_sampling_cut_exists N C sample c hc
  refine ⟨k,hk,?_⟩
  intro sigma H gamma common r L q hbal
  have hs := actual_original_post_suffix N C k
  rw [hk] at hs
  have hv := actual_calendar_tuple_expansion e N C H gamma common r L q hbal c
    (originalPostDates N C k) hs (samplingReference N sample)
    (sampling_reference_active N C sample c hc) sigma
  have ho := reference_rebank_observation N sample sigma
  have heq := actual_guarded_calendar_quotient N r L q hbal
    (calendarTail N C H gamma common c (originalPostDates N C k))
    (reBank N (samplingReference N sample) sigma) (activatedCode N sample sigma) ho.1 ho.2
  rw [actual_observed_guarded_calendar N C sample sigma H gamma common r L q hbal,
    actual_sampling_backward_reduction N C sample sigma H gamma common r L q hbal c hc k hk,
    sampling_suffix_original, hk,← heq]
  exact hv.2

#print axioms actual_original_post_suffix
#print axioms actual_post_dates_length
#print axioms actual_population_bound_positive
#print axioms actual_original_tuple_card
#print axioms actual_original_observed_tuple
end ResearchCommons.MSCI.JC69OriginalAgendaTuples
