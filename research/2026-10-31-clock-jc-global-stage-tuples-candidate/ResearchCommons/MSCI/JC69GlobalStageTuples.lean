import ResearchCommons.MSCI.JC69StagePathCoefficient
import ResearchCommons.MSCI.JC69ActiveStage
import ResearchCommons.MSCI.JC69RootCanonicalRatios

/-! WORKING, UNCOMPILED. Actual supported-calendar tuple construction.
Dot (OpenAI), 31 October 2026. Original Copy, one whole date block per stage,
fixed admitted representatives, original bank outside no partial product.
This working file is not a compiler request or accepted theorem. -/
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace ResearchCommons.MSCI.JC69GlobalStageTuples
open MeasureTheory Set Nanuq.Source GProgram.SourceForest
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceAncestralCompletion
open UnifiedLean.Source.NativeParentRouting
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceBoundaryKernels
open ResearchCommons.MSCI.JC69 ResearchCommons.MSCI.JC69FixedBankBoundary
open ResearchCommons.MSCI.JC69OrderedPathExpansion ResearchCommons.MSCI.JC69CanonicalPathCount
open ResearchCommons.MSCI.JC69CanonicalWeightedSum ResearchCommons.MSCI.JC69CommonCountIndex
open ResearchCommons.MSCI.JC69WeightedCalendar ResearchCommons.MSCI.JC69GuardedCalendarQuotient
open ResearchCommons.MSCI.JC69BoundaryWord
open ResearchCommons.MSCI.JC69RootCanonicalRatios ResearchCommons.MSCI.JC69StagePathCoefficient
open ResearchCommons.MSCI.JC69SupportedStateBound ResearchCommons.MSCI.JC69ActiveStage
open scoped Classical BigOperators ENNReal NNReal
variable {V E Copy X : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Original source dates, not a desired likelihood/quotient hypothesis. -/
def SourceSuffix (N : RootedBinary V E X) (C : Calendar N.graph)
    (a : ℝ) (dates : List ℝ) : Prop :=
  a ≤ C.age N.root ∧ dates.Pairwise (· < ·) ∧
    (∀ b ∈ dates, a < b ∧ b ≤ C.age N.root) ∧
    (∀ v : V, a < C.age v → C.age v ∈ dates)

lemma source_suffix_nil (N : RootedBinary V E X) (C : Calendar N.graph)
    (a : ℝ) (h : SourceSuffix N C a []) : a = C.age N.root := by
  apply le_antisymm h.1
  by_contra hn
  have hp : a < C.age N.root := lt_of_not_ge hn
  simpa using h.2.2.2 N.root hp

lemma source_suffix_cons (N : RootedBinary V E X) (C : Calendar N.graph)
    (a b : ℝ) (dates : List ℝ) (h : SourceSuffix N C a (b::dates)) :
    a < b ∧ b ≤ C.age N.root ∧
    (∀ v : V, a < C.age v → b ≤ C.age v) ∧ SourceSuffix N C b dates := by
  have hb := h.2.2.1 b (by simp)
  have ho := List.pairwise_cons.mp h.2.1
  refine ⟨hb.1,hb.2,?_,hb.2,ho.2,?_,?_⟩
  · intro v hv
    rcases List.mem_cons.mp (h.2.2.2 v hv) with he | he
    · exact he.ge
    · exact (ho.1 _ he).le
  · intro d hd
    exact ⟨ho.1 d hd,(h.2.2.1 d (List.mem_cons_of_mem _ hd)).2⟩
  · intro v hv
    have hm := h.2.2.2 v (hb.1.trans hv)
    exact (List.mem_cons.mp hm).resolve_left (ne_of_gt hv)

/-- Actual whole original boundary word, before embedding it in ProgramStep. -/
def originalBoundaryWord (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (b : ℝ) : List (BoundaryOperation N) :=
  ((Finset.univ.filter (fun e : E => C.age (N.graph.source e) = b)).toList.map
    (fun e => .exit e)) ++
  ((Finset.univ.filter (fun v : V => C.age v = b)).toList.map
    (originalNodeOperation N H gamma common))

lemma original_boundary_word_map (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (b : ℝ) :
    (originalBoundaryWord N C H gamma common b).map ProgramStep.boundary =
      boundaryOperations N C H gamma common b := by
  simp [originalBoundaryWord,boundaryOperations,List.map_map,Function.comp_def]

/-- Count/rate/bank-independent dependent index. Exactly one next-state
choice per WHOLE boundary word; no initial-state sum or intermediate target. -/
def TupleIndex (e : Copy ≃ Fin (Fintype.card Copy))
    (N : RootedBinary V E X) (C : Calendar N.graph) {sample : Copy → X} :
    List ℝ → Code N sample → Type _
  | [], s => CanonicalPath e N (Fintype.card Copy) s
  | b::dates, s => CommonTermIndex e N (Fintype.card Copy) s ×
      ((o : SupportedObservation N sample (stageLocations N C b)) ×
        TupleIndex e N C dates (representative N o))

instance tupleIndexFintype (e : Copy ≃ Fin (Fintype.card Copy))
    (N : RootedBinary V E X) (C : Calendar N.graph) {sample : Copy → X}
    (dates : List ℝ) (s : Code N sample) : Fintype (TupleIndex e N C dates s) := by
  induction dates generalizing s with
  | nil => exact inferInstanceAs (Fintype (CanonicalPath e N (Fintype.card Copy) s))
  | cons b dates ih =>
      letI : ∀ d : Code N sample, Fintype (TupleIndex e N C dates d) := ih
      exact inferInstanceAs (Fintype (CommonTermIndex e N (Fintype.card Copy) s ×
        ((o : SupportedObservation N sample (stageLocations N C b)) ×
          TupleIndex e N C dates (representative N o))))

/-- Signed term of the actual path product. The original sigma is passed
unchanged to every boundary; it is not independently averaged per stage. -/
def tupleTerm (e : Copy ≃ Fin (Fintype.card Copy))
    (N : RootedBinary V E X) (C : Calendar N.graph) {sample : Copy → X}
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (L : ℕ)
    (q : Fin L → Copy → Base) (sigma : V → Bool) :
    (a : ℝ) → (dates : List ℝ) → (s : Code N sample) → TupleIndex e N C dates s → ℝ
  | _, [], s, h => rootCoefficient N r L q (Fintype.card Copy) s h.val
  | a, b::dates, s, h =>
      commonCoefficient e N r L q (Fintype.card Copy) s
        (observeCode N (pathEnd N (Fintype.card Copy) s h.1.1.val)) h.1 *
      (boundaryCoefficient N (originalBoundaryWord N C H gamma common b)
        (reBank N (pathEnd N (Fintype.card Copy) s h.1.1.val) sigma) h.2.1.val).toReal *
      Real.exp (-commonRate e N r L q (Fintype.card Copy) s h.1 * (b-a)) *
      tupleTerm e N C H gamma common r L q sigma b dates (representative N h.2.1) h.2.2

/-- Concrete tuple count, not a generic finite-mixture cardinal premise.
The original P premise remains visible at each actual output date. -/
theorem actual_tuple_index_card [Nonempty Copy]
    (e : Copy ≃ Fin (Fintype.card Copy)) (N : RootedBinary V E X)
    (C : Calendar N.graph) {sample : Copy → X} (dates : List ℝ)
    (s : Code N sample) (P : ℕ) (hroot : 1 ≤ P)
    (hP : ∀ b ∈ dates, (Finset.univ.filter (C.Active b)).card ≤ P) :
    Fintype.card (TupleIndex e N C dates s) ≤
      (∑ k ∈ Finset.range (Fintype.card Copy), ((Fintype.card Copy).choose 2)^k) *
      (Fintype.card Copy *
        (∑ k ∈ Finset.range (Fintype.card Copy), ((Fintype.card Copy).choose 2)^k) *
        (BellCount (Fintype.card Copy) * P ^ Fintype.card Copy)) ^ dates.length := by
  let n := Fintype.card Copy
  let B := ∑ k ∈ Finset.range n, (n.choose 2)^k
  let S := BellCount n * P ^ n
  change Fintype.card (TupleIndex e N C dates s) ≤ B * (n*B*S)^dates.length
  induction dates generalizing s with
  | nil =>
      simpa only [TupleIndex,List.length_nil,pow_zero,mul_one] using
        actual_canonical_path_card_le e N (Fintype.card Copy) s
  | cons b dates ih =>
      have hi : ∀ d : Code N sample,
          Fintype.card (TupleIndex e N C dates d) ≤ B * (n*B*S)^dates.length := by
        intro d
        exact ih d (fun c hc => hP c (List.mem_cons_of_mem b hc))
      have hs : Fintype.card (SupportedObservation N sample (stageLocations N C b)) ≤ S :=
        stage_supported_card N C sample b P hroot (hP b (by simp))
      have hp : Fintype.card (CommonTermIndex e N (Fintype.card Copy) s) ≤ n*B :=
        actual_interval_boundary_index_card e N s
      change Fintype.card (CommonTermIndex e N (Fintype.card Copy) s ×
        ((o : SupportedObservation N sample (stageLocations N C b)) ×
          TupleIndex e N C dates (representative N o))) ≤ _
      rw [Fintype.card_prod,Fintype.card_sigma]
      calc
        _ ≤ (n*B) * ∑ o : SupportedObservation N sample (stageLocations N C b),
            B * (n*B*S)^dates.length :=
          Nat.mul_le_mul hp (Finset.sum_le_sum (fun o _ => hi (representative N o)))
        _ = (n*B) * (Fintype.card (SupportedObservation N sample (stageLocations N C b)) *
            (B * (n*B*S)^dates.length)) := by simp
        _ ≤ (n*B) * (S * (B * (n*B*S)^dates.length)) :=
          Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hs)
        _ = B * (n*B*S)^(b::dates).length := by
          rw [List.length_cons,pow_succ]
          ring


lemma representative_locations (N : RootedBinary V E X) {sample : Copy → X}
    {A : Finset (Location V E)} (o : SupportedObservation N sample A) :
    ∀ x : Copy, copyLocation (state (representative N o)) x ∈ A := by
  have ho := congrArg Prod.snd (representative_observation N o)
  intro x
  change (observeCode N (representative N o)).2 x ∈ A
  rw [ho]
  exact o.property.2 x

lemma rebank_locations (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (sigma : V → Bool) (A : Finset (Location V E))
    (hs : ∀ x : Copy, copyLocation (state s) x ∈ A) :
    ∀ x : Copy, copyLocation (state (reBank N s sigma)) x ∈ A := by
  have ho := congrArg Prod.snd (actual_reBank_observation N s sigma).1
  intro x
  change (observeCode N (reBank N s sigma)).2 x ∈ A
  rw [ho]
  exact hs x

lemma stage_indicator_coefficient (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E) (L : ℕ)
    (q : Fin L → Copy → Base) (a b : ℝ) (s : Code N sample)
    (o : BlockPopulationObservation Copy V E) :
    programObservationWeight N r L q (stageProgram N C H gamma common a b) s o =
      intervalBoundaryCoefficient N r L q (Real.toNNReal (b-a))
        (originalBoundaryWord N C H gamma common b) s o := by
  rw [programObservationWeight,actual_calendar_weighted_recursion]
  simp only [intervalBoundaryCoefficient,stageProgram,original_boundary_word_map]

/-- Exact source value, not an assumed scalar likelihood: finiteness is
proved simultaneously, before substituting any signed local coefficient. -/
theorem actual_calendar_tuple_expansion [Nonempty Copy]
    (e : Copy ≃ Fin (Fintype.card Copy)) (N : RootedBinary V E X)
    (C : Calendar N.graph) {sample : Copy → X} (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (L : ℕ) (q : Fin L → Copy → Base)
    (hbal : ∀ j, ∑ x, q j x = 0)
    (a : ℝ) (dates : List ℝ) (hdates : SourceSuffix N C a dates)
    (s : Code N sample) (hs : ∀ x : Copy, copyLocation (state s) x ∈ stageLocations N C a)
    (sigma : V → Bool) :
    let value := calendarValue N r L q (guardedRoot N r L q)
      (calendarTail N C H gamma common a dates) (reBank N s sigma)
    value ≠ ∞ ∧ value.toReal =
      ∑ t : TupleIndex e N C dates s, tupleTerm e N C H gamma common r L q sigma a dates s t := by
  induction dates generalizing a s with
  | nil =>
      have ha := source_suffix_nil N C a hdates
      have hroot : AncestralRoot N s := by
        intro x
        simpa only [ha,stageLocations,lt_self_iff_false,if_false,Finset.mem_singleton] using hs x
      have heq : guardedRoot N r L q (reBank N s sigma) = rootWeight N r L q s := by
        rw [guarded_root_observation N r L q hbal (reBank N s sigma) s
          (actual_reBank_observation N s sigma).1,guardedRoot,if_pos hroot]
      have hb : liveCard s ≤ Fintype.card Copy + 1 :=
        (Finset.card_le_univ s.val.live).trans (Nat.le_succ _)
      change guardedRoot N r L q (reBank N s sigma) ≠ ∞ ∧ _
      rw [heq]
      constructor
      · rw [actual_root_canonical_ratio_sum e N r L q hbal (Fintype.card Copy) s hroot hb]
        exact ENNReal.sum_ne_top.mpr (fun _ _ => ENNReal.ofReal_ne_top)
      · exact actual_root_canonical_real_sum e N r L q hbal (Fintype.card Copy) s hroot hb
  | cons b dates ih =>
      obtain ⟨hab,hb,hgap,htail⟩ := source_suffix_cons N C a b dates hdates
      have ha : a < C.age N.root := hab.trans_le hb
      have hactive : ActiveCode N C a (reBank N s sigma) := by
        have hloc := rebank_locations N s sigma (stageLocations N C a) hs
        simpa only [stageLocations,if_pos ha,ActiveCode] using hloc
      let A := SupportedObservation N sample (stageLocations N C b)
      let R : A → Code N sample := fun o => representative N o
      let d : A → Code N sample := fun o => reBank N (R o) sigma
      let post := calendarTail N C H gamma common b dates
      let future : A → ℝ≥0∞ := fun o => calendarValue N r L q (guardedRoot N r L q) post (d o)
      let coefficient : A → ℝ≥0∞ := fun o => intervalBoundaryCoefficient N r L q
        (Real.toNNReal (b-a)) (originalBoundaryWord N C H gamma common b) (reBank N s sigma) o.val
      have hind (o : A) : future o ≠ ∞ ∧ (future o).toReal =
          ∑ t : TupleIndex e N C dates (R o),
            tupleTerm e N C H gamma common r L q sigma b dates (R o) t :=
        ih b htail (R o) (representative_locations N o)
      obtain ⟨F,hF,hstage⟩ := actual_stage_guarded_transfer N C H gamma common r L q hbal
        a b hab hb hgap (reBank N s sigma) hactive post
      have hf (o : A) : F o.val = future o := by
        have hr : (state (d o)).register = (state (reBank N s sigma)).register :=
          (actual_reBank_observation N (R o) sigma).2.trans
            (actual_reBank_observation N s sigma).2.symm
        have h := (hF (d o) hr).symm
        simpa only [d,R,(actual_reBank_observation N (R o) sigma).1,
          representative_observation] using h
      have hrec : calendarValue N r L q (guardedRoot N r L q)
          (calendarTail N C H gamma common a (b::dates)) (reBank N s sigma) =
          ∑ o : A, coefficient o * future o := by
        change calendarValue N r L q (guardedRoot N r L q)
          (stageProgram N C H gamma common a b ++ post) (reBank N s sigma) = _
        rw [hstage]
        apply Finset.sum_congr rfl
        intro o _
        rw [stage_indicator_coefficient,hf]
      have hcf (o : A) : coefficient o ≠ ∞ :=
        actual_interval_boundary_finite N r L q _ _ _ o.val
      have hprod (o : A) : coefficient o * future o ≠ ∞ :=
        ENNReal.mul_ne_top (hcf o) (hind o).1
      constructor
      · rw [hrec]
        exact ENNReal.sum_ne_top.mpr (fun o _ => hprod o)
      · rw [hrec,ENNReal.toReal_sum (fun o _ => hprod o)]
        simp_rw [ENNReal.toReal_mul]
        have hc (o : A) : (coefficient o).toReal =
            ∑ i : CommonTermIndex e N (Fintype.card Copy) s,
              commonCoefficient e N r L q (Fintype.card Copy) s
                (observeCode N (pathEnd N (Fintype.card Copy) s i.1.val)) i *
              (boundaryCoefficient N (originalBoundaryWord N C H gamma common b)
                (reBank N (pathEnd N (Fintype.card Copy) s i.1.val) sigma) o.val).toReal *
              Real.exp (-commonRate e N r L q (Fintype.card Copy) s i * (b-a)) := by
          have he := actual_interval_boundary_path_expansion e N r L q (Real.toNNReal (b-a))
            (originalBoundaryWord N C H gamma common b) (reBank N s sigma) s
            (actual_reBank_observation N s sigma).1 o.val
          simpa only [coefficient,(actual_reBank_observation N s sigma).2,
            Real.coe_toNNReal _ (sub_nonneg.mpr hab.le)] using he
        simp_rw [hc,fun o => (hind o).2,Finset.sum_mul,Finset.mul_sum]
        rw [Finset.sum_comm]
        simp only [TupleIndex,Fintype.sum_prod_type,Fintype.sum_sigma,tupleTerm,R]

#print axioms source_suffix_nil
#print axioms source_suffix_cons
#print axioms original_boundary_word_map
#print axioms actual_tuple_index_card
#print axioms actual_calendar_tuple_expansion
end ResearchCommons.MSCI.JC69GlobalStageTuples
