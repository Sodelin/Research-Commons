import G6NativePhaseClocks
import UnifiedLean.Source.SourceMergerClockCatalogue

/-!
Actual paired legal-merger phase relation and surviving-clock square.
Cloud Sol delegated original G6 structural/source lane, 8 October 2026.
Original snapshot/merge/clock catalogue providers: Dot. This additive consumer
is compiler UNCHECKED and outside the sole181 and preceding179 inputs.

No source-law equality or physical prefix marginal is supplied as a field.
The original full current owners, old grafted trees, outside register and
protected child phase remain explicit. Natural second initialization and
complete tied calendar boundary transport are separate obligations.
-/

namespace UnifiedLean.G6.MergerPhaseSquare
set_option backward.isDefEq.respectTransparency false
open MeasureTheory ProbabilityTheory Nanuq.Source GProgram.SourceForest GProgram.G5
open GProgram.SourceForestKingmanPopulationProjection
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceMergerClockCatalogue
open UnifiedLean.Source.SourceActualHoldingClocks
open UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.SourceRaceWinnerSelection
open UnifiedLean.Source.SourceWinningClockReset
open UnifiedLean.G6.OriginalSpliceAdapter UnifiedLean.G6.SpineBoundaryCarrier
open UnifiedLean.G6.ProtectedChildCarrier UnifiedLean.G6.BoundaryPhaseRelation
open UnifiedLean.G6.NativePhaseClocks
open GProgram.G2.LiteralMarkedClockTrace
open scoped Classical
attribute [local instance] GProgram.G2.LiteralMarkedClockTrace.codeMeasurable

variable {V E X Copy : Type*}
variable [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]
variable (N : RootedBinary V E X)
variable (hcut : ∀ e, N.graph.IsHybrid (N.graph.source e) → N.graph.IsBridge e)
variable (b : N.graph.Blob) (hb : b ≠ N.graph.blobOf N.root)
variable (hp : Nat.card (BlobIncidentPorts.IncidentPorts N b) = 2)

/-- Actual finite coding preserves the exact redirected original owner. -/
theorem merger_ancestor {sample : Copy → X} (s : Code N sample) (p : Choice N s)
    (x : Copy) :
    (state (stepDestination N s (some p))).ancestor x =
      if (state s).ancestor x = p.2.val.2 then p.2.val.1 else (state s).ancestor x := rfl

theorem merger_register {sample : Copy → X} (s : Code N sample) (p : Choice N s)
    (v : V) : (state (stepDestination N s (some p))).register v =
      (state s).register v := rfl

/-- Only LIVE output trees are compared; dead snapshot padding is irrelevant. -/
theorem merger_live_genealogy {sample : Copy → X} (s : Code N sample) (p : Choice N s)
    (l : Copy) (hl : l ∈ (state (stepDestination N s (some p))).live) :
    (state (stepDestination N s (some p))).genealogy l =
      if l = p.2.val.1 then .graft ((state s).genealogy p.2.val.1)
        ((state s).genealogy p.2.val.2) else (state s).genealogy l := by
  unfold state stepDestination admittedCode
  rw [decode_encode_live_genealogy]
  rfl
  exact hl

/-- Every ORIGINAL labelled copy keeps its real current population through
the actual merger, even when its representative changes from b to a. -/
theorem merger_copy_location {sample : Copy → X} (s : Code N sample) (p : Choice N s)
    (x : Copy) : copyLocation (state (stepDestination N s (some p))) x =
      copyLocation (state s) x := by
  unfold state stepDestination admittedCode
  rw [decode_encode_copyLocation]
  exact merge_population_preserved _
    (population_pair_is_source_legal (state s) (originalPlace N p.1)
      (originalPlace_not_node N p.1) p.2.property) x

/-- Calendar licence is preserved by the actual merger, because all original
copy populations are preserved; it is not extended across a boundary date. -/
theorem merger_epoch_compatible {sample : Copy → X} (C : Calendar N.graph) (a until : ℝ)
    (s : Code N sample) (p : Choice N s)
    (hs : EpochCompatible N C a until (state s)) :
    EpochCompatible N C a until (state (stepDestination N s (some p))) :=
  actual_step_destination_epoch N C s hs (some p)

theorem paired_choice_operands {sample : Copy → X}
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) (p : Choice N s) :
    (actualChoiceEquiv N hcut b hb hp s t h p).2.val = p.2.val := rfl

/-- Both actual source mergers erase the same second original owner, graft
the SAME old operand trees, and leave every outside register value unchanged.
The guarded current-location partition is preserved for every original copy. -/
theorem paired_step_related {sample : Copy → X}
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) (p : Choice N s) :
    Related N hcut b hb hp (stepDestination N s (some p))
      (stepDestination (suppressedNetwork N hcut b hb hp) t
        (some (actualChoiceEquiv N hcut b hb hp s t h p))) := by
  let q := actualChoiceEquiv N hcut b hb hp s t h p
  have hq : q.2.val = p.2.val := rfl
  have hl : (state (stepDestination (suppressedNetwork N hcut b hb hp) t (some q))).live =
      (state (stepDestination N s (some p))).live := by
    rw [merged_live, merged_live, h.live, hq]
  refine ⟨hl, ?_, ?_, ?_, ?_⟩
  · funext x
    rw [merger_ancestor, merger_ancestor]
    simp only [hq, h.ancestor]
  · intro l hls
    have hlt : l ∈ (state (stepDestination (suppressedNetwork N hcut b hb hp) t
        (some q))).live := by rw [hl]; exact hls
    have hle : l ∈ (state s).live.erase p.2.val.2 := by
      simpa only [merged_live] using hls
    have hlo : l ∈ (state s).live := (Finset.mem_erase.mp hle).2
    have ha : p.2.val.1 ∈ (state s).live :=
      (Finset.mem_filter.mp (Finset.mem_offDiag.mp p.2.property).1).1
    have hc : p.2.val.2 ∈ (state s).live :=
      (Finset.mem_filter.mp (Finset.mem_offDiag.mp p.2.property).2.1).1
    rw [merger_live_genealogy _ _ _ l hlt, merger_live_genealogy _ _ _ l hls]
    simp only [hq]
    by_cases hla : l = p.2.val.1
    · simp only [hla, ite_true, h.genealogy _ ha, h.genealogy _ hc]
    · simp only [hla, ite_false, h.genealogy _ hlo]
  · intro v
    rw [merger_register, merger_register]
    exact h.outsideRegister v
  · intro x
    obtain ⟨j, ho, hn⟩ := h.location x
    refine ⟨j, ?_, ?_⟩
    · rw [merger_copy_location]
      exact ho
    · rw [merger_copy_location]
      exact hn

private theorem choice_eq {sample : Copy → X} (s : Code N sample) (p q : Choice N s)
    (hi : p.1 = q.1) (hab : p.2.val = q.2.val) : p = q := by
  cases p with
  | mk i p =>
      cases q with
      | mk j q =>
          cases hi
          exact congrArg (Sigma.mk i) (Subtype.ext hab)

/-- The genuine original surviving-clock inclusion COMMUTES with the derived
current-pair transport. No new/reset clock coordinates or rate laws are input.
Both sides retain the same original ordered operands and guarded physical site. -/
theorem destination_choice_square {sample : Copy → X}
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) (p : Choice N s)
    (a : Choice N (stepDestination N s (some p))) :
    actualChoiceEquiv N hcut b hb hp s t h (destinationChoiceOld N s p a) =
      destinationChoiceOld (suppressedNetwork N hcut b hb hp) t
        (actualChoiceEquiv N hcut b hb hp s t h p)
        (actualChoiceEquiv N hcut b hb hp (stepDestination N s (some p))
          (stepDestination (suppressedNetwork N hcut b hb hp) t
            (some (actualChoiceEquiv N hcut b hb hp s t h p)))
          (paired_step_related N hcut b hb hp s t h p) a) := by
  apply choice_eq (suppressedNetwork N hcut b hb hp) t
  · change newSite N hcut b hb hp
        (choiceSite N hcut b hb hp s t h (destinationChoiceOld N s p a)) =
      newSite N hcut b hb hp
        (choiceSite N hcut b hb hp (stepDestination N s (some p))
          (stepDestination (suppressedNetwork N hcut b hb hp) t
            (some (actualChoiceEquiv N hcut b hb hp s t h p)))
          (paired_step_related N hcut b hb hp s t h p) a)
    congr 1
    apply old_site_injective N hcut b hb hp
    rw [choice_site_spec, choice_site_spec]
    rfl
  · rfl

noncomputable def reindexClocks {sample : Copy → X}
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) :
    (Choice N s → ℝ) ≃ᵐ (Choice (suppressedNetwork N hcut b hb hp) t → ℝ) :=
  MeasurableEquiv.piCongrLeft
    (fun _ : Choice (suppressedNetwork N hcut b hb hp) t => ℝ)
    (actualChoiceEquiv N hcut b hb hp s t h)

theorem reindexed_clock_apply {sample : Copy → X}
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) (c : Choice N s → ℝ) (p : Choice N s) :
    reindexClocks N hcut b hb hp s t h c (actualChoiceEquiv N hcut b hb hp s t h p) =
      c p := MeasurableEquiv.piCongrLeft_apply_apply _ _ _

/-- The SAME winning waiting variable is subtracted from the SAME surviving
coordinate. This is the actual residual used by the original literal compiler. -/
theorem destination_residual_square {sample : Copy → X}
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) (c : Choice N s → ℝ) (p : Choice N s)
    (a : Choice N (stepDestination N s (some p))) :
    reindexClocks N hcut b hb hp s t h c
        (destinationClockEmbedding (suppressedNetwork N hcut b hb hp) t
          (actualChoiceEquiv N hcut b hb hp s t h p)
          (actualChoiceEquiv N hcut b hb hp (stepDestination N s (some p))
            (stepDestination (suppressedNetwork N hcut b hb hp) t
              (some (actualChoiceEquiv N hcut b hb hp s t h p)))
            (paired_step_related N hcut b hb hp s t h p) a)).val -
      reindexClocks N hcut b hb hp s t h c (actualChoiceEquiv N hcut b hb hp s t h p) =
        c (destinationClockEmbedding N s p a).val - c p := by
  change reindexClocks N hcut b hb hp s t h c
      (destinationChoiceOld (suppressedNetwork N hcut b hb hp) t
        (actualChoiceEquiv N hcut b hb hp s t h p)
        (actualChoiceEquiv N hcut b hb hp (stepDestination N s (some p))
          (stepDestination (suppressedNetwork N hcut b hb hp) t
            (some (actualChoiceEquiv N hcut b hb hp s t h p)))
          (paired_step_related N hcut b hb hp s t h p) a)) - _ = _
  rw [← destination_choice_square, reindexed_clock_apply, reindexed_clock_apply]

/-- The FULL destination vector commutes, including every outside current
pair coordinate; no selected two-lineage reset approximation is used. -/
theorem destination_residual_reindex {sample : Copy → X}
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) (c : Choice N s → ℝ) (p : Choice N s) :
    reindexClocks N hcut b hb hp (stepDestination N s (some p))
        (stepDestination (suppressedNetwork N hcut b hb hp) t
          (some (actualChoiceEquiv N hcut b hb hp s t h p)))
        (paired_step_related N hcut b hb hp s t h p)
        (fun a => c (destinationClockEmbedding N s p a).val - c p) =
      (fun a => reindexClocks N hcut b hb hp s t h c
          (destinationClockEmbedding (suppressedNetwork N hcut b hb hp) t
            (actualChoiceEquiv N hcut b hb hp s t h p) a).val -
        reindexClocks N hcut b hb hp s t h c (actualChoiceEquiv N hcut b hb hp s t h p)) := by
  funext a
  obtain ⟨j, rfl⟩ := (actualChoiceEquiv N hcut b hb hp (stepDestination N s (some p))
    (stepDestination (suppressedNetwork N hcut b hb hp) t
      (some (actualChoiceEquiv N hcut b hb hp s t h p)))
    (paired_step_related N hcut b hb hp s t h p)).surjective a
  rw [reindexed_clock_apply, destination_residual_square]

/-- An actual strict winner, including the none/tie branch, is equivariant
under finite coordinate relabelling. No positive-mass tie breaker is added. -/
theorem selected_winner_equiv {I J : Type*} [Fintype I] [Fintype J]
    [DecidableEq I] [DecidableEq J] (e : I ≃ J) (c : I → ℝ) :
    selectedWinner (fun q => c (e.symm q)) = (selectedWinner c).map e := by
  cases ho : selectedWinner c with
  | some p =>
      simp only [Option.map_some]
      apply (selectedWinner_eq_some_iff _ (e p)).mpr
      have hw := (selectedWinner_eq_some_iff c p).mp ho
      refine ⟨by simpa only [Equiv.symm_apply_apply] using hw.1, ?_⟩
      intro q
      have hq : e.symm q.val ≠ p := by
        intro he
        apply q.property
        calc
          q.val = e (e.symm q.val) := (e.apply_symm_apply q.val).symm
          _ = e p := congrArg e he
      simpa only [Equiv.symm_apply_apply] using hw.2 ⟨e.symm q.val, hq⟩
  | none =>
      simp only [Option.map_none]
      cases hn : selectedWinner (fun q => c (e.symm q)) with
      | none => rfl
      | some q =>
          have hw := (selectedWinner_eq_some_iff _ q).mp hn
          have hp : selectedWinner c = some (e.symm q) := by
            apply (selectedWinner_eq_some_iff c (e.symm q)).mpr
            refine ⟨hw.1, ?_⟩
            intro p
            have hpq : e p.val ≠ q := by
              intro he
              apply p.property
              simpa only [Equiv.symm_apply_apply] using congrArg e.symm he
            simpa only [Equiv.symm_apply_apply] using hw.2 ⟨e p.val, hpq⟩
          rw [ho] at hp
          cases hp

theorem reindexed_selected_winner {sample : Copy → X}
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) (c : Choice N s → ℝ) :
    selectedWinner (reindexClocks N hcut b hb hp s t h c) =
      (selectedWinner c).map (actualChoiceEquiv N hcut b hb hp s t h) := by
  have hc : reindexClocks N hcut b hb hp s t h c =
      fun q => c ((actualChoiceEquiv N hcut b hb hp s t h).symm q) := by
    funext q
    obtain ⟨p, rfl⟩ := (actualChoiceEquiv N hcut b hb hp s t h).surjective q
    rw [reindexed_clock_apply, Equiv.symm_apply_apply]
  rw [hc]
  exact selected_winner_equiv _ c

theorem no_merger_reindex {sample : Copy → X}
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) (c : Choice N s → ℝ) (duration : ℝ) :
    (∀ p : Choice N s, duration < c p) ↔
      ∀ q, duration < reindexClocks N hcut b hb hp s t h c q := by
  constructor
  · intro ho q
    obtain ⟨p, rfl⟩ := (actualChoiceEquiv N hcut b hb hp s t h).surjective q
    rw [reindexed_clock_apply]
    exact ho p
  · intro hn p
    simpa only [reindexed_clock_apply] using hn (actualChoiceEquiv N hcut b hb hp s t h p)

/-- Success flags, ALL absolute within-epoch ages (including padding), full
live forests/current owners and retained register agree in the explicit phase
relation. The distinct graph-specific Codes are never identified literally. -/
def TraceRelated {sample : Copy → X} (n : Nat)
    (old : Bool × ClockTrace N sample n)
    (new : Bool × ClockTrace (suppressedNetwork N hcut b hb hp) sample n) : Prop :=
  old.1 = new.1 ∧ ∀ i : Fin n,
    (old.2 i).1 = (new.2 i).1 ∧ (old.2 i).2.1 = (new.2 i).2.1 ∧
      Related N hcut b hb hp (old.2 i).2.2 (new.2 i).2.2

theorem empty_trace_related {sample : Copy → X} (n : Nat) (ok : Bool)
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) :
    TraceRelated N hcut b hb hp n (ok, emptyTrace N n s)
      (ok, emptyTrace (suppressedNetwork N hcut b hb hp) n t) :=
  ⟨rfl, fun _ => ⟨rfl, rfl, h⟩⟩

theorem prepend_trace_related {sample : Copy → X} {n : Nat} (age : ℝ)
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t)
    (old : Bool × ClockTrace N sample n)
    (new : Bool × ClockTrace (suppressedNetwork N hcut b hb hp) sample n)
    (hr : TraceRelated N hcut b hb hp n old new) :
    TraceRelated N hcut b hb hp (n+1) (old.1, prependTrace N age s old.2)
      (new.1, prependTrace (suppressedNetwork N hcut b hb hp) age t new.2) := by
  refine ⟨hr.1, ?_⟩
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact ⟨rfl, rfl, h⟩
  · exact ⟨(hr.2 j).1, congrArg (fun z : ℝ => age + z) (hr.2 j).2.1, (hr.2 j).2.2⟩

/-- Deterministic SAME-clock comparison of the ENTIRE original literal epoch
record at arbitrary finite merger budget, including exhausted/pathological
and padded branches. Every actual outside merger coordinate is included.
This remains a fixed frozen epoch; no h/r boundary is crossed physically. -/
theorem literal_trace_phase_relation {sample : Copy → X} (n : Nat) (duration : ℝ)
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) (c : Choice N s → ℝ) :
    TraceRelated N hcut b hb hp n (literalMarkedTrace N n duration s c)
      (literalMarkedTrace (suppressedNetwork N hcut b hb hp) n duration t
        (reindexClocks N hcut b hb hp s t h c)) := by
  induction n generalizing duration s t with
  | zero =>
      refine ⟨?_, ?_⟩
      · change decide (∀ p : Choice N s, duration < c p) =
          decide (∀ q, duration < reindexClocks N hcut b hb hp s t h c q)
        simp only [no_merger_reindex N hcut b hb hp s t h c duration]
      · intro i
        exact Fin.elim0 i
  | succ n ih =>
      have hno := no_merger_reindex N hcut b hb hp s t h c duration
      by_cases ho : ∀ p : Choice N s, duration < c p
      · have hn := hno.mp ho
        rw [literalMarkedTrace, if_pos ho, literalMarkedTrace, if_pos hn]
        exact empty_trace_related N hcut b hb hp (n+1) true s t h
      · have hn : ¬∀ q, duration < reindexClocks N hcut b hb hp s t h c q :=
          fun hh => ho (hno.mpr hh)
        rw [literalMarkedTrace, if_neg ho, literalMarkedTrace, if_neg hn]
        cases hw : selectedWinner c with
        | none =>
            have hnew : selectedWinner (reindexClocks N hcut b hb hp s t h c) = none := by
              rw [reindexed_selected_winner, hw]
              rfl
            rw [hnew]
            exact empty_trace_related N hcut b hb hp (n+1) false s t h
        | some p =>
            have hnew : selectedWinner (reindexClocks N hcut b hb hp s t h c) =
                some (actualChoiceEquiv N hcut b hb hp s t h p) := by
              rw [reindexed_selected_winner, hw]
              rfl
            rw [hnew, reindexed_clock_apply]
            by_cases hpclock : c p ≤ duration
            · simp only [if_pos hpclock]
              have hr := ih (duration-c p) (stepDestination N s (some p))
                (stepDestination (suppressedNetwork N hcut b hb hp) t
                  (some (actualChoiceEquiv N hcut b hb hp s t h p)))
                (paired_step_related N hcut b hb hp s t h p)
                (fun a => c (destinationClockEmbedding N s p a).val-c p)
              rw [destination_residual_reindex] at hr
              exact prepend_trace_related N hcut b hb hp (c p)
                (stepDestination N s (some p))
                (stepDestination (suppressedNetwork N hcut b hb hp) t
                  (some (actualChoiceEquiv N hcut b hb hp s t h p)))
                (paired_step_related N hcut b hb hp s t h p) _ _ hr
            · simp only [if_neg hpclock]
              exact empty_trace_related N hcut b hb hp (n+1) false s t h

/-- Both records are compiled by their OWN inherited literal source compiler
from a SAME native current-clock vector, with the derived coordinate map.
The second graph is started at t; no independent prefix law for t is assumed. -/
noncomputable def pairedEpochRecords {sample : Copy → X} (n : Nat) (duration : ℝ)
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) (c : Choice N s → ℝ) :
    (Bool × ClockTrace N sample n) ×
      (Bool × ClockTrace (suppressedNetwork N hcut b hb hp) sample n) :=
  (literalMarkedTrace N n duration s c,
    literalMarkedTrace (suppressedNetwork N hcut b hb hp) n duration t
      (reindexClocks N hcut b hb hp s t h c))

theorem paired_epoch_records_measurable {sample : Copy → X} (n : Nat) (duration : ℝ)
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) :
    Measurable (pairedEpochRecords N hcut b hb hp n duration s t h) :=
  (marked_trace_measurable N n s duration).prodMk
    ((marked_trace_measurable (suppressedNetwork N hcut b hb hp) n t duration).comp
      (reindexClocks N hcut b hb hp s t h).measurable)

noncomputable def pairedEpochLaw {sample : Copy → X} (r : PositivePairRates E)
    (n : Nat) (duration : ℝ) (s : Code N sample)
    (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) :
    Measure ((Bool × ClockTrace N sample n) ×
      (Bool × ClockTrace (suppressedNetwork N hcut b hb hp) sample n)) :=
  (currentPairClockMeasure N r s).map (pairedEpochRecords N hcut b hb hp n duration s t h)

/-- Normalization is inherited from the ACTUAL native product and measurable
compiler. Failed/exhausted budget records are retained, not conditioned away. -/
theorem paired_epoch_probability {sample : Copy → X} (r : PositivePairRates E)
    (n : Nat) (duration : ℝ) (s : Code N sample)
    (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) :
    IsProbabilityMeasure (pairedEpochLaw N hcut b hb hp r n duration s t h) := by
  letI := GProgram.G2.HistoryResidualAttachment.current_clock_probability N r s
  exact Measure.isProbabilityMeasure_map
    (paired_epoch_records_measurable N hcut b hb hp n duration s t h).aemeasurable

/-- The first marginal is the actual original native marked-epoch law. -/
theorem paired_epoch_original_marginal {sample : Copy → X} (r : PositivePairRates E)
    (n : Nat) (duration : ℝ) (s : Code N sample)
    (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) :
    (pairedEpochLaw N hcut b hb hp r n duration s t h).map Prod.fst =
      actualMarkedTraceLaw N r n s duration := by
  unfold pairedEpochLaw actualMarkedTraceLaw
  rw [Measure.map_map measurable_fst (paired_epoch_records_measurable N hcut b hb hp _ _ _ _ _)]
  rfl

/-- The second marginal is DERIVED to be the SECOND graph's own actual
native marked-epoch law at t, under the local before-h rate bank.
Thus every outside merger, elapsed age, current forest and shared register
in that conditional epoch record is transported jointly, not fitted marginally.
Naturally initialized t-prefix and physical later phases remain separate. -/
theorem paired_epoch_constructed_marginal {sample : Copy → X} (r : PositivePairRates E)
    (n : Nat) (duration : ℝ) (s : Code N sample)
    (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) :
    (pairedEpochLaw N hcut b hb hp r n duration s t h).map Prod.snd =
      actualMarkedTraceLaw (suppressedNetwork N hcut b hb hp)
        (youngestPhaseRates N hcut b hb hp r) n t duration := by
  unfold pairedEpochLaw actualMarkedTraceLaw
  rw [Measure.map_map measurable_snd (paired_epoch_records_measurable N hcut b hb hp _ _ _ _ _)]
  change (currentPairClockMeasure N r s).map
    (literalMarkedTrace (suppressedNetwork N hcut b hb hp) n duration t ∘
      reindexClocks N hcut b hb hp s t h) = _
  rw [← Measure.map_map
    (marked_trace_measurable (suppressedNetwork N hcut b hb hp) n t duration)
    (reindexClocks N hcut b hb hp s t h).measurable]
  rw [show (currentPairClockMeasure N r s).map (reindexClocks N hcut b hb hp s t h) =
      currentPairClockMeasure (suppressedNetwork N hcut b hb hp)
        (youngestPhaseRates N hcut b hb hp r) t from
      actual_joint_clock_product N hcut b hb hp r s t h]

theorem paired_epoch_records_related {sample : Copy → X} (n : Nat) (duration : ℝ)
    (s : Code N sample) (t : Code (suppressedNetwork N hcut b hb hp) sample)
    (h : Related N hcut b hb hp s t) (c : Choice N s → ℝ) :
    TraceRelated N hcut b hb hp n (pairedEpochRecords N hcut b hb hp n duration s t h c).1
      (pairedEpochRecords N hcut b hb hp n duration s t h c).2 :=
  literal_trace_phase_relation N hcut b hb hp n duration s t h c

#print axioms merger_copy_location
#print axioms merger_epoch_compatible
#print axioms paired_step_related
#print axioms destination_choice_square
#print axioms destination_residual_square
#print axioms destination_residual_reindex
#print axioms selected_winner_equiv
#print axioms literal_trace_phase_relation
#print axioms paired_epoch_records_measurable
#print axioms paired_epoch_probability
#print axioms paired_epoch_original_marginal
#print axioms paired_epoch_constructed_marginal
#print axioms paired_epoch_records_related

end UnifiedLean.G6.MergerPhaseSquare
