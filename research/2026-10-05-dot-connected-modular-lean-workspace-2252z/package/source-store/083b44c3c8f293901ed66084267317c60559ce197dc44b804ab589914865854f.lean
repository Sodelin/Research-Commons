import G1OriginalEpochPanelSilence

/-! Canonical original epoch compression with DERIVED silence/partition.
Contributor: dot, 2026-10-03. Allows all current roots on either original
parallel arm. The actual exterior continues processing every original date;
only the complete inside selected-view readout is recomposed. -/
namespace G1OriginalEpochPanelCompression
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourcePoissonKernel UnifiedLean.Source.SourceFiniteProjection
open G1InitializedFrontierPrefix G1ActualJointProgram G1OriginalEpochPanelSilence
open G1ExteriorBoundarySilence G1InterleavedEpochCompression G1OriginalEpochRecomposition
open scoped Classical NNReal
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

def EdgeSafeStep (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (edges : Finset E)
    (op : ProgramStep N) : Prop :=
  (∃ t : ℝ≥0, op = .interval t) ∨ (∃ e : E, e ∉ edges ∧ op = .boundary (.exit e)) ∨
    (∃ v : V, op = .boundary (originalNodeOperation N H gamma common v))

lemma actual_edge_safe_step_support (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) {sample : Copy → X}
    (r : PositivePairRates E) (op : ProgramStep N) (edges : Finset E)
    (hsafe : EdgeSafeStep N H gamma common edges op) (s : Code N sample) (keep : Finset Copy)
    (hs : AtEdgePanel (state s) keep edges) {d : Code N sample}
    (hd : d ∈ (sourceProgramStep N r op s).support) : AtEdgePanel (state d) keep edges := by
  rcases hsafe with ⟨t,rfl⟩ | ⟨e,he,rfl⟩ | ⟨v,rfl⟩
  · exact actual_time_edge_panel N r t s keep edges hs hd
  · exact actual_other_exit_preserves_edge_panel N s keep edges e he hs hd
  · exact actual_node_preserves_edge_panel N H gamma common v s keep edges hs hd

/-- SilentExteriorAgenda follows from original syntax and actual population
support, rather than being supplied as a desired source-law hypothesis. -/
theorem actual_edge_safe_agenda_silent (N : RootedBinary V E X) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) {sample : Copy → X}
    (r : PositivePairRates E) (ops : List (ProgramStep N)) (edges : Finset E)
    (hsafe : ∀ op ∈ ops, EdgeSafeStep N H gamma common edges op) (s : Code N sample) (keep : Finset Copy)
    (hs : AtEdgePanel (state s) keep edges) : SilentExteriorAgenda N r keep ops s := by
  induction ops generalizing s with
  | nil => trivial
  | cons op ops ih =>
      have ht := fun p hp => hsafe p (List.mem_cons_of_mem op hp)
      rcases hsafe op (by simp) with ⟨t,rfl⟩ | ⟨e,he,rfl⟩ | ⟨v,rfl⟩
      · intro d hd
        exact ih ht d (actual_time_edge_panel N r t s keep edges hs hd)
      · refine ⟨actual_other_exit_at_edge_absent N s keep edges e he hs,?_⟩
        intro d hd
        exact ih ht d (actual_other_exit_preserves_edge_panel N s keep edges e he hs hd)
      · refine ⟨actual_node_at_edge_absent N H gamma common v s keep edges hs,?_⟩
        intro d hd
        exact ih ht d (actual_node_preserves_edge_panel N H gamma common v s keep edges hs hd)

lemma actual_earlier_boundary_edge_safe (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (edges : Finset E) (b a : ℝ) (ha : a < b)
    (hend : ∀ e ∈ edges, C.age (N.graph.source e) = b) :
    ∀ op ∈ boundaryOperations N C H gamma common a, EdgeSafeStep N H gamma common edges op := by
  intro op hop
  rcases List.mem_append.mp hop with hiexit | hinode
  · obtain ⟨e,he,hop⟩ := List.mem_map.mp hiexit
    have he := (Finset.mem_filter.mp (Finset.mem_toList.mp he)).2
    have hnot : e ∉ edges := by
      intro hm
      have hx := hend e hm
      exact (ne_of_lt ha) (he.symm.trans hx)
    exact Or.inr (Or.inl ⟨e,hnot,hop.symm⟩)
  · obtain ⟨v,_,hop⟩ := List.mem_map.mp hinode
    exact Or.inr (Or.inr ⟨v,hop.symm⟩)

lemma actual_stop_tail_edge_safe (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (edges : Finset E) (b : ℝ) (hend : ∀ e ∈ edges, C.age (N.graph.source e) = b)
    (dates : List ℝ) (horder : dates.Pairwise (· < ·)) (hb : b ∈ dates) (a : ℝ) :
    ∀ op ∈ stopBeforeTail N C H gamma common b a dates, EdgeSafeStep N H gamma common edges op := by
  induction dates generalizing a with
  | nil => exact False.elim (List.not_mem_nil hb)
  | cons c cs ih =>
      have hp := List.pairwise_cons.mp horder
      intro op hop
      by_cases hc : c = b
      · have heq : op = .interval (Real.toNNReal (c-a)) := by simpa [stopBeforeTail,hc] using hop
        exact Or.inl ⟨_,heq⟩
      · have hm : b ∈ cs := (List.mem_cons.mp hb).resolve_left (Ne.symm hc)
        have hop : op = .interval (Real.toNNReal (c-a)) ∨
            op ∈ boundaryOperations N C H gamma common c ++ stopBeforeTail N C H gamma common b c cs := by
          simpa [stopBeforeTail,hc] using hop
        rcases hop with heq | hop
        · exact Or.inl ⟨_,heq⟩
        · rcases List.mem_append.mp hop with hboundary | htail
          · exact actual_earlier_boundary_edge_safe N C H gamma common edges b c (hp.1 _ hm) hend op hboundary
          · exact ih hp.2 hm c op htail

lemma interval_durations_append (N : RootedBinary V E X) (xs ys : List (ProgramStep N)) :
    originalIntervalDurations N (xs ++ ys) = originalIntervalDurations N xs ++ originalIntervalDurations N ys := by
  induction xs with
  | nil => rfl
  | cons op ops ih => cases op <;> simp [originalIntervalDurations,ih]

lemma boundary_list_no_intervals (N : RootedBinary V E X) {A : Type*}
    (f : A → BoundaryOperation N) (xs : List A) :
    originalIntervalDurations N (xs.map (fun x => .boundary (f x))) = [] := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [originalIntervalDurations] using ih

lemma actual_boundary_no_intervals (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool) (a : ℝ) :
    originalIntervalDurations N (boundaryOperations N C H gamma common a) = [] := by
  rw [boundaryOperations,interval_durations_append,boundary_list_no_intervals,boundary_list_no_intervals]
  rfl

/-- Actual original date ordering derives the epoch's original-duration
partition, including all unrelated calendar breaks. -/
theorem actual_stop_tail_duration_partition (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (dates : List ℝ) (horder : dates.Pairwise (· < ·)) (b : ℝ) (hb : b ∈ dates)
    (a : ℝ) (ha : ∀ c ∈ dates, a ≤ c) :
    OriginalDurationPartition a b (originalIntervalDurations N (stopBeforeTail N C H gamma common b a dates)) := by
  induction dates generalizing a with
  | nil => exact False.elim (List.not_mem_nil hb)
  | cons c cs ih =>
      have hp := List.pairwise_cons.mp horder
      by_cases hc : c = b
      · subst c
        simpa [stopBeforeTail,originalIntervalDurations] using (OriginalDurationPartition.whole (ha b (by simp)))
      · have hm : b ∈ cs := (List.mem_cons.mp hb).resolve_left (Ne.symm hc)
        have hpart := OriginalDurationPartition.split c (ha c (by simp)) (hp.1 _ hm).le
          (ih hp.2 hm c (fun d hd => (hp.1 d hd).le))
        simpa [stopBeforeTail,hc,originalIntervalDurations,interval_durations_append,actual_boundary_no_intervals] using hpart

/-- The actual interleaved source's WHOLE inside genealogy/population/SAME-Γ
law equals the original fixed-edge epoch. Both silence and the original
duration partition are DERIVED; there is no fitted scalar or kernel premise. -/
theorem actual_canonical_edge_panel_epoch_compression (N : RootedBinary V E X) (C : Calendar N.graph)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy) (edges : Finset E)
    (dates : List ℝ) (horder : dates.Pairwise (· < ·)) (b : ℝ) (hb : b ∈ dates)
    (hend : ∀ e ∈ edges, C.age (N.graph.source e) = b) (a : ℝ) (ha : ∀ c ∈ dates, a ≤ c)
    (s : Code N sample) (hs : AtEdgePanel (state s) keep edges) :
    (sourceProgram N r (stopBeforeTail N C H gamma common b a dates) s).map (projection N keep) =
      (sourceTimeKernel N r (Real.toNNReal (b-a)) s).map (projection N keep) := by
  exact actual_interleaved_original_date_partition N r keep _ s
    (actual_edge_safe_agenda_silent N H gamma common r _ edges
      (actual_stop_tail_edge_safe N C H gamma common edges b hend dates horder hb a) s keep hs)
    (actual_stop_tail_duration_partition N C H gamma common dates horder b hb a ha)

end G1OriginalEpochPanelCompression
