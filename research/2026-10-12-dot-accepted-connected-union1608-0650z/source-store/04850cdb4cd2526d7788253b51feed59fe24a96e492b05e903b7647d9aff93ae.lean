import G4LiteralLastChildExitCut

namespace G4PartialExitSeparationNextDraft
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceBoundaryKernels
open G1OriginalCalendarDecomposition G1InitializedFrontierPrefix
open G1OriginalExitBatchBinding G1ActualJointProgram G1JointSeparatedSourceGeometry
open G1SeparatedAgendaSupportCuts G4LiteralLastChildExitCutDraft
open scoped Classical
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

/-- New list bookkeeping; no Nodup assumption is needed for first occurrence. -/
lemma first_index_lt_of_mem_take {es : List E} {e : E} {n : Nat}
    (he : e ∈ es.take n) : es.idxOf e < n := by
  have hi := congrArg (fun xs : List E => xs.idxOf e) (List.take_append_drop n es)
  rw [List.idxOf_append, if_pos he] at hi
  calc
    es.idxOf e = (es.take n).idxOf e := hi.symm
    _ < (es.take n).length := List.idxOf_lt_length_of_mem he
    _ ≤ n := List.length_take_le n es

lemma not_both_child_hits {es : List E} {ei ej : E} {n : Nat}
    (hn : n < max (es.idxOf ei) (es.idxOf ej) + 1) :
    ¬ (ei ∈ es.take n ∧ ej ∈ es.take n) := by
  rintro ⟨hi, hj⟩
  have hm : max (es.idxOf ei) (es.idxOf ej) < n :=
    max_lt_iff.mpr ⟨first_index_lt_of_mem_take hi, first_index_lt_of_mem_take hj⟩
  exact (not_lt_of_ge (Nat.le_of_lt_succ hn)) hm

/-- Missing-name adapter only: unfold the existing deterministic location operation. -/
lemma exit_location_list_not_hit (N : RootedBinary V E X) (es : List E) (e : E)
    (he : e ∉ es) : exitLocationList N es (.edge e) = .edge e := by
  induction es with
  | nil => rfl
  | cons f fs ih =>
      have hef : e ≠ f := fun h => he (List.mem_cons.mpr (Or.inl h))
      have htail : e ∉ fs := fun h => he (List.mem_cons.mpr (Or.inr h))
      simpa [exitLocationList, exitLocation, hef] using ih htail

/-- Conditional deterministic separator, even for arbitrary earlier genealogy/register. -/
lemma separated_after_exit_list (N : RootedBinary V E X) {sample : Copy → X}
    (es : List E) (inside outside : Finset Copy) (ei ej : E) (s : Code N sample)
    (hne : ei ≠ ej)
    (hl : ∀ x ∈ inside, copyLocation (state s) x = .edge ei)
    (hr : ∀ y ∈ outside, copyLocation (state s) y = .edge ej)
    (hsafe : ei ∉ es ∨ ej ∉ es) :
    PopulationSeparated (state (exitCodeList N es s)) inside outside := by
  intro x hx y hy
  rw [actual_exit_list_copy_location N es s x,
    actual_exit_list_copy_location N es s y, hl x hx, hr y hy]
  rcases hsafe with hi | hj
  · rw [exit_location_list_not_hit N es ei hi]
    by_cases hj : ej ∈ es
    · rw [actual_exit_location_list_hit N es ej hj]
      intro h
      cases h
    · rw [exit_location_list_not_hit N es ej hj]
      exact fun h => hne (Location.edge.inj h)
  · rw [exit_location_list_not_hit N es ej hj]
    by_cases hi : ei ∈ es
    · rw [actual_exit_location_list_hit N es ei hi]
      intro h
      cases h
    · rw [exit_location_list_not_hit N es ei hi]
      exact fun h => hne (Location.edge.inj h)

/-- Main next target: every strict take-prefix support of the literal exit segment. -/
theorem supported_separated_partial_exits (N : RootedBinary V E X)
    (C : Calendar N.graph) {sample : Copy → X} (r : PositivePairRates E)
    (v : V) (ei ej : E) (inside outside : Finset Copy) (s : Code N sample)
    (hne : ei ≠ ej)
    (hl : ∀ x ∈ inside, copyLocation (state s) x = .edge ei)
    (hr : ∀ y ∈ outside, copyLocation (state s) y = .edge ej) :
    SupportedSeparatedPrefixes N r inside outside
      (((originalExits N C (C.age v)).take (lastChildCutLength N C v ei ej)).map
        (fun e => .boundary (.exit e))) s := by
  let es := originalExits N C (C.age v)
  let k := lastChildCutLength N C v ei ej
  intro n hn d hd
  have hlen : n < (es.take k).length := by
    simpa only [List.length_map] using hn
  have hnk : n < k := hlen.trans_le (List.length_take_le k es)
  have ht : ((es.take k).map (fun e =>
      (ProgramStep.boundary (.exit e) : ProgramStep N))).take n =
      (es.take n).map (fun e => .boundary (.exit e)) := by
    rw [← List.map_take, List.take_take, Nat.min_eq_left (le_of_lt hnk)]
  rw [ht, actual_exit_list_program] at hd
  obtain rfl := (PMF.mem_support_pure_iff _ _).mp hd
  have hb : ¬ (ei ∈ es.take n ∧ ej ∈ es.take n) :=
    not_both_child_hits (by simpa only [k, lastChildCutLength, es] using hnk)
  apply separated_after_exit_list N (es.take n) inside outside ei ej s hne hl hr
  by_cases hi : ei ∈ es.take n
  · exact Or.inr (fun hj => hb ⟨hi, hj⟩)
  · exact Or.inl hi

/-- The physical pre-boundary inputs remain visible rather than being inferred. -/
theorem literal_agenda_of_before_boundary_inputs (N : RootedBinary V E X)
    (C : Calendar N.graph) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (v : V) (ei ej : E)
    (inside outside : Finset Copy) (s : Code N sample) (hne : ei ≠ ej)
    (hbefore : SeparatedAgenda N r inside outside
      (beforeBoundaryProgram N C H gamma common (C.age v)) s)
    (hchild : ∀ d ∈ (sourceProgram N r
      (beforeBoundaryProgram N C H gamma common (C.age v)) s).support,
      (∀ x ∈ inside, copyLocation (state d) x = .edge ei) ∧
      (∀ y ∈ outside, copyLocation (state d) y = .edge ej)) :
    SeparatedAgenda N r inside outside
      (literalPrefix N C H gamma common v ei ej) s := by
  unfold literalPrefix
  apply (actual_separated_agenda_append_iff N r inside outside _ _ s).mpr
  refine ⟨hbefore, ?_⟩
  intro d hd
  have hc := hchild d hd
  exact agenda_of_supported_prefixes N r inside outside _ d
    (supported_separated_partial_exits N C r v ei ej inside outside d hne hc.1 hc.2)
end G4PartialExitSeparationNextDraft
