# Literal partial-exit separator: next uncompiled proof target

SOURCE_ONLY_UNCOMPILED_NOT_KERNEL_ACCEPTED. Author: lean_integration_successor, 2026-10-11. This is one new full UTF-8 note in the counted WF metadata. The four frozen draft files are unchanged. No Lean parser, elaborator, compiler, executable import, staging, cache, observer, native process or Git/index operation was used. Scripts below are a proof skeleton requiring future independent review/elaboration, not an accepted theorem. No new probability or routing engine is proposed.

## What this closes conditionally

Set es=originalExits N C (C.age v) and k=max(es.idxOf ei)(es.idxOf ej)+1, exactly as in frozen draft09f8. Assume ei≠ej and an admitted original Code s whose selected left/right copies occupy original edges ei/ej. For each n<k, both children cannot have appeared in es.take n. A foreign exit leaves both unchanged. A child exit puts that cohort at node(source child); the other remains on its original edge until its own literal occurrence. Edge/node constructors differ, so the selected cohorts remain separated. The terminal state n=k may already be co-located at v.

This repairs the precise gap identified by critique b123: after the earlier child exit, node v is NOT BelowMeeting. Do not use the strict-age separator on that state. Use the later child's non-hit witness instead. In this exit-only segment there are no intervals, node entries or hybrid draws, so existing deterministic exitCodeList is sufficient. Current-root mergers that occurred earlier remain in s; all original-copy fibres are handled by actual_exit_list_copy_location.

The resulting target is stronger than a statement only for n<k: it gives SupportedSeparatedPrefixes of the actual finite exit segment and hence its existing SeparatedAgenda. Combined with an already proved pre-boundary agenda and actual pre-boundary child-edge support, it gives the literal P agenda. It does NOT derive either of those pre-boundary hypotheses from calibration.

## Next-lemma statement and proof skeleton

The block is a future draft extension referring to names in the separate, still-uncompiled G4LiteralLastChildExitCut draft. It is not a currently resolved/imported module. Existing namespace/type references are pinned below.

```lean
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
  obtain rfl := PMF.mem_support_pure_iff.mp hd
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
```

## Nodup, cut semantics and exact premises

The accepted originalExits definition is Finset.toList, so its Nodup witness is Finset.nodup_toList. No new Nodup assumption on a desired program is needed. It ensures each named child has one literal occurrence. The proof of not_both_child_hits itself is stronger and does not need Nodup: idxOf is the first occurrence, and membership in take n implies that first index is below n even in a repeated list. This removes a superfluous dependency without changing the actual tied phase.

The partial-exit separator also does not need source(ei)=source(ej)=v: whenever one child is still an edge and the other has become any node, constructors differ. For interpreting k as the later of two actual meeting-child exits, reuse frozen child_mem_exits / last_child_cut_members / last_child_cut_le_length with both original-source equations and ei≠ej. At terminal k reuse frozen last_child_exit_colocates, with source equations and supplied child inputs. No endpoint separation is promised. Full genealogy/register data stays governed by the existing actual_exit_list_genealogy/register results; the separator proof only reads locations.

The physical beforeBoundary and calibration obligations are now isolated: (1) prove hbefore for ALL actual reachable original states of the strict pre-boundary word; (2) prove hchild at its terminal support, starting from actual initialCode with actual sample/register/modes; (3) derive actual original opposite-child geometry from the admitted paired natural COMMON calibration. Use SourceValid.original_descendant, strict timing/epoch bounds and route dominance, as recorded in the frozen prior note. Existing BeforeReady's non-strict node bound alone does not give these inputs. Do not assume arbitrary Old-conditioned independence, no-merger histories, or fixed selectors to discharge all support.

Given these inputs, the append theorem supplies literal-prefix SeparatedAgenda and the already accepted actual_separated_joint_program_law supplies its fixed-Code conditional product. A natural erased product still separately requires actual natural initializer/private-bank/no-read/same-erased-input binding. No scalar OriginalSpan coercion, desired-law admission, native readout refinement or master closure follows.

## Immutable provider and input pins

The following rows bind actual bytes that were read as text. Provider source bodies are at the accepted1504 source-store path plus their SHA256 and .lean suffix. Declaration names were checked against those exact bodies; listing them is not fresh kernel admission. Core list files were read only, never imported/executed. There are no new compiler objects or resource-policy changes.

```json
{"status":"SOURCE_ONLY_UNCOMPILED_NOT_KERNEL_ACCEPTED","created_utc":"2026-10-11T04:17:46.799996+00:00","prior_draft_root":"/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z/metadata/g4-literal-last-child-exit-bridge-draft-20261011T040345.699402Z","prior_four_files_sha256":{"FILE-INVENTORY.json":"7eaf05061b6121341e91f06880f445eb3847e6748c0a6ee194ca71e359c8ad7c","SOURCE-ONLY-FREEZE.json":"7e5b077daf86bc9e2c542cb1c7113bb6e102d6509cd284fd46d1fc9069879647","BRIDGE-API-AND-PROOF-OBLIGATIONS.md":"53700cc8249e636939620eed071f68550618bf38594be1922dfc0a1c360e139c","G4LiteralLastChildExitCut.lean":"09f8eda714d7182675e582ca31266de98c6fcf6de303c70e9a760373241278b7"},"critique":{"path":"/dev/shm/rc-lean-g6-forest-register-20261011T004522.928832Z/metadata/G4-LITERAL-LAST-CHILD-EXIT-INDEPENDENT-CRITIQUE-20261011T0410Z.json","sha256":"b1233c39f0000e964bdcfbcacbb88ba527082677bf675b3b3c6c10dd477ed0ee"},"accepted_graph_sha256":"e05a87db2b34f42aada87a958f7ff9114c68a817458b5919f7ecac62386fbacd","provider_source_store":"/dev/shm/rc-lean-g7-survival-integration-20261010T223510.923050Z/source-store","accepted_provider_pins":[{"module":"G1OriginalExitBatchBinding","sha256":"d1e84e70b0f2ce7cf16e89fd640debf580fd504b3670ff5e53f3bef95481bbb7","bytes":5926,"declarations":["exitLocationList","actual_exit_list_program","actual_exit_list_copy_location","actual_exit_location_list_hit","actual_exit_list_genealogy","actual_exit_list_register"]},{"module":"UnifiedLean.Source.SourceBoundaryKernels","sha256":"994b25e798e39889a56084b267c3e896580cd21e902764c3c6922d9bfdd6070d","bytes":8870,"declarations":["exitLocation"]},{"module":"G1OriginalCalendarDecomposition","sha256":"5fafa3802a1cb9ba286b64c2e69b1d0e42cfeddb6b83fc5be4c9304c1736daae","bytes":8062,"declarations":["originalExits"]},{"module":"G1SeparatedAgendaSupportCuts","sha256":"19ee680f2b2ee5ffbdbd956b180825abe4687ada80f641e307015961f4d6a8be","bytes":2556,"declarations":["actual_separated_agenda_append_iff"]},{"module":"G1ActualJointProgram","sha256":"8d8b5177193a6e80241d1d8435bc2461221191965d8f7f285634b9fe180f2cc7","bytes":5308,"declarations":["SeparatedAgenda","actual_separated_joint_program_law"]},{"module":"UnifiedLean.Source.SourceProgramTransport","sha256":"d009fdfc510bfcaffaeea3bc241401eaf2996178ff4b82376eb22f1e49387831","bytes":4978,"declarations":["sourceProgram"]},{"module":"G1InitializedFrontierPrefix","sha256":"c7ce7cff89b7c4d7e2fd13d6d1fd22ab3303bbc89c2cf4f194f50d78284a37d5","bytes":12663,"declarations":["beforeBoundaryProgram"]}],"core_text_pins":[{"path":"/workspace/toolchains/lean-4.33.1-linux/src/lean/Init/Data/List/Find.lean","sha256":"46c8f9f09f6790204446656b8b8cbd62420e83d0da3c6ec727a9862cc19181aa","bytes":54821,"declarations":["idxOf_append","idxOf_lt_length_of_mem"]},{"path":"/workspace/toolchains/lean-4.33.1-linux/src/lean/Init/Data/List/TakeDrop.lean","sha256":"16c0418c733f7ef8f331cd6bf6848ca343bda50766494292e80c438755942ac5","bytes":17520,"declarations":["take_append_drop","map_take"]},{"path":"/workspace/toolchains/lean-4.33.1-linux/src/lean/Init/Data/List/Nat/TakeDrop.lean","sha256":"7e05a9cb5945ae0b0a3cc7d011fb897a6197c72ead3ce2388981c70d769c0ede","bytes":25003,"declarations":["length_take_le","take_take"]}],"validated":"Exact text hashes/name references, UTF-8, allocated budget and unchanged prior four bytes only. No Lean/parser/runtime/Git operation.","new_output_allocated_limit_bytes":16384}
```
