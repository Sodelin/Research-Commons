import G1CompactComponentBlockRows

/-! Full canonical original component equals its registry-aligned compact
three-epoch source word at the complete inside selected interface.
Contributor: dot, 2026-10-03. -/
namespace G1CanonicalCompactComponentRow
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceFiniteProjection
open G1OriginalNodeBatchBinding G1CanonicalEpochSpecialization G1OriginalComponentNodeIdentity
open G1CanonicalEpochBlockBinding G1CanonicalThreeEpochList G1CanonicalComponentSegment
open G1ExtractedComponentProgram G1NonrootBigonKernel G1OriginalRegistryBigon
open G1CutChildPorts G1ActualTwoPortBlob G1BigonFootprint G1OriginalCalendarDecomposition
open G1CompactComponentBlockRows G1CompactSourceComposition G1ActualJointProgram
open G1SameOriginalExteriorContinuation
open scoped Classical NNReal
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

theorem actual_canonical_compact_component_row (N : RootedBinary V E X) (hc : CutChild N)
    (C : Calendar N.graph) (b : N.graph.Blob) (A : ActualBlobBigon N b) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    {sample : Copy → X} (r : PositivePairRates E) (keep : Finset Copy)
    (s : Code N sample) (hs : AtNodePanel (state s) keep (N.graph.target A.child)) :
    let B := registryAlignedBigon N hc b A H
    (sourceProgram N r (componentAgenda N C b B H gamma common) s).map (projection N keep) =
      (sourceProgram N r (componentProgram N hc C b B
        (gamma (originalHybrid N b B)) (common (originalHybrid N b B))) s).map (projection N keep) := by
  dsimp only
  let B := registryAlignedBigon N hc b A H
  let cb := canonicalEpochBlock N C H gamma common (N.graph.target B.child) B.fragment.parents.hybrid
    (originalExits N C (C.age B.fragment.parents.hybrid))
  let ab := canonicalEpochBlock N C H gamma common B.fragment.parents.hybrid B.fragment.upper
    (originalExits N C (C.age B.fragment.upper))
  let eb := canonicalEpochBlock N C H gamma common B.fragment.upper (N.graph.source B.entry)
    (exitsBeforeEntry N C b B ++ [B.entry])
  let cw := edgeProgram N C B.child (extracted_child_ordinary N b B)
  let aw := bigonProgram N C B.fragment (gamma (originalHybrid N b B)) (common (originalHybrid N b B))
  let ew := edgeProgram N C B.entry (extracted_entry_ordinary N hc b B)
  have hcdeg := extracted_child_ordinary N b B
  have hcin := actual_single_incoming_edges N B.child hcdeg
  have hcsource : ∀ e ∈ incomingEdges N (N.graph.target B.child), N.graph.source e = B.fragment.parents.hybrid := by
    intro e he
    have heq : e = B.child := by simpa only [hcin,Finset.mem_singleton] using he
    subst e; exact B.child_source
  have hcdate : C.age (N.graph.target B.child) < C.age B.fragment.parents.hybrid := by
    simpa only [B.child_source] using C.edge_older B.child
  have hccanonical : ∀ e ∈ incomingEdges N (N.graph.target B.child), e ∈ [B.child] := by
    intro e he; simpa only [hcin,Finset.mem_singleton,List.mem_singleton] using he
  have hchit : B.child ∈ originalExits N C (C.age B.fragment.parents.hybrid) :=
    Finset.mem_toList.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,congrArg C.age B.child_source⟩)
  have hcrow (z : Code N sample) (hz : AtNodePanel (state z) keep (N.graph.target B.child)) :
      (sourceProgram N r cb z).map (projection N keep) = (sourceProgram N r cw z).map (projection N keep) := by
    simpa only [cb,cw,B.child_source] using actual_canonical_ordinary_block_row N C H gamma common r keep
      B.child hcdeg _ hchit z hz
  have hcout (z : Code N sample) (hz : AtNodePanel (state z) keep (N.graph.target B.child))
      {d : Code N sample} (hd : d ∈ (sourceProgram N r cb z).support) :
      AtNodePanel (state d) keep B.fragment.parents.hybrid :=
    actual_canonical_epoch_block_exit_support N C H gamma common r keep _ _ (N.edge_target_ne_root B.child)
      hcdate hcsource _ [B.child] (actual_original_exits_cover N C _ _ hcsource) hccanonical z hz hd
  have hain := actual_bigon_incoming_edges N b B
  have hasource : ∀ e ∈ incomingEdges N B.fragment.parents.hybrid, N.graph.source e = B.fragment.upper := by
    intro e he
    rcases (by simpa only [hain,Finset.mem_insert,Finset.mem_singleton] using he :
      e = B.fragment.parents.parent0 ∨ e = B.fragment.parents.parent1) with rfl | rfl
    · exact B.fragment.arm_sources false
    · exact B.fragment.arm_sources true
  have hacanonical : ∀ e ∈ incomingEdges N B.fragment.parents.hybrid,
      e ∈ [B.fragment.parents.parent0,B.fragment.parents.parent1] := by
    intro e he
    simpa only [hain,Finset.mem_insert,Finset.mem_singleton,List.mem_cons,List.mem_singleton,List.not_mem_nil,or_false] using he
  have hadate : C.age B.fragment.parents.hybrid < C.age B.fragment.upper := by
    simpa only [B.fragment.parents.target0,
      show N.graph.source B.fragment.parents.parent0 = B.fragment.upper from B.fragment.arm_sources false]
      using C.edge_older B.fragment.parents.parent0
  have haroot : B.fragment.parents.hybrid ≠ N.root := by
    rw [← B.fragment.parents.target0]; exact N.edge_target_ne_root _
  have harow (z : Code N sample) (hz : AtNodePanel (state z) keep B.fragment.parents.hybrid) :
      (sourceProgram N r ab z).map (projection N keep) = (sourceProgram N r aw z).map (projection N keep) :=
    actual_canonical_aligned_bigon_block_row N hc C b A H gamma common r keep z hz
  have haout (z : Code N sample) (hz : AtNodePanel (state z) keep B.fragment.parents.hybrid)
      {d : Code N sample} (hd : d ∈ (sourceProgram N r ab z).support) : AtNodePanel (state d) keep B.fragment.upper :=
    actual_canonical_epoch_block_exit_support N C H gamma common r keep _ _ haroot hadate hasource _ _
      (actual_original_exits_cover N C _ _ hasource) hacanonical z hz hd
  have herow (z : Code N sample) (hz : AtNodePanel (state z) keep B.fragment.upper) :
      (sourceProgram N r eb z).map (projection N keep) = (sourceProgram N r ew z).map (projection N keep) := by
    have hh := actual_canonical_ordinary_block_row N C H gamma common r keep
      B.entry (extracted_entry_ordinary N hc b B) (exitsBeforeEntry N C b B ++ [B.entry]) (by simp) z
      (by simpa only [B.entry_target] using hz)
    simpa only [eb,ew,B.entry_target] using hh
  have htail (z : Code N sample) (hz : AtNodePanel (state z) keep B.fragment.parents.hybrid) :
      (sourceProgram N r (ab ++ eb) z).map (projection N keep) =
        (sourceProgram N r (aw ++ ew) z).map (projection N keep) := by
    calc
      _ = (sourceProgram N r (ab ++ ew) z).map (projection N keep) := by
        rw [actual_source_program_append,actual_source_program_append,PMF.map_bind,PMF.map_bind]
        apply bind_eq_of_eq_on_support
        intro d hd
        exact herow d (haout z hz hd)
      _ = _ := actual_source_row_suffix_congr N r keep ab aw ew z (harow z hz)
  have hlist : componentAgenda N C b B H gamma common = cb ++ ab ++ eb := by
    have hh := actual_component_agenda_three_epochs N C b B H gamma common
    simpa only [cb,ab,eb,canonicalEpochBlock,List.append_assoc] using hh
  rw [hlist]
  change (sourceProgram N r ((cb ++ ab) ++ eb) s).map (projection N keep) =
    (sourceProgram N r (cw ++ (aw ++ ew)) s).map (projection N keep)
  rw [List.append_assoc]
  calc
    _ = (sourceProgram N r (cb ++ (aw ++ ew)) s).map (projection N keep) := by
      rw [actual_source_program_append,actual_source_program_append,PMF.map_bind,PMF.map_bind]
      apply bind_eq_of_eq_on_support
      intro d hd
      exact htail d (hcout s hs hd)
    _ = _ := actual_source_row_suffix_congr N r keep cb cw (aw ++ ew) s (hcrow s hs)

end G1CanonicalCompactComponentRow
