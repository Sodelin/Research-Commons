import G1OriginalCurrentRootReconstruction

/-!
# Actual original nonroot bigon fragment and its one-population exit

Contributor: dot, 2026-10-03. Each fragment names an original hybrid and its
two distinct parallel original parent arcs with a common nonroot upper node.
Its positive duration is derived from the original calendar. Natural routing
is one draw per CURRENT ancestor or the SAME original common register.
The output population is derived on the whole actual source-law support.
No desired population law, forest kernel, or output equality is a source field.
Canonical admitted-class blob extraction and whole-core erasure remain separate.
-/
namespace G1NonrootBigonKernel
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.SourceForest GProgram.G5
open GProgram.SourceForestKingmanPopulationProjection
open G1OpaqueSourceGrafting G1ContextualForestReplacement G1OriginalCurrentRootReconstruction
open UnifiedLean.Source.FiniteSourceSnapshot
open UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep
open UnifiedLean.Source.SourceBoundaryKernels
open UnifiedLean.Source.SourcePoissonKernel
open UnifiedLean.Source.SourceProgramTransport
open scoped Classical NNReal
variable {V E X Copy : Type*}
variable [DecidableEq V] [DecidableEq E] [Fintype V] [Fintype E] [Fintype X]
variable [DecidableEq Copy] [Fintype Copy]

/-- Original graph data of one nonroot parallel bigon, not a kernel field. -/
structure NonrootBigon (N : RootedBinary V E X) where
  parents : GProgram.G2.OriginalHybridParents N
  upper : V
  upper_nonroot : upper ≠ N.root
  arm_sources : ∀ b, N.graph.source (parents.parent b) = upper

noncomputable def bigonDuration (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : NonrootBigon N) : ℝ≥0 := Real.toNNReal (C.age B.upper - C.age B.parents.hybrid)

omit [DecidableEq E] in
theorem actual_bigon_duration_positive (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : NonrootBigon N) : 0 < bigonDuration N C B := by
  have h := C.edge_older B.parents.parent0
  rw [B.parents.target0,show N.graph.source B.parents.parent0 = B.upper from B.arm_sources false] at h
  exact Real.toNNReal_pos.mpr (sub_pos.mpr h)

noncomputable def bigonPulse (N : RootedBinary V E X) (B : NonrootBigon N)
    (gamma : unitInterval) (common : Bool) : BoundaryOperation N :=
  if common then .common B.parents else .independent B.parents gamma

noncomputable def bigonProgram (N : RootedBinary V E X) (C : Calendar N.graph)
    (B : NonrootBigon N) (gamma : unitInterval) (common : Bool) : List (ProgramStep N) :=
  [.boundary (bigonPulse N B gamma common),.interval (bigonDuration N C B),
    .boundary (.exit B.parents.parent0),.boundary (.exit B.parents.parent1)]

lemma actual_step_copy_population (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (p : Option (Choice N s)) (x : Copy) :
    copyLocation (state (stepDestination N s p)) x = copyLocation (state s) x := by
  cases p with
  | none => rfl
  | some p =>
      have hm := population_pair_is_source_legal (state s) (originalPlace N p.1)
        (originalPlace_not_node N p.1) p.2.property
      rw [show copyLocation (state (stepDestination N s (some p))) x =
          copyLocation (merge (state s) p.2.val.1 p.2.val.2) x from
        decode_encode_copyLocation N.root _ (merge_source_valid N sample _ s.property hm).forest x]
      exact merge_population_preserved _ hm x

lemma actual_iteration_copy_population (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (n : Nat) (s : Code N sample) {d : Code N sample}
    (hd : d ∈ (sourceIteration N r n s).support) (x : Copy) :
    copyLocation (state d) x = copyLocation (state s) x := by
  induction n generalizing s with
  | zero =>
      have he : d = s := by simpa only [sourceIteration,PMF.mem_support_pure_iff] using hd
      rw [he]
  | succ n ih =>
      obtain ⟨z,hz,hdz⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
      obtain ⟨p,_,hp⟩ := (PMF.mem_support_map_iff _ _ _).mp hz
      exact (ih z hdz).trans (hp ▸ actual_step_copy_population N s p x)

lemma actual_time_copy_population (N : RootedBinary V E X) {sample : Copy → X}
    (r : PositivePairRates E) (t : ℝ≥0) (s : Code N sample) {d : Code N sample}
    (hd : d ∈ (sourceTimeKernel N r t s).support) (x : Copy) :
    copyLocation (state d) x = copyLocation (state s) x := by
  obtain ⟨n,_,hdn⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact actual_iteration_copy_population N r n s hdn x

lemma actual_exit_copy_population (N : RootedBinary V E X) {sample : Copy → X}
    (s : Code N sample) (e : E) (x : Copy) :
    copyLocation (state (exitCode N s e)) x =
      if copyLocation (state s) x = .edge e then .node (N.graph.source e) else copyLocation (state s) x := by
  rw [show copyLocation (state (exitCode N s e)) x = copyLocation (exitEdge N (state s) e) x from
    decode_encode_copyLocation N.root _ (exitEdge_source_valid N sample _ s.property e).forest x]
  rfl

lemma actual_pulse_copy_population (N : RootedBinary V E X) {sample : Copy → X}
    (H : GProgram.G2.OriginalHybridParents N) (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node H.hybrid)
    (coin : AtNode (state s) H.hybrid → Bool) (x : Copy) :
    ∃ b, copyLocation (state (pulseCode H s coin)) x = .edge (H.parent b) := by
  have hx : (state s).ancestor x ∈ (state s).live ∧
      (state s).location ((state s).ancestor x) = .node H.hybrid :=
    ⟨s.property.forest.ancestor_live x,hinput _ (s.property.forest.ancestor_live x)⟩
  refine ⟨coin ⟨(state s).ancestor x,hx⟩,?_⟩
  rw [show copyLocation (state (pulseCode H s coin)) x = copyLocation (pulse H (state s) coin) x from
    decode_encode_copyLocation N.root _ (pulse_source_valid H sample _ s.property coin).forest x]
  exact pulse_routes_current_ancestor H (state s) coin ⟨(state s).ancestor x,hx⟩

lemma actual_bigon_pulse_on_arms (N : RootedBinary V E X) {sample : Copy → X}
    (B : NonrootBigon N) (gamma : unitInterval) (common : Bool) (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node B.parents.hybrid)
    {d : Code N sample} (hd : d ∈ (boundaryKernel N (bigonPulse N B gamma common) s).support)
    (x : Copy) : ∃ b, copyLocation (state d) x = .edge (B.parents.parent b) := by
  cases common with
  | false =>
      obtain ⟨coin,_,hc⟩ := (PMF.mem_support_map_iff _ _ _).mp hd
      rw [← hc]
      exact actual_pulse_copy_population N B.parents s hinput coin x
  | true =>
      have he : d = pulseCode B.parents s (fun _ => (state s).register B.parents.hybrid) := by
        simpa only [bigonPulse,ite_true,boundaryKernel,PMF.mem_support_pure_iff] using hd
      subst d
      exact actual_pulse_copy_population N B.parents s hinput _ x

lemma actual_bigon_two_exits (N : RootedBinary V E X) {sample : Copy → X}
    (B : NonrootBigon N) (s : Code N sample) (x : Copy)
    (harms : ∃ b, copyLocation (state s) x = .edge (B.parents.parent b)) :
    copyLocation (state (exitCode N (exitCode N s B.parents.parent0) B.parents.parent1)) x = .node B.upper := by
  obtain ⟨b,hb⟩ := harms
  rw [actual_exit_copy_population,actual_exit_copy_population]
  cases b with
  | false =>
      rw [show copyLocation (state s) x = .edge B.parents.parent0 from hb,
        if_pos rfl,show N.graph.source B.parents.parent0 = B.upper from B.arm_sources false]
      rfl
  | true =>
      rw [show copyLocation (state s) x = .edge B.parents.parent1 from hb]
      have hne : (Location.edge B.parents.parent1 : Location V E) ≠ .edge B.parents.parent0 := by
        intro h
        exact B.parents.different (Location.edge.inj h).symm
      rw [if_neg hne,if_pos rfl,show N.graph.source B.parents.parent1 = B.upper from B.arm_sources true]

theorem actual_bigon_program_kernel (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E) (B : NonrootBigon N)
    (gamma : unitInterval) (common : Bool) (s : Code N sample) :
    sourceProgram N r (bigonProgram N C B gamma common) s =
      (boundaryKernel N (bigonPulse N B gamma common) s).bind
        (fun p => (sourceTimeKernel N r (bigonDuration N C B) p).map
          (fun d => exitCode N (exitCode N d B.parents.parent0) B.parents.parent1)) := by
  simp only [bigonProgram,sourceProgram,sourceProgramStep,boundaryKernel,PMF.pure_bind]
  rfl

/-- Both source modes, every already-formed input forest, and every actual
output realization reach the ONE original rootward interface population.
This exit-population fact is derived, rather than supplied as a desired law. -/
theorem actual_nonroot_bigon_exit_population (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E) (B : NonrootBigon N)
    (gamma : unitInterval) (common : Bool) (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node B.parents.hybrid)
    {d : Code N sample} (hd : d ∈ (sourceProgram N r (bigonProgram N C B gamma common) s).support)
    (l : Copy) (hl : l ∈ (state d).live) : (state d).location l = .node B.upper := by
  rw [actual_bigon_program_kernel] at hd
  obtain ⟨p,hp,hdp⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  obtain ⟨z,hz,hzd⟩ := (PMF.mem_support_map_iff _ _ _).mp hdp
  have hpop := actual_time_copy_population N r (bigonDuration N C B) p hz l
  have harms := actual_bigon_pulse_on_arms N B gamma common s hinput hp l
  have houtput := actual_bigon_two_exits N B z l (hpop.symm ▸ harms)
  rw [hzd] at houtput
  have hrep : (state d).ancestor l = l := d.property.forest.representative l hl
  simpa only [copyLocation,hrep] using houtput

/-- The compressed label is extracted from an actual original component
program on the smaller CURRENT-root source. Its provenance remains the
original graph, calendar, rates, parent IDs, natural mode and retained register. -/
noncomputable def bigonCurrentKernel (N : RootedBinary V E X) {sample : Copy → X}
    (C : Calendar N.graph) (r : PositivePairRates E) (B : NonrootBigon N)
    (gamma : unitInterval) (common : Bool) (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node B.parents.hybrid) :=
  smallerCurrentRootKernel N r (bigonProgram N C B gamma common) s (.node B.parents.hybrid) hinput

theorem actual_nonroot_bigon_contextual_replacement
    (N : RootedBinary V E X) {sample : Copy → X} {History Obs : Type*}
    (C : Calendar N.graph) (r : PositivePairRates E) (B : NonrootBigon N)
    (gamma : unitInterval) (common : Bool) (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node B.parents.hybrid)
    (history : History)
    (exterior : History × (V → Bool) × Finset
      (UnifiedLean.Source.UnrankedGenealogyObservation.UnrankedTree Copy) → PMF Obs) :
    (sourceProgram N r (bigonProgram N C B gamma common) s).bind
      (fun d => exterior (history,(state d).register,rootForest N d)) =
    (bigonCurrentKernel N C r B gamma common s hinput).bind
      (fun F => exterior (history,(state s).register,
        F.image (graftUnranked (fun l => (state s).genealogy l.val)))) :=
  actual_original_contextual_forest_replacement N r (bigonProgram N C B gamma common)
    s (.node B.parents.hybrid) hinput history exterior

/-- The local accepted G1 kernel/opaque-graft/current-root/shared-register/
root-history contract, with the original rootward output population DERIVED.
Only current entering roots are capped; original descendant labels are not.
Interior gamma gives the admitted natural contract, and the law also happens
to remain valid at endpoints without declaring them positive natural sources. -/
theorem actual_cap_m_nonroot_bigon_g1
    (N : RootedBinary V E X) {sample : Copy → X} {History Obs : Type*}
    (C : Calendar N.graph) (r : PositivePairRates E) (B : NonrootBigon N)
    (gamma : unitInterval) (common : Bool) (s : Code N sample)
    (hinput : ∀ l ∈ (state s).live, (state s).location l = .node B.parents.hybrid)
    (m : Nat) (cap : (state s).live.card ≤ m) (history : History)
    (exterior : History × (V → Bool) × Finset
      (UnifiedLean.Source.UnrankedGenealogyObservation.UnrankedTree Copy) → PMF Obs) :
    0 < bigonDuration N C B ∧
    Fintype.card (UnifiedLean.Source.SourceCopyCarrierTransport.SelectedCopy (state s).live) ≤ m ∧
    (∀ d ∈ (sourceProgram N r (bigonProgram N C B gamma common) s).support,
      ∀ l ∈ (state d).live, (state d).location l = .node B.upper) ∧
    ((sourceProgram N r (bigonProgram N C B gamma common) s).bind
      (fun d => exterior (history,(state d).register,rootForest N d)) =
      (bigonCurrentKernel N C r B gamma common s hinput).bind
        (fun F => exterior (history,(state s).register,
          F.image (graftUnranked (fun l => (state s).genealogy l.val))))) := by
  refine ⟨actual_bigon_duration_positive N C B,actual_kernel_carrier_cap N s m cap,?_,?_⟩
  · intro d hd l hl
    exact actual_nonroot_bigon_exit_population N C r B gamma common s hinput hd l hl
  · exact actual_nonroot_bigon_contextual_replacement N C r B gamma common s hinput history exterior

end G1NonrootBigonKernel
