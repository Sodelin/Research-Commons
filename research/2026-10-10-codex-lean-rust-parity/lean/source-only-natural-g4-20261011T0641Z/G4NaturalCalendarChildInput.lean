import G4InitializedBeforeBoundaryPrefixes
import G5ActualProtectiveOccupancy
import G4PartialExitSeparation

/-! SOURCE-ONLY UNCOMPILED V2, lean_integration_successor, 2026-10-11.
This consumes the separately frozen literal-prefix BelowMeeting adapter rather
than duplicating the accepted stopped-date induction. All earlier drafts and
accepted providers remain unchanged. Pending-node/root exclusion, natural
child input, literal strict-prefix agenda and terminal co-location are derived
from actual original initialization and SUPPLIED graph meeting geometry.
Calibration-to-geometry/source admission and a natural Old/seed mixture remain
separate. No target/parser/compiler/native process has checked this source. -/
namespace G4NaturalCalendarChildInput
open Nanuq.Source GProgram.G5 GProgram.SourceForest
open UnifiedLean.Source.NativeParentRouting UnifiedLean.Source.NativePairClockLaw
open UnifiedLean.Source.UniformizedSourceStep UnifiedLean.Source.SourceProgramTransport
open UnifiedLean.Source.SourceCalendarCompiler UnifiedLean.Source.SourceCalendarCompatibility
open UnifiedLean.Source.SourceCalendarPhysicalSupport UnifiedLean.Source.SourceInitializedCalendar
open UnifiedLean.Source.SourceBoundaryKernels UnifiedLean.Source.FiniteSourceSnapshot
open G1InitializedFrontierPrefix G1OriginalExitBatchBinding
open GProgram.G5.ActualProtectiveOccupancy
open G4LiteralLastChildExitCutDraft G4PartialExitSeparationNextDraft
open G4InitializedBeforeBoundaryPrefixes
open scoped Classical NNReal
variable {V E X Copy : Type*} [Fintype V] [Fintype E] [Fintype X] [Fintype Copy]
variable [DecidableEq V] [DecidableEq E] [DecidableEq Copy]

/-- Readiness plus the retained strictly younger endpoint excludes a pending
node. Root occupancy also contradicts N.rooted v, INCLUDING v=root. -/
lemma occupied_edge_of_before_ready_below (N : RootedBinary V E X)
    (C : Calendar N.graph) {sample : Copy → X} (v : V) (d : Code N sample)
    (hbefore : BeforeReady N C sample (C.age v) (state d)) (x : Copy)
    (hbelow : BelowMeeting N C v (copyLocation (state d) x)) :
    ∃ f : E, copyLocation (state d) x = .edge f := by
  cases hp : copyLocation (state d) x with
  | node w =>
      have hready := hbefore.1 x
      rw [hp] at hready hbelow
      change C.age w < C.age v at hbelow
      exact False.elim ((not_lt_of_ge hready) hbelow)
  | edge f => exact ⟨f, hp⟩
  | rootPopulation w =>
      have hready := hbefore.1 x
      rw [hp] at hready hbelow
      change C.age w < C.age v at hbelow
      have hupper : C.age v ≤ C.age w := by
        simpa only [hready.1] using C.age_le_of_directed (N.rooted v)
      exact False.elim ((not_lt_of_ge hupper) hbelow)

/-- Direct use of actual_edge_on_original_route and active_unique. This
works through arbitrary original mergers, gamma endpoints and stored registers;
no bridge, interior gamma or unchanged-live-count hypothesis is introduced. -/
lemma child_edge_of_before_ready (N : RootedBinary V E X) (C : Calendar N.graph)
    {sample : Copy → X} (v : V) (e : E) (hsource : N.graph.source e = v)
    (d : Code N sample) (hbefore : BeforeReady N C sample (C.age v) (state d))
    (x : Copy) (hall : ∀ es,
      EdgePath N.graph N.root (N.leaf (sample x)) es → e ∈ es)
    (hexists : ∃ f : E, copyLocation (state d) x = .edge f) :
    copyLocation (state d) x = .edge e := by
  obtain ⟨f, hf⟩ := hexists
  obtain ⟨es, hp, hm⟩ := actual_edge_on_original_route N d x f hf
  have he : e ∈ es := hall es hp
  have hfyoung : C.age (N.graph.target f) < C.age v := hbefore.2.2 x f hf
  have heyoung : C.age (N.graph.target e) < C.age v := by
    simpa only [hsource] using C.edge_older e
  have hbound := hbefore.1 x
  rw [hf] at hbound
  obtain ⟨u, hlu, hu⟩ := exists_between (max_lt_iff.mpr ⟨hfyoung, heyoung⟩)
  have hfa : C.Active u f :=
    ⟨(le_max_left _ _).trans hlu.le, hu.trans_le hbound.2⟩
  have hea : C.Active u e := by
    refine ⟨(le_max_right _ _).trans hlu.le, ?_⟩
    simpa only [hsource] using hu
  have hfe : f = e := hp.active_unique C hm he hfa hea
  exact hf.trans (congrArg (fun z : E => (Location.edge z : Location V E)) hfe)

/-- The supplied all-route original child lies strictly above its sampled tip;
this uses actual path membership and strict edge ages, not a tip-age convention. -/
lemma tip_younger_than_all_path_child (N : RootedBinary V E X) (C : Calendar N.graph)
    (i : X) (v : V) (e : E) (hsource : N.graph.source e = v)
    (hall : ∀ es, EdgePath N.graph N.root (N.leaf i) es → e ∈ es) :
    C.age (N.leaf i) < C.age v := by
  obtain ⟨es, hp⟩ := original_tip_route_exists N i
  have hdown := hp.target_reaches_end_of_mem (hall es hp)
  have hage := (C.age_le_of_directed hdown).trans_lt (C.edge_older e)
  simpa only [hsource] using hage

/-- The endpoint is exactly take(length), not a permuted phase endpoint.
The prefix adapter includes this take even for the first-date empty word. -/
theorem actual_initialized_child_edge (N : RootedBinary V E X) (C : Calendar N.graph)
    (sample : Copy → X) (register : V → Bool) (H : OriginalParentRegistry N)
    (gamma : Hybrid N → unitInterval) (common : Hybrid N → Bool)
    (r : PositivePairRates E) (v : V) (e : E)
    (hsource : N.graph.source e = v) (x : Copy)
    (hall : ∀ es, EdgePath N.graph N.root (N.leaf (sample x)) es → e ∈ es)
    {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (beforeBoundaryProgram N C H gamma common (C.age v))
      (initialCode N sample register)).support) :
    copyLocation (state d) x = .edge e := by
  have hbefore := actual_initialized_before_boundary_support N C sample register
    H gamma common r (C.age v) (original_date_scheduled N C v) hd
  have hyoung := tip_younger_than_all_path_child N C (sample x) v e hsource hall
  have htake : d ∈ (sourceProgram N r
      ((beforeBoundaryProgram N C H gamma common (C.age v)).take
        (beforeBoundaryProgram N C H gamma common (C.age v)).length)
      (initialCode N sample register)).support := by
    simpa only [List.take_length] using hd
  have hleaf : ∀ y ∈ ({x} : Finset Copy), C.age (N.leaf (sample y)) < C.age v := by
    intro y hy
    have hyx : y = x := Finset.mem_singleton.mp hy
    subst y
    exact hyoung
  have hbelow := actual_initialized_before_boundary_prefix_below N C H gamma common r v
    sample register ({x} : Finset Copy) hleaf
    (beforeBoundaryProgram N C H gamma common (C.age v)).length htake
  apply child_edge_of_before_ready N C v e hsource d hbefore x hall
  exact occupied_edge_of_before_ready_below N C v d hbefore x
    (hbelow x (Finset.mem_singleton_self x))

/-- Supplies the old partial-exit draft's hchild premise from the actual
initialCode. Graph-only RouteMeetingGeometry and original sample identities
remain explicit; no arbitrary Code can be admitted by the desired conclusion. -/
theorem actual_initialized_meeting_child_input (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    {i j : X} {v : V} {ei ej : E} (hg : RouteMeetingGeometry N i j v ei ej)
    (inside outside : Finset Copy)
    (hinside : ∀ x ∈ inside, sample x = i)
    (houtside : ∀ y ∈ outside, sample y = j) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (beforeBoundaryProgram N C H gamma common (C.age v))
      (initialCode N sample register)).support) :
    (∀ x ∈ inside, copyLocation (state d) x = .edge ei) ∧
      (∀ y ∈ outside, copyLocation (state d) y = .edge ej) := by
  constructor
  · intro x hx
    apply actual_initialized_child_edge N C sample register H gamma common r v ei
      hg.leftSource x _ hd
    intro es hes
    exact hg.leftOnEveryPath es (by simpa only [hinside x hx] using hes)
  · intro y hy
    apply actual_initialized_child_edge N C sample register H gamma common r v ej
      hg.rightSource y _ hd
    intro es hes
    exact hg.rightOnEveryPath es (by simpa only [houtside y hy] using hes)

/-- An actual supplied law of original initialization registers is supported
statewise by the same result. This does not invent that law or factor it from
an arbitrarily conditioned Old variable. -/
theorem actual_initialized_register_mixture_child_input (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (registerLaw : PMF (V → Bool))
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    {i j : X} {v : V} {ei ej : E} (hg : RouteMeetingGeometry N i j v ei ej)
    (inside outside : Finset Copy)
    (hinside : ∀ x ∈ inside, sample x = i)
    (houtside : ∀ y ∈ outside, sample y = j) {d : Code N sample}
    (hd : d ∈ (registerLaw.bind (fun register =>
      sourceProgram N r (beforeBoundaryProgram N C H gamma common (C.age v))
        (initialCode N sample register))).support) :
    (∀ x ∈ inside, copyLocation (state d) x = .edge ei) ∧
      (∀ y ∈ outside, copyLocation (state d) y = .edge ej) := by
  obtain ⟨register, hregister, hprogram⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  exact actual_initialized_meeting_child_input N C sample register H gamma common r
    hg inside outside hinside houtside hprogram

/-- Both old physical input fields hbefore and hchild are supplied by the new
prefix adapter and the endpoint reader above. All tied exits remain literal;
only PRE-operation states are separated, not the co-located terminal state. -/
theorem actual_initialized_literal_agenda (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    {i j : X} {v : V} {ei ej : E} (hg : RouteMeetingGeometry N i j v ei ej)
    (inside outside : Finset Copy)
    (hinside : ∀ x ∈ inside, sample x = i)
    (houtside : ∀ y ∈ outside, sample y = j) :
    SeparatedAgenda N r inside outside
      (literalPrefix N C H gamma common v ei ej)
      (initialCode N sample register) := by
  apply literal_agenda_of_before_boundary_inputs N C H gamma common r v ei ej
    inside outside (initialCode N sample register) hg.childDistinct
  · exact actual_initialized_before_boundary_separated_agenda N C H gamma common r
      sample register hg inside outside hinside houtside
  · intro d hd
    exact actual_initialized_meeting_child_input N C sample register H gamma common r
      hg inside outside hinside houtside hd

/-- The same initialized literal prefix has the original meeting population
at its terminal endpoint, with every carried copy, genealogy and register kept.
Terminal co-location is an endpoint conclusion, not a separated-agenda field. -/
theorem actual_initialized_literal_endpoint (N : RootedBinary V E X)
    (C : Calendar N.graph) (sample : Copy → X) (register : V → Bool)
    (H : OriginalParentRegistry N) (gamma : Hybrid N → unitInterval)
    (common : Hybrid N → Bool) (r : PositivePairRates E)
    {i j : X} {v : V} {ei ej : E} (hg : RouteMeetingGeometry N i j v ei ej)
    (inside outside : Finset Copy)
    (hinside : ∀ x ∈ inside, sample x = i)
    (houtside : ∀ y ∈ outside, sample y = j) {d : Code N sample}
    (hd : d ∈ (sourceProgram N r (literalPrefix N C H gamma common v ei ej)
      (initialCode N sample register)).support) :
    ∀ x ∈ inside ∪ outside, copyLocation (state d) x = .node v := by
  rw [literalPrefix, sourceProgram_append] at hd
  obtain ⟨m, hm, hdm⟩ := (PMF.mem_support_bind_iff _ _ _).mp hd
  have hc := actual_initialized_meeting_child_input N C sample register H gamma common r
    hg inside outside hinside houtside hm
  exact last_child_exit_colocates N C r v ei ej hg.leftSource hg.rightSource
    inside outside m d hc.1 hc.2 hdm

end G4NaturalCalendarChildInput
