import G1RootSubdivisionPlanarAdmission

/-! Exact outer-labelled SEMIDIRECTED rooted-partner admission. Root ports
are actual original arcs, the graph is literal former-root suppression,
and every mark is fixed by original hybrid incidence. Faithful curved edge
IDs allow parallel arcs, and ONLY labelled leaves must lie on the unbounded
face. The convention is Holtgrefe et al., Definition2.2 and2.3(v).

This bridge transports the class along the SAME constructed splice Steps;
it supplies no stochastic output equality and no embedding-order surrogate. -/
namespace G1ExactSemidirectedPartnerAdmission
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 G1ActualFormerRootPorts G1LiteralSemidirectedRootSuppression
open G1OuterLabelledMultigraphCurves G1RootSuppressedPlanarCurves G1RootSubdivisionPlanarAdmission
open G1ActualGraphNormalization G1SpliceOuterLabelledCurveAdmission
open scoped Classical
universe u v w
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

/-- A rooted binary LSA partner with exactly its prescribed root-suppressed
semidirected multigraph drawing. The edge marks are DEFINITIONS from original
hybrid incidence, not a permissive user-selected direction assignment. -/
structure OuterSemidirectedPartner (N : RootedBinary V E X) where
  ports : RootPorts N
  outer : OuterLabelledCurves (suppressedGraph N ports) (suppressedLeaf N)

noncomputable def OuterSemidirectedPartner.graph {N : RootedBinary V E X}
    (P : OuterSemidirectedPartner N) := suppressedGraph N P.ports
noncomputable def OuterSemidirectedPartner.mark {N : RootedBinary V E X}
    (P : OuterSemidirectedPartner N) := suppressedMark N P.ports

/-- Partner admission uses the actual suppressed semidirected graph. It is
not mere compatibility with a displayed split circular order. -/
def HasOuterSemidirectedPartner {Y : Type w} [Fintype Y] (S : Source.{u,v,w} Y) : Prop :=
  Nonempty (OuterSemidirectedPartner S.network)

theorem actual_partner_drawing_equivalent_rooted_drawing (N : RootedBinary V E X) :
    Nonempty (OuterSemidirectedPartner N) ↔ Nonempty (OuterLabelledCurves N.graph N.leaf) := by
  constructor
  · rintro ⟨P⟩
    exact ⟨actualRootSubdivisionOuterCurves N P.ports P.outer⟩
  · rintro ⟨D⟩
    exact ⟨⟨actualRootPorts N,actualRootSuppressedOuterCurves N (actualRootPorts N) D⟩⟩

/-- Even the arbitrary ordering/choice of the TWO actual root ports does
not affect class admission: the inverse subdivision is proved, not assumed. -/
theorem actual_every_root_port_choice_admitted (N : RootedBinary V E X)
    (hN : Nonempty (OuterSemidirectedPartner N)) (ports : RootPorts N) :
    Nonempty (OuterLabelledCurves (suppressedGraph N ports) (suppressedLeaf N)) := by
  obtain ⟨D⟩ := (actual_partner_drawing_equivalent_rooted_drawing N).mp hN
  exact ⟨actualRootSuppressedOuterCurves N ports D⟩

/-- The class witness for the EXACT output of one physical splice is
constructed by subdividing input, concatenating the retained bigon path,
and suppressing the same retained former root. -/
theorem actual_step_preserves_outer_semidirected_partner {Y : Type w} [Fintype Y]
    {S T : Source.{u,v,w} Y} (step : Step S T) (hS : HasOuterSemidirectedPartner S) :
    HasOuterSemidirectedPartner T := by
  apply (actual_partner_drawing_equivalent_rooted_drawing T.network).mpr
  apply actual_step_preserves_outer_labelled_curves step
  exact (actual_partner_drawing_equivalent_rooted_drawing S.network).mp hS

/-- Exact partner admission on the SAME finite physical core, never a
separately selected core or a stronger all-vertices/straight-edge class. -/
theorem actual_steps_preserve_outer_semidirected_partner {Y : Type w} [Fintype Y]
    {S T : Source.{u,v,w} Y} (steps : Steps S T) (hS : HasOuterSemidirectedPartner S) :
    HasOuterSemidirectedPartner T := by
  induction steps with
  | refl => exact hS
  | tail prior step ih => exact actual_step_preserves_outer_semidirected_partner step ih

#print axioms actual_steps_preserve_outer_semidirected_partner
end G1ExactSemidirectedPartnerAdmission
