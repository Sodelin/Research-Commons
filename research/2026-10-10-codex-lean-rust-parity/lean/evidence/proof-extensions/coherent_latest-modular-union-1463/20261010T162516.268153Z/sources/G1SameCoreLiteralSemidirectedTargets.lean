import G1LiteralSemidirectedTargetReadoutBinding

/-! Literal semidirected target preservation on the SAME admitted core.
The existing rooted target theorem is used only after the actual marked
switching/deletion/cut readouts are bound in both directions. -/
namespace G1SameCoreLiteralSemidirectedTargets
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 G1ActualGraphNormalization G1OneSameOriginalCoreAssembly
open G1ActualFormerRootPorts G1LiteralSemidirectedTargetReadoutBinding
open G1ActualMarkedSemidirectedGalledAdmission G1ExactSemidirectedPartnerAdmission
open scoped Classical
universe u v w
variable {X : Type w} [Fintype X]

def HasGalledOuterSemidirectedPartner (S : Source.{u,v,w} X) : Prop :=
  ∃ P : OuterSemidirectedPartner S.network, BinaryGalledCriterion S.network P.ports

theorem actual_outer_source_partner_is_galled (S : Source.{u,v,w} X)
    (hs : HasOuterSemidirectedPartner S) : HasGalledOuterSemidirectedPartner S := by
  obtain ⟨P⟩ := hs
  exact ⟨P,actual_source_partner_has_galled_admission S P⟩

def SameLiteralSemidirectedTargets (O T : Source.{u,v,w} X) : Prop :=
  ∀ po : RootPorts O.network, ∀ pt : RootPorts T.network,
    (∀ panel : Finset X,
      actualSemidirectedCutTreeFamily T.network pt panel = actualSemidirectedCutTreeFamily O.network po panel ∧
      actualSemidirectedNontrivialSplits T.network pt panel = actualSemidirectedNontrivialSplits O.network po panel) ∧
    (∀ q : Fin 4 ↪ X, actualSemidirectedQuartets T.network pt q = actualSemidirectedQuartets O.network po q)

theorem actual_same_rooted_targets_bind_literal_semidirected_targets (O T : Source.{u,v,w} X)
    (h : SamePhysicalTargets O T) : SameLiteralSemidirectedTargets O T := by
  intro po pt
  constructor
  · intro panel
    constructor
    · ext cuts
      rw [actual_semidirected_tree_family_iff_rooted T.network T.calendar pt panel,
        actual_semidirected_tree_family_iff_rooted O.network O.calendar po panel,(h.1 panel).2.2.2]
    · ext cut
      rw [actual_semidirected_nontrivial_S_iff_rooted T.network T.calendar pt panel,
        actual_semidirected_nontrivial_S_iff_rooted O.network O.calendar po panel,(h.1 panel).2.1]
  · intro q
    rw [actual_semidirected_Q_equals_rooted T.network T.calendar pt,
      actual_semidirected_Q_equals_rooted O.network O.calendar po,(h.2.1 q)]

#print axioms actual_same_rooted_targets_bind_literal_semidirected_targets
end G1SameCoreLiteralSemidirectedTargets
