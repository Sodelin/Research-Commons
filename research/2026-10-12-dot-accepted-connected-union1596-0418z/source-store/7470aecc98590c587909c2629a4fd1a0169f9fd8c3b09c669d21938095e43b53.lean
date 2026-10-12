import G1RootSuppressionCutChildTransport

/-! Direct graph-and-MARK admission for the semidirected partner. Actual
marked hybrid vertices coincide with the original binary hybrid vertices.
Every such vertex has an incident literal child bridge after suppression,
realizing the primary binary articulation-node galledness criterion. -/
namespace G1ActualMarkedSemidirectedGalledAdmission
set_option backward.isDefEq.respectTransparency false
open Nanuq.Source GProgram.G5 G1CutChildPorts G1ActualFormerRootPorts G1LiteralSemidirectedRootSuppression
open G1RootSuppressionCutChildTransport G1ExactSemidirectedPartnerAdmission G1ActualGraphNormalization
open scoped Classical
universe u v w
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

def MarkedIncoming (N : RootedBinary V E X) (ports : RootPorts N) (e : SuppressedEdge N)
    (v : SuppressedVertex N) : Prop :=
  (suppressedMark N ports e = .towardTarget ∧ (suppressedGraph N ports).target e = v) ∨
  (suppressedMark N ports e = .towardSource ∧ (suppressedGraph N ports).source e = v)

def MarkedHybrid (N : RootedBinary V E X) (ports : RootPorts N) (v : SuppressedVertex N) : Prop :=
  ∃ e, MarkedIncoming N ports e v

theorem actual_marked_hybrid_iff_original (N : RootedBinary V E X) (ports : RootPorts N)
    (v : SuppressedVertex N) : MarkedHybrid N ports v ↔ N.graph.IsHybrid v.val := by
  constructor
  · rintro ⟨e,hmark⟩
    cases e with
    | inl e =>
      rcases hmark with ⟨hm,ht⟩ | ⟨hm,hs⟩
      · have hh : N.graph.IsHybrid (N.graph.target e.val) := by
          by_cases hh : N.graph.IsHybrid (N.graph.target e.val)
          · exact hh
          · simp [suppressedMark,hh] at hm
        have hv : N.graph.target e.val = v.val := congrArg Subtype.val ht
        rw [← hv]
        exact hh
      · by_cases hh : N.graph.IsHybrid (N.graph.target e.val) <;> simp [suppressedMark,hh] at hm
    | inr e =>
      cases e
      rcases hmark with ⟨hm,ht⟩ | ⟨hm,hs⟩
      · have hh := (actual_suppressed_edge_towards_second_iff N ports).mp hm
        have hv : N.graph.target ports.second = v.val := congrArg Subtype.val ht
        rw [← hv]
        exact hh
      · have hh := (actual_suppressed_edge_towards_first_iff N ports).mp hm
        have hv : N.graph.target ports.first = v.val := congrArg Subtype.val hs
        rw [← hv]
        exact hh
  · intro hh
    let incoming := Finset.univ.filter (fun e : E => N.graph.target e = v.val)
    have hn : incoming.Nonempty := Finset.card_pos.mp (by
      change 0 < N.graph.inDegree v.val
      rw [hh.1]
      norm_num)
    obtain ⟨e,he⟩ := hn
    have ht : N.graph.target e = v.val := (Finset.mem_filter.mp he).2
    by_cases hroot : N.graph.source e = N.root
    · rcases ports.exhaustive e hroot with hf | hs
      · subst e
        refine ⟨.inr (),Or.inr ⟨(actual_suppressed_edge_towards_first_iff N ports).mpr ?_,Subtype.ext ht⟩⟩
        simpa [ht] using hh
      · subst e
        refine ⟨.inr (),Or.inl ⟨(actual_suppressed_edge_towards_second_iff N ports).mpr ?_,Subtype.ext ht⟩⟩
        simpa [ht] using hh
    · refine ⟨.inl ⟨e,hroot⟩,Or.inl ⟨?_,Subtype.ext ht⟩⟩
      simp [suppressedMark,ht,hh]

/-- The binary articulation-node characterization used by the primary
source, expressed on the actual root-suppressed graph and MARKED hybrids. -/
def BinaryGalledCriterion (N : RootedBinary V E X) (ports : RootPorts N) : Prop :=
  ∀ v : SuppressedVertex N, MarkedHybrid N ports v →
    ∃ e : SuppressedEdge N, (suppressedGraph N ports).IsBridge e ∧
      ((suppressedGraph N ports).source e = v ∨ (suppressedGraph N ports).target e = v)

theorem actual_root_suppressed_binary_galled (N : RootedBinary V E X) (hc : CutChild N)
    (ports : RootPorts N) : BinaryGalledCriterion N ports := by
  intro v hv
  have hh := (actual_marked_hybrid_iff_original N ports v).mp hv
  obtain ⟨e,hs,hsource,hcut⟩ := actual_semidirected_hybrid_incident_child_cut N hc ports v.val hh
  exact ⟨.inl e,hcut,Or.inl (hsource.trans (Subtype.ext rfl))⟩

/-- EVERY actual input/output partner of the raw admitted source satisfies
both outer-labelled drawing and the precise marked-hybrid articulation gate.
There is no additional user-supplied galledness/output predicate. -/
theorem actual_source_partner_has_galled_admission {Y : Type w} [Fintype Y]
    (S : Source.{u,v,w} Y) (P : OuterSemidirectedPartner S.network) :
    BinaryGalledCriterion S.network P.ports :=
  actual_root_suppressed_binary_galled S.network S.cutChild P.ports

#print axioms actual_source_partner_has_galled_admission
end G1ActualMarkedSemidirectedGalledAdmission
