import GuardedCycleDetour
import OriginalIncomingTransport

/-! UNCOMPILED original marked simple-gall admission on the literal chosen
root-suppressed partner. No CutChild or desired raw detour is an input.
The original network's identification with this chosen partner remains explicit. -/
namespace Nanuq.MarkedGallAdmission
open Nanuq.Source Nanuq.SimpleGallAdmission
open G1ActualFormerRootPorts G1LiteralSemidirectedRootSuppression
open G1ActualMarkedSemidirectedGalledAdmission G1RootSuppressionCutChildTransport
open scoped Classical Graph
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X]
    [DecidableEq V] [DecidableEq E]
variable (N : RootedBinary V E X) (ports : RootPorts N)

/-- Transparent literal syntax for the original marked simple-gall condition.
Both incoming edge IDs lie on one simple undirected cycle; every OTHER edge
is unmarked. Parallel bigons are admitted. This is not BinaryGalledCriterion. -/
def MarkedSimpleGalls : Prop :=
  ∀ (h : SuppressedVertex N) (e f : SuppressedEdge N), e≠f →
    MarkedIncoming N ports e h → MarkedIncoming N ports f h →
    ∃ (a : SuppressedVertex N) (W : List (SuppressedEdge N)),
      (originalGraph (suppressedGraph N ports)).IsCycleThrough e h a W ∧ f∈W ∧
        ∀ d ∈ e::W, d≠e → d≠f → suppressedMark N ports d = .undirected

/-- Admission from ACTUAL marked simple cycles in the literal suppressed
partner to the ORIGINAL ordinary-parent detours. All traversal uses original
IDs; a merged root edge expands to its two original root IDs. -/
theorem actual_marked_simple_galls_to_detour
    (hg : MarkedSimpleGalls N ports) : N.graph.GalledDetour := by
  intro h hh e f hef he hf
  let v : SuppressedVertex N := ⟨h,actual_hybrid_nonroot N h hh⟩
  obtain ⟨a,ha,hma,hleft⟩ := incoming_parent_transport N ports hh he
  obtain ⟨b,hb,hmb,hright⟩ := incoming_parent_transport N ports hh hf
  obtain ⟨a',W,hcycle,hfm,hord⟩ :=
    hg v (incomingID N e) (incomingID N f)
      (incoming_ids_distinct N ports hef he hf) hma hmb
  have haa : a'=a := hcycle.isLink.right_unique ha
  subst a'
  have hwalk := guarded_cycle_detour (suppressedGraph N ports) hcycle hb hfm hord
  have hallowed : (suppressedGraph N ports).UReach (SuppressedOrdinaryAvoid N ports h) a b := by
    apply (suppressedGraph N ports).ureach_mono _ hwalk
    intro d hd
    exact ⟨hd.1,fun heq => hd.2.1 (Subtype.ext heq),fun heq => hd.2.2 (Subtype.ext heq)⟩
  have hex := ordinary_suppressed_walk_expansion N ports (actual_hybrid_nonroot N h hh) hallowed
  exact hleft.trans (hex.trans (N.graph.ureach_symm hright))

#print axioms actual_marked_simple_galls_to_detour
end Nanuq.MarkedGallAdmission
