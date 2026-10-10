import G1ActualFormerRootPorts

/-! Former-root suppression cannot create a doubly directed edge. The
actual rooted LSA DAG has at most ONE hybrid child at its root, derived
from actual reachability/parent IDs/acyclicity, not an added class premise. -/
namespace G1FormerRootHybridDirections
open Nanuq.Source GProgram.G5 G1ActualFormerRootPorts
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

lemma actual_nonroot_reachable_from_root_child (N : RootedBinary V E X) (ports : RootPorts N)
    (v : V) (hv : v ≠ N.root) :
    N.graph.DReach (N.graph.target ports.first) v ∨ N.graph.DReach (N.graph.target ports.second) v := by
  rcases Relation.ReflTransGen.cases_head (N.rooted v) with he | ⟨next,hstep,hlater⟩
  · exact False.elim (hv he.symm)
  · obtain ⟨e,hs,ht⟩ := hstep
    rcases ports.exhaustive e hs with he | he
    · subst e; left; simpa only [EdgeGraph.DReach, ht] using hlater
    · subst e; right; simpa only [EdgeGraph.DReach, ht] using hlater

lemma actual_hybrid_root_child_reached_from_other (N : RootedBinary V E X) (ports : RootPorts N)
    (hh : N.graph.IsHybrid (N.graph.target ports.first)) :
    N.graph.DReach (N.graph.target ports.second) (N.graph.target ports.first) := by
  obtain ⟨f,hft,hfe⟩ := N.graph.hybrid_has_partner hh ports.first
  have hs : N.graph.source f ≠ N.root := by
    intro hroot
    rcases ports.exhaustive f hroot with he | he
    · exact hfe he
    · have ht := hft
      rw [he] at ht
      exact actual_root_children_distinct N ports ht.symm
  rcases actual_nonroot_reachable_from_root_child N ports (N.graph.source f) hs with hfirst | hsecond
  · exact False.elim (N.acyclic (N.graph.target ports.first)
      (Relation.TransGen.tail' hfirst ⟨f,rfl,hft⟩))
  · exact hsecond.tail ⟨f,rfl,hft⟩

def reversePorts (N : RootedBinary V E X) (ports : RootPorts N) : RootPorts N where
  first := ports.second
  second := ports.first
  different := Ne.symm ports.different
  source_first := ports.source_second
  source_second := ports.source_first
  exhaustive e he := (ports.exhaustive e he).symm

/-- Exact direction handling for the root-suppressed edge: it is undirected
or directed towards ONE hybrid endpoint. Parallel arcs remain separate IDs. -/
theorem actual_root_has_at_most_one_hybrid_child (N : RootedBinary V E X) (ports : RootPorts N) :
    ¬ (N.graph.IsHybrid (N.graph.target ports.first) ∧ N.graph.IsHybrid (N.graph.target ports.second)) := by
  rintro ⟨hfirst,hsecond⟩
  have hf := actual_hybrid_root_child_reached_from_other N ports hfirst
  have hs := actual_hybrid_root_child_reached_from_other N (reversePorts N ports) hsecond
  exact actual_root_children_distinct N ports (N.graph.dreach_antisymm N.acyclic hs hf)

#print axioms actual_root_has_at_most_one_hybrid_child
end G1FormerRootHybridDirections
