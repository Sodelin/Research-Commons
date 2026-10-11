import G1FormerRootHybridDirections

/-! The literal multigraph and edge marks prescribed by the rooted-LSA
partner convention: keep every non-root edge ID, replace the two former-root
arcs by ONE edge, undirect non-hybrid arcs, and direct the merged edge towards
its hybrid endpoint when present. Parallel retained arcs are never collapsed.
The no-double-direction fact is derived from the actual LSA DAG. -/
namespace G1LiteralSemidirectedRootSuppression
open Nanuq.Source GProgram.G5 G1ActualFormerRootPorts G1FormerRootHybridDirections
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

abbrev SuppressedVertex (N : RootedBinary V E X) := {v : V // v ≠ N.root}
abbrev KeptEdge (N : RootedBinary V E X) := {e : E // N.graph.source e ≠ N.root}
abbrev SuppressedEdge (N : RootedBinary V E X) := KeptEdge N ⊕ Unit

def firstChild (N : RootedBinary V E X) (ports : RootPorts N) : SuppressedVertex N :=
  ⟨N.graph.target ports.first,N.edge_target_ne_root ports.first⟩
def secondChild (N : RootedBinary V E X) (ports : RootPorts N) : SuppressedVertex N :=
  ⟨N.graph.target ports.second,N.edge_target_ne_root ports.second⟩
def keptSource (N : RootedBinary V E X) (e : KeptEdge N) : SuppressedVertex N :=
  ⟨N.graph.source e.val,e.property⟩
def keptTarget (N : RootedBinary V E X) (e : KeptEdge N) : SuppressedVertex N :=
  ⟨N.graph.target e.val,N.edge_target_ne_root e.val⟩

def suppressedGraph (N : RootedBinary V E X) (ports : RootPorts N) :
    EdgeGraph (SuppressedVertex N) (SuppressedEdge N) where
  source := fun e => match e with | .inl e => keptSource N e | .inr _ => firstChild N ports
  target := fun e => match e with | .inl e => keptTarget N e | .inr _ => secondChild N ports

def suppressedLeaf (N : RootedBinary V E X) (x : X) : SuppressedVertex N :=
  ⟨N.leaf x,N.leaf_ne_root x⟩

inductive EdgeMark where
  | undirected | towardSource | towardTarget
  deriving DecidableEq, Repr

noncomputable def suppressedMark (N : RootedBinary V E X) (ports : RootPorts N) :
    SuppressedEdge N → EdgeMark
  | .inl e => if N.graph.IsHybrid (N.graph.target e.val) then .towardTarget else .undirected
  | .inr _ => if N.graph.IsHybrid (N.graph.target ports.first) then .towardSource
      else if N.graph.IsHybrid (N.graph.target ports.second) then .towardTarget else .undirected

theorem actual_retained_edge_marks (N : RootedBinary V E X) (ports : RootPorts N) (e : KeptEdge N) :
    suppressedMark N ports (.inl e) =
      if N.graph.IsHybrid (N.graph.target e.val) then .towardTarget else .undirected := rfl

theorem actual_suppressed_edge_towards_first_iff (N : RootedBinary V E X) (ports : RootPorts N) :
    suppressedMark N ports (.inr ()) = .towardSource ↔ N.graph.IsHybrid (N.graph.target ports.first) := by
  by_cases hf : N.graph.IsHybrid (N.graph.target ports.first) <;>
    by_cases hs : N.graph.IsHybrid (N.graph.target ports.second) <;> simp [suppressedMark,hf,hs]

theorem actual_suppressed_edge_towards_second_iff (N : RootedBinary V E X) (ports : RootPorts N) :
    suppressedMark N ports (.inr ()) = .towardTarget ↔ N.graph.IsHybrid (N.graph.target ports.second) := by
  have hnot := actual_root_has_at_most_one_hybrid_child N ports
  by_cases hfirst : N.graph.IsHybrid (N.graph.target ports.first)
  · have hsecond : ¬ N.graph.IsHybrid (N.graph.target ports.second) := fun hs => hnot ⟨hfirst,hs⟩
    simp [suppressedMark,hfirst,hsecond]
  · simp [suppressedMark,hfirst]

theorem actual_suppressed_edge_undirected_iff (N : RootedBinary V E X) (ports : RootPorts N) :
    suppressedMark N ports (.inr ()) = .undirected ↔
      ¬ N.graph.IsHybrid (N.graph.target ports.first) ∧ ¬ N.graph.IsHybrid (N.graph.target ports.second) := by
  by_cases hf : N.graph.IsHybrid (N.graph.target ports.first) <;>
    by_cases hs : N.graph.IsHybrid (N.graph.target ports.second) <;> simp [suppressedMark,hf,hs]

theorem actual_kept_parallel_ids_preserved (N : RootedBinary V E X) :
    Function.Injective (Sum.inl : KeptEdge N → SuppressedEdge N) := Sum.inl_injective

theorem actual_merged_edge_not_loop (N : RootedBinary V E X) (ports : RootPorts N) :
    (suppressedGraph N ports).source (.inr ()) ≠ (suppressedGraph N ports).target (.inr ()) := by
  intro he
  exact actual_root_children_distinct N ports (congrArg Subtype.val he)

#print axioms actual_suppressed_edge_towards_second_iff
end G1LiteralSemidirectedRootSuppression
