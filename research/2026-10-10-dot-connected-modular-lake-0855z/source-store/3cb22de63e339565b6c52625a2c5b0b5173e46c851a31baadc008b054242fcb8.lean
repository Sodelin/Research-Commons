import G1SpliceOuterLabelledCurveAdmission

/-! The former-root suppression data are derived from the actual raw root
degree and LSA condition. Root arcs retain separate IDs; their children are
distinct, so suppression does not invent a loop or conflate parallel arcs. -/
namespace G1ActualFormerRootPorts
open Nanuq.Source GProgram.G5
open scoped Classical
variable {V E X : Type*} [Fintype V] [Fintype E] [Fintype X] [DecidableEq V] [DecidableEq E]

structure RootPorts (N : RootedBinary V E X) where
  first : E
  second : E
  different : first ≠ second
  source_first : N.graph.source first = N.root
  source_second : N.graph.source second = N.root
  exhaustive : ∀ e, N.graph.source e = N.root → e = first ∨ e = second

theorem actual_root_ports_exist (N : RootedBinary V E X) : Nonempty (RootPorts N) := by
  let roots := Finset.univ.filter (fun e : E => N.graph.source e = N.root)
  have hcard : roots.card = 2 := N.root_degrees.2
  obtain ⟨first,second,hne,he⟩ := Finset.card_eq_two.mp hcard
  have hf : first ∈ roots := by rw [he]; simp
  have hs : second ∈ roots := by rw [he]; simp
  refine ⟨⟨first,second,hne,(Finset.mem_filter.mp hf).2,(Finset.mem_filter.mp hs).2,?_⟩⟩
  intro e hroot
  have hm : e ∈ roots := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hroot⟩
  rw [he] at hm
  simpa using hm

noncomputable def actualRootPorts (N : RootedBinary V E X) : RootPorts N :=
  Classical.choice (actual_root_ports_exist N)

theorem actual_root_children_distinct (N : RootedBinary V E X) (ports : RootPorts N) :
    N.graph.target ports.first ≠ N.graph.target ports.second := by
  intro heq
  let child := N.graph.target ports.first
  have hchild : child ≠ N.root := N.edge_target_ne_root ports.first
  obtain ⟨x,avoid⟩ := N.exists_leaf_avoiding_of_ne_root hchild
  rcases Relation.ReflTransGen.cases_head avoid.2.2 with hsame | ⟨next,hstep,_⟩
  · exact N.leaf_ne_root x hsame.symm
  · obtain ⟨e,hs,ht⟩ := hstep.1
    have he := ports.exhaustive e hs
    rcases he with he | he
    · subst e
      exact hstep.2.2 ht.symm
    · subst e
      exact hstep.2.2 (ht.symm.trans heq.symm)

#print axioms actual_root_children_distinct
end G1ActualFormerRootPorts
