import BinaryTraceIncidence

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Actual shortest branches are chosen for every collider of one original
collider-count/distance minimum. The already-proved oriented splices are
joined to literal trace ordering here. Branches include zero-length cases;
the start collider is retained separately from its post-start vertices.
-/

namespace RestrictedCausal.ProbabilitySource

open SelectedWalk WeakInducing VertexActivePaths CanonicalSelection LatentRoots
open InducingSeparation OriginalProjection DiscriminatingStatus

universe u

theorem trace_collider_activated {V : Type u} (D : V → V → Prop) (C : V → Prop)
    {x y b : V} {vertices : List V} (path : Path (arrowGraph D) C x y vertices)
    (collider : TraceCollider D (x :: vertices) b) : SourceSelection.AncestorOf (arrowGraph D) C b := by
  obtain ⟨a, c, occurrence, «left», «right»⟩ := collider
  exact (occurrence.property path.2.2).1 (arrow_heads_collider D «left» «right»)

theorem trace_activation_avoids_main {V : Type u} (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (C : V → Prop)
    {x y b finish : V} {vertices branch : List V}
    (minimal : ColliderMinimal (arrowGraph D) C x y vertices)
    (collider : TraceCollider D (x :: vertices) b)
    (shortest : MinimumDirectedPath (arrowGraph D) C b branch finish) :
    ∀ v ∈ branch, v ∉ x :: vertices := by
  obtain ⟨a, c, occurrence, leftEdge, rightEdge⟩ := collider
  obtain ⟨«left», «right», literal⟩ := occurrence.literal
  exact shortest_activation_avoids_main_path (arrowGraph D) (arrow_single_edges D acyclic)
    (arrow_graph_symm D) (arrow_directed_acyclic D acyclic) C x y a b c finish «left» «right»
    minimal literal (arrow_heads_collider D leftEdge rightEdge) shortest

theorem ordered_trace_activation_disjoint {V : Type u} (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (C : V → Prop)
    {x y b e finishB finishE : V} {vertices branchB branchE : List V}
    (minimal : ColliderMinimal (arrowGraph D) C x y vertices)
    (colliderB : TraceCollider D (x :: vertices) b)
    (colliderE : TraceCollider D (x :: vertices) e)
    (ordered : OrderedCenters (x :: vertices) b e)
    (shortestB : MinimumDirectedPath (arrowGraph D) C b branchB finishB)
    (shortestE : MinimumDirectedPath (arrowGraph D) C e branchE finishE) :
    ∀ v ∈ branchB, v ∉ branchE := by
  obtain ⟨«left», a, middle, d, c, «right», original⟩ := ordered
  have atB : ∀ «next» rest, middle ++ d :: e :: c :: «right» = «next» :: rest →
      Collider (arrowGraph D) a b «next» := by
    intro «next» rest equation
    have occurrence : TripleOn (x :: vertices) a b «next» := by
      rw [original, equation]
      exact TripleOn.of_literal «left» rest a b «next»
    have arrows := trace_collider_original D minimal.1.2.1 occurrence colliderB
    exact arrow_heads_collider D arrows.1 arrows.2
  have occurrenceE : TripleOn (x :: vertices) d e c := by
    rw [original]
    simpa only [List.append_assoc, List.cons_append] using
      TripleOn.of_literal («left» ++ a :: b :: middle) «right» d e c
  have arrowsE := trace_collider_original D minimal.1.2.1 occurrenceE colliderE
  exact shortest_activation_branches_disjoint_ordered (arrowGraph D)
    (arrow_single_edges D acyclic) (arrow_graph_symm D) (arrow_directed_acyclic D acyclic)
    C x y a b d e c finishB finishE «left» middle «right» minimal original atB
    (arrow_heads_collider D arrowsE.1 arrowsE.2) shortestB shortestE

theorem trace_activation_branches_disjoint {V : Type u} (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (C : V → Prop)
    {x y b e finishB finishE : V} {vertices branchB branchE : List V}
    (minimal : ColliderMinimal (arrowGraph D) C x y vertices)
    (colliderB : TraceCollider D (x :: vertices) b)
    (colliderE : TraceCollider D (x :: vertices) e) (distinct : b ≠ e)
    (shortestB : MinimumDirectedPath (arrowGraph D) C b branchB finishB)
    (shortestE : MinimumDirectedPath (arrowGraph D) C e branchE finishE) :
    ∀ v ∈ b :: branchB, v ∉ e :: branchE := by
  have avoidB := trace_activation_avoids_main D acyclic C minimal colliderB shortestB
  have avoidE := trace_activation_avoids_main D acyclic C minimal colliderE shortestE
  have onMainB : b ∈ x :: vertices := by
    obtain ⟨a, c, triple, _, _⟩ := colliderB
    exact triple.left.members.2
  have onMainE : e ∈ x :: vertices := by
    obtain ⟨a, c, triple, _, _⟩ := colliderE
    exact triple.left.members.2
  have tailsDisjoint : ∀ v ∈ branchB, v ∉ branchE := by
    rcases trace_colliders_ordered D acyclic minimal.1.2.1 colliderB colliderE distinct with forward | backward
    · exact ordered_trace_activation_disjoint D acyclic C minimal colliderB colliderE forward shortestB shortestE
    · intro v inB inE
      exact ordered_trace_activation_disjoint D acyclic C minimal colliderE colliderB backward shortestE shortestB
        v inE inB
  intro v inB inE
  rcases List.mem_cons.mp inB with atB | inB <;>
    rcases List.mem_cons.mp inE with atE | inE
  · exact distinct (atB.symm.trans atE)
  · exact avoidE v inE (atB.symm ▸ onMainB)
  · exact avoidB v inB (atE.symm ▸ onMainE)
  · exact tailsDisjoint v inB inE

structure ActivationBranch {V : Type u} (D : V → V → Prop) (C : V → Prop) (b : V) where
  vertices : List V
  finish : V
  shortest : MinimumDirectedPath (arrowGraph D) C b vertices finish

noncomputable def chosenActivationBranch {V : Type u} (D : V → V → Prop) (C : V → Prop)
    {x y : V} {vertices : List V} (path : Path (arrowGraph D) C x y vertices)
    (b : {b // TraceCollider D (x :: vertices) b}) : ActivationBranch D C b.val := by
  classical
  have existsBranch := minimum_directed_path_exists (arrowGraph D) C b.val
    (trace_collider_activated D C path b.property)
  let branch := Classical.choose existsBranch
  let finish := Classical.choose (Classical.choose_spec existsBranch)
  exact ⟨branch, finish, (Classical.choose_spec (Classical.choose_spec existsBranch)).1⟩

end RestrictedCausal.ProbabilitySource
