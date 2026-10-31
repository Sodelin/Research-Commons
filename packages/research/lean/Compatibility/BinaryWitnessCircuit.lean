import BinaryActivationFamily

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

The concrete fair/copy/XOR/zero gate assignment on the ORIGINAL finite
DAG. Fair-bit indices are exactly the main-path trek-source vertices.
All gate ranks are derived from original-DAG acyclicity and finiteness.
Chosen activation branches and their unique predecessors are derived from
the one actual minimum path, not supplied as an independent interface.
-/

namespace RestrictedCausal.ProbabilitySource

open SelectedWalk WeakInducing VertexActivePaths CanonicalSelection LatentRoots
open InducingSeparation OriginalProjection BinaryCPT

universe u

structure BinaryWitnessGeometry (V : Type u) where
  arrow : V → V → Prop
  acyclic : ∀ a xs, Route arrow a xs a → xs = []
  conditioned : Finset V
  start : V
  finish : V
  distinct : start ≠ finish
  startOutside : start ∉ conditioned
  finishOutside : finish ∉ conditioned
  vertices : List V
  minimal : ColliderMinimal (arrowGraph arrow) (fun v => v ∈ conditioned) start finish vertices

namespace BinaryWitnessGeometry

variable {V : Type u} [Fintype V] [DecidableEq V]

def main (g : BinaryWitnessGeometry V) : List V := g.start :: g.vertices
def ColliderIndex (g : BinaryWitnessGeometry V) := {v // TraceCollider g.arrow g.main v}
def SourceIndex (g : BinaryWitnessGeometry V) := {v // TrekRoot g.arrow g.main v}
def ordinary (g : BinaryWitnessGeometry V) (v : V) : Prop :=
  v ∈ g.main ∧ ¬ TraceCollider g.arrow g.main v

theorem simple (g : BinaryWitnessGeometry V) : g.main.Nodup := g.minimal.1.2.1

noncomputable def branch (g : BinaryWitnessGeometry V) (b : g.ColliderIndex) :
    ActivationBranch g.arrow (fun v => v ∈ g.conditioned) b.val :=
  chosenActivationBranch g.arrow (fun v => v ∈ g.conditioned) g.minimal.1 b

theorem branch_avoids_main (g : BinaryWitnessGeometry V) (b : g.ColliderIndex) :
    ∀ v ∈ (g.branch b).vertices, v ∉ g.main :=
  trace_activation_avoids_main g.arrow g.acyclic _ g.minimal b.property (g.branch b).shortest

theorem branches_disjoint (g : BinaryWitnessGeometry V) (b e : g.ColliderIndex) (different : b ≠ e) :
    ∀ v ∈ b.val :: (g.branch b).vertices, v ∉ e.val :: (g.branch e).vertices := by
  have differentValues : b.val ≠ e.val := fun h => different (Subtype.ext h)
  exact trace_activation_branches_disjoint g.arrow g.acyclic _ g.minimal b.property e.property
    differentValues (g.branch b).shortest (g.branch e).shortest

theorem branch_simple (g : BinaryWitnessGeometry V) (b : g.ColliderIndex) :
    (b.val :: (g.branch b).vertices).Nodup :=
  (g.branch b).shortest.route.acyclic_trace_nodup (arrow_directed_acyclic g.arrow g.acyclic)

def BranchParent (g : BinaryWitnessGeometry V) (parent child : V) : Prop :=
  ∃ b : g.ColliderIndex, NextOn (b.val :: (g.branch b).vertices) parent child

theorem branchParent_edge (g : BinaryWitnessGeometry V) {parent child : V}
    (h : g.BranchParent parent child) : g.arrow parent child := by
  obtain ⟨b, «next»⟩ := h
  exact (arrow_directed_exact g.arrow parent child).mp
    (route_next_edge (g.branch b).shortest.route parent child «next»)

theorem branchParent_off_main (g : BinaryWitnessGeometry V) {parent child : V}
    (h : g.BranchParent parent child) : child ∉ g.main := by
  obtain ⟨b, «next»⟩ := h
  exact g.branch_avoids_main b child «next».second_in_tail

theorem branchParent_unique (g : BinaryWitnessGeometry V) {a b vertex : V}
    («first» : g.BranchParent a vertex) (second : g.BranchParent b vertex) : a = b := by
  obtain ⟨firstIndex, firstNext⟩ := «first»
  obtain ⟨secondIndex, secondNext⟩ := second
  by_cases same : firstIndex = secondIndex
  · subst secondIndex
    exact firstNext.unique_left (g.branch_simple firstIndex) secondNext
  · exact (g.branches_disjoint firstIndex secondIndex same vertex firstNext.members.2 secondNext.members.2).elim

theorem branch_vertex_parent (g : BinaryWitnessGeometry V) (b : g.ColliderIndex) (vertex : V)
    (member : vertex ∈ (g.branch b).vertices) : ∃ parent, g.BranchParent parent vertex := by
  obtain ⟨parent, «next»⟩ := NextOn.preceding_of_mem b.val vertex (g.branch b).vertices member
  exact ⟨parent, b, «next»⟩

noncomputable def rank (g : BinaryWitnessGeometry V) : V → Nat := dagRank g.arrow g.acyclic

theorem rank_strict (g : BinaryWitnessGeometry V) {parent child : V} (arrow : g.arrow parent child) :
    g.rank parent < g.rank child := dagRank_strict g.arrow g.acyclic arrow

noncomputable def gate (g : BinaryWitnessGeometry V) (vertex : V) :
    Gate g.arrow g.rank g.SourceIndex vertex := by
  classical
  by_cases member : vertex ∈ g.main
  · by_cases collider : TraceCollider g.arrow g.main vertex
    · let «left» := Classical.choose collider
      let «right» := Classical.choose (Classical.choose_spec collider)
      have spec := Classical.choose_spec (Classical.choose_spec collider)
      exact .xor «left» «right» spec.2.1 spec.2.2 (g.rank_strict spec.2.1) (g.rank_strict spec.2.2)
    · by_cases hasParent : ∃ parent, MainParent g.arrow g.main parent vertex
      · let parent := Classical.choose hasParent
        have spec := Classical.choose_spec hasParent
        exact .copy parent spec.2 (g.rank_strict spec.2)
      · exact .fair ⟨vertex, member, collider, hasParent⟩
  · by_cases hasParent : ∃ parent, g.BranchParent parent vertex
    · let parent := Classical.choose hasParent
      have allowed := g.branchParent_edge (Classical.choose_spec hasParent)
      exact .copy parent allowed (g.rank_strict allowed)
    · exact .off

theorem gate_at_source (g : BinaryWitnessGeometry V) (i : g.SourceIndex) : g.gate i.val = .fair i := by
  classical
  simp only [gate, dif_pos i.property.1, dif_neg i.property.2.1, dif_neg i.property.2.2]
  rfl

theorem fair_is_source (g : BinaryWitnessGeometry V) (vertex : V) (i : g.SourceIndex)
    (fair : g.gate vertex = .fair i) : i.val = vertex := by
  classical
  by_cases member : vertex ∈ g.main
  · by_cases collider : TraceCollider g.arrow g.main vertex
    · simp only [gate, dif_pos member, dif_pos collider] at fair
      cases fair
    · by_cases hasParent : ∃ parent, MainParent g.arrow g.main parent vertex
      · simp only [gate, dif_pos member, dif_neg collider, dif_pos hasParent] at fair
        cases fair
      · simp only [gate, dif_pos member, dif_neg collider, dif_neg hasParent] at fair
        have same : (⟨vertex, member, collider, hasParent⟩ : g.SourceIndex) = i := by
          injection fair
        exact (congrArg Subtype.val same).symm
  · by_cases hasParent : ∃ parent, g.BranchParent parent vertex
    · simp only [gate, dif_neg member, dif_pos hasParent] at fair
      cases fair
    · simp only [gate, dif_neg member, dif_neg hasParent] at fair
      cases fair

noncomputable def circuit (g : BinaryWitnessGeometry V) : BoundaryCircuit g.arrow g.SourceIndex where
  rank := g.rank
  gate := g.gate
  source := Subtype.val
  source_gate := g.gate_at_source
  fair_source := g.fair_is_source

theorem gate_main_copy (g : BinaryWitnessGeometry V) {parent child : V}
    (ordinary : g.ordinary child) (parentOn : MainParent g.arrow g.main parent child) :
    g.circuit.Copies parent child := by
  classical
  have hasParent : ∃ p, MainParent g.arrow g.main p child := ⟨parent, parentOn⟩
  have chosen := Classical.choose_spec hasParent
  have same := mainParent_unique g.arrow g.simple ordinary.2 chosen parentOn
  refine ⟨parentOn.2, g.rank_strict parentOn.2, ?_⟩
  simp only [circuit, gate, dif_pos ordinary.1, dif_neg ordinary.2, dif_pos hasParent]
  cases same
  rfl

theorem gate_branch_copy (g : BinaryWitnessGeometry V) {parent child : V}
    (parentOn : g.BranchParent parent child) : g.circuit.Copies parent child := by
  classical
  have outside := g.branchParent_off_main parentOn
  have hasParent : ∃ p, g.BranchParent p child := ⟨parent, parentOn⟩
  have chosen := Classical.choose_spec hasParent
  have same := g.branchParent_unique chosen parentOn
  have allowed := g.branchParent_edge parentOn
  refine ⟨allowed, g.rank_strict allowed, ?_⟩
  simp only [circuit, gate, dif_neg outside, dif_pos hasParent]
  cases same
  rfl

theorem gate_collider_xor (g : BinaryWitnessGeometry V) {a b c : V}
    (occurrence : TripleOn g.main a b c) (collider : TraceCollider g.arrow g.main b) :
    ∃ leftEdge rightEdge leftRank rightRank,
      g.circuit.gate b = .xor a c leftEdge rightEdge leftRank rightRank := by
  classical
  have member := occurrence.left.members.2
  let «left» := Classical.choose collider
  let «right» := Classical.choose (Classical.choose_spec collider)
  have spec := Classical.choose_spec (Classical.choose_spec collider)
  have sameLeft : «left» = a := spec.1.left.unique_left g.simple occurrence.left
  have sameRight : «right» = c := spec.1.right.unique_right g.simple occurrence.right
  have arrows := trace_collider_original g.arrow g.simple occurrence collider
  refine ⟨arrows.1, arrows.2, g.rank_strict arrows.1, g.rank_strict arrows.2, ?_⟩
  simp only [circuit, gate, dif_pos member, dif_pos collider]
  dsimp [«left», «right»] at sameLeft sameRight
  cases sameLeft
  cases sameRight
  rfl

theorem ordinary_gate_classification (g : BinaryWitnessGeometry V) (vertex : V)
    (ordinary : g.ordinary vertex) :
    (∃ i, g.circuit.gate vertex = .fair i) ∨
    ∃ parent allowed earlier, g.circuit.gate vertex = .copy parent allowed earlier ∧ g.ordinary parent := by
  classical
  by_cases hasParent : ∃ p, MainParent g.arrow g.main p vertex
  · obtain ⟨parent, parentOn⟩ := hasParent
    obtain ⟨allowed, earlier, equation⟩ := g.gate_main_copy ordinary parentOn
    exact Or.inr ⟨parent, allowed, earlier, equation,
      mainParent_member g.arrow parentOn, mainParent_ordinary g.arrow g.acyclic g.simple parentOn⟩
  · exact Or.inl ⟨⟨vertex, ordinary.1, ordinary.2, hasParent⟩, by
      simp only [circuit, gate, dif_pos ordinary.1, dif_neg ordinary.2, dif_neg hasParent]⟩

theorem branch_copy_route (g : BinaryWitnessGeometry V) (b : g.ColliderIndex) :
    Route g.circuit.Copies b.val (g.branch b).vertices (g.branch b).finish := by
  have full := (g.branch b).shortest.route
  have transform : ∀ {start rest finish}, Route (Directed (arrowGraph g.arrow)) start rest finish →
      (∀ a child, NextOn (start :: rest) a child → g.BranchParent a child) →
      Route g.circuit.Copies start rest finish := by
    intro start rest finish route
    induction route with
    | nil start => intro _; exact .nil start
    | @cons start «next» finish rest edge tail ih =>
        intro every
        exact .cons (g.gate_branch_copy (every start «next» (.here _ _ _)))
          (ih (fun a child h => every a child (.there start h)))
  exact transform full (fun a child h => ⟨b, h⟩)

theorem start_ordinary (g : BinaryWitnessGeometry V) : g.ordinary g.start :=
  ⟨List.mem_cons_self, trace_first_not_collider g.arrow g.start g.vertices g.simple⟩

theorem finish_ordinary (g : BinaryWitnessGeometry V) : g.ordinary g.finish := by
  obtain ⟨front, equation⟩ := route_terminal_trace g.minimal.1.1
  constructor
  · rw [main, equation]; simp
  · rw [main, equation]
    exact trace_last_not_collider g.arrow front g.finish (by simpa only [main, equation] using g.simple)

theorem ordinary_outside_conditioning (g : BinaryWitnessGeometry V) {vertex : V}
    (ordinary : g.ordinary vertex) : vertex ∉ g.conditioned := by
  rcases route_member_position g.minimal.1.1 vertex ordinary.1 with atStart | atFinish | internal
  · exact atStart.symm ▸ g.startOutside
  · exact atFinish.symm ▸ g.finishOutside
  · obtain ⟨a, c, occurrence⟩ := internal
    apply (occurrence.property g.minimal.1.2.2).2
    intro collider
    have arrows := arrow_collider_arrows g.arrow collider
    exact ordinary.2 ⟨a, c, occurrence, arrows.1, arrows.2⟩

end BinaryWitnessGeometry

end RestrictedCausal.ProbabilitySource
