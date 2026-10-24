import BinarySelectedInvarianceIdentity
import BinaryAncestralMoralConnection

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Actual D1 finite elimination step on the original CPT product. A sink's
binary output sums to one and all other remaining factors are unchanged.
Sinks outside a retained ancestral set are derived from the finite-DAG
rank; they are not supplied by an external topological-sort oracle.
The complete iterated finite-sum/ancestral-marginal join remains separate.
-/

namespace RestrictedCausal.ProbabilitySource.BinaryCPT

open scoped BigOperators
open SelectedWalk

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

def partialJointMass (D : V → V → Prop) (θ : Coordinate D → ℚ) (vertices : Finset V)
    (w : Assignment V) : ℚ := ∏ v ∈ vertices, bernoulliMass θ (row D w v) (w v)

def sumAt (vertex : V) (f : Assignment V → ℚ) : Assignment V → ℚ :=
  fun w => f (pointAssignment vertex w false) + f (pointAssignment vertex w true)

theorem row_update_nonparent (D : V → V → Prop) (w : Assignment V) (vertex child : V) (b : Bool)
    (notParent : ¬ D vertex child) : row D (pointAssignment vertex w b) child = row D w child := by
  have rows : (fun p : {p // D p child} => pointAssignment vertex w b p.val) = (fun p => w p.val) := by
    funext p
    have different : p.val ≠ vertex := by intro same; exact notParent (same ▸ p.property)
    simp only [pointAssignment, if_neg different]
  exact congrArg (fun parents => (⟨child, parents⟩ : Coordinate D)) rows

theorem remaining_factor_unchanged (D : V → V → Prop) (θ : Coordinate D → ℚ)
    (w : Assignment V) (vertex child : V) (b : Bool)
    (different : child ≠ vertex) (notParent : ¬ D vertex child) :
    bernoulliMass θ (row D (pointAssignment vertex w b) child) (pointAssignment vertex w b child) =
      bernoulliMass θ (row D w child) (w child) := by
  rw [row_update_nonparent D w vertex child b notParent]
  simp only [pointAssignment, if_neg different]

theorem erase_sink_product_unchanged (D : V → V → Prop) (θ : Coordinate D → ℚ)
    (vertices : Finset V) (vertex : V) (w : Assignment V) (b : Bool)
    (sink : ∀ child ∈ vertices, ¬ D vertex child) :
    partialJointMass D θ (vertices.erase vertex) (pointAssignment vertex w b) =
      partialJointMass D θ (vertices.erase vertex) w := by
  apply Finset.prod_congr rfl
  intro child member
  have facts := Finset.mem_erase.mp member
  exact remaining_factor_unchanged D θ w vertex child b facts.1 (sink child facts.2)

theorem sumAt_sink_product (D : V → V → Prop) (θ : Coordinate D → ℚ)
    (vertices : Finset V) (vertex : V) (member : vertex ∈ vertices)
    (sink : ∀ child ∈ vertices, ¬ D vertex child) :
    sumAt vertex (partialJointMass D θ vertices) = partialJointMass D θ (vertices.erase vertex) := by
  funext w
  have «split» : ∀ b : Bool,
      partialJointMass D θ vertices (pointAssignment vertex w b) =
        bernoulliMass θ (row D w vertex) b * partialJointMass D θ (vertices.erase vertex) w := by
    intro b
    rw [partialJointMass, ← Finset.mul_prod_erase _ _ member]
    rw [row_update_nonparent D w vertex vertex b (sink vertex member)]
    have atVertex : pointAssignment vertex w b vertex = b := by simp only [pointAssignment, if_pos rfl]
    rw [atVertex]
    rw [show (∏ child ∈ vertices.erase vertex,
        bernoulliMass θ (row D (pointAssignment vertex w b) child) (pointAssignment vertex w b child)) =
        partialJointMass D θ (vertices.erase vertex) w from
      erase_sink_product_unchanged D θ vertices vertex w b sink]
  change _ + _ = _
  rw [«split» false, «split» true, ← add_mul, bernoulli_mass_normalized, one_mul]

def AncestralSet (D : V → V → Prop) (A : Finset V) : Prop :=
  ∀ parent child, D parent child → child ∈ A → parent ∈ A

theorem finite_subset_has_rank_sink (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (U : Finset V) (nonempty : U.Nonempty) :
    ∃ vertex ∈ U, ∀ child ∈ U, ¬ D vertex child := by
  obtain ⟨initial, initialMember⟩ := nonempty
  have maximum := bounded_nat_maximum
    (fun n => ∃ vertex ∈ U, dagRank D acyclic vertex = n) (Fintype.card V)
    ⟨dagRank D acyclic initial, initial, initialMember, rfl⟩
    (by
      intro n witness
      obtain ⟨vertex, member, equality⟩ := witness
      have bound := dagRank_lt_card D acyclic vertex
      omega)
  obtain ⟨n, ⟨vertex, member, rankEq⟩, maximal⟩ := maximum
  refine ⟨vertex, member, ?_⟩
  intro child childMember edge
  have earlier := dagRank_strict D acyclic edge
  have bound := maximal (dagRank D acyclic child) ⟨child, childMember, rfl⟩
  omega

theorem sink_outside_ancestral (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (A U : Finset V)
    (ancestral : AncestralSet D A) (disjoint : Disjoint A U) (nonempty : U.Nonempty) :
    ∃ vertex ∈ U, ∀ child ∈ A ∪ U, ¬ D vertex child := by
  obtain ⟨vertex, member, sink⟩ := finite_subset_has_rank_sink D acyclic U nonempty
  refine ⟨vertex, member, ?_⟩
  intro child inUnion edge
  rcases Finset.mem_union.mp inUnion with inA | inU
  · exact (Finset.disjoint_left.mp disjoint) (ancestral vertex child edge inA) member
  · exact sink child inU edge

end RestrictedCausal.ProbabilitySource.BinaryCPT
