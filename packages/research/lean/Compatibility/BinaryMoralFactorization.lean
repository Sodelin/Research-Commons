import BinaryFactorElimination

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

D1 graph-to-factor join. For d-separated endpoints, the component of x
in the ancestral moral graph after deleting C does not contain y. Every
actual ancestral CPT family is confined to that component or its
complement once C is fixed. The clamped original product is split into
two factors with disjoint dependence sets. No factorization oracle is a
premise; its factors are literal finite products of original CPTs.
-/

namespace RestrictedCausal.ProbabilitySource.BinaryCPT

open scoped BigOperators
open SelectedWalk CanonicalSelection LatentRoots OriginalProjection InducingSeparation
open SourceSelection (AncestorOf)

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]

def clampCondition (C : Finset V) (base w : Assignment V) : Assignment V :=
  fun v => if v ∈ C then base v else w v

def clampedFactor (D : V → V → Prop) (θ : Coordinate D → ℚ) (C : Finset V)
    (base : Assignment V) (child : V) (w : Assignment V) : ℚ :=
  bernoulliMass θ (row D (clampCondition C base w) child) (clampCondition C base w child)

theorem clamped_factor_depends (D : V → V → Prop) (θ : Coordinate D → ℚ)
    (C S : Finset V) (base : Assignment V) (child : V)
    (family : ∀ v, FamilyVertex D child v → v ∉ C → v ∈ S) :
    DependsOn S (clampedFactor D θ C base child) := by
  intro «first» second agree
  have familyAgreement : ∀ v, FamilyVertex D child v →
      clampCondition C base «first» v = clampCondition C base second v := by
    intro v member
    by_cases conditioned : v ∈ C
    · simp only [clampCondition, if_pos conditioned]
    · simp only [clampCondition, if_neg conditioned]
      exact agree v (family v member conditioned)
  have atChild := familyAgreement child (Or.inl rfl)
  have parentRows : (fun p : {p // D p child} => clampCondition C base «first» p.val) =
      (fun p => clampCondition C base second p.val) := by
    funext p
    exact familyAgreement p.val (Or.inr p.property)
  have rows := congrArg (fun parents => (⟨child, parents⟩ : Coordinate D)) parentRows
  unfold clampedFactor row
  rw [rows, atChild]

theorem finite_product_depends {I : Type*} (indices : Finset I) (S : Finset V)
    (factor : I → Assignment V → ℚ) (each : ∀ i ∈ indices, DependsOn S (factor i)) :
    DependsOn S (fun w => ∏ i ∈ indices, factor i w) := by
  intro «first» second agree
  apply Finset.prod_congr rfl
  intro i member
  exact each i member «first» second agree

noncomputable def ancestralVertices (D : V → V → Prop) (C : Finset V) (x y : V) : Finset V := by
  classical
  exact Finset.univ.filter (AncestorOf (arrowGraph D) (EndpointCondition (fun v => v ∈ C) x y))

theorem mem_ancestralVertices (D : V → V → Prop) (C : Finset V) (x y v : V) :
    v ∈ ancestralVertices D C x y ↔
      AncestorOf (arrowGraph D) (EndpointCondition (fun v => v ∈ C) x y) v := by
  classical
  simp only [ancestralVertices, Finset.mem_filter, Finset.mem_univ, true_and]

theorem ancestralVertices_closed (D : V → V → Prop) (C : Finset V) (x y : V) :
    AncestralSet D (ancestralVertices D C x y) := by
  intro parent child edge member
  exact (mem_ancestralVertices D C x y parent).mpr
    (ancestral_parent_closed D _ edge ((mem_ancestralVertices D C x y child).mp member))

def ancestorMoral (D : V → V → Prop) (C : Finset V) (x y : V) : V → V → Prop :=
  MoralStep D (AncestorOf (arrowGraph D) (EndpointCondition (fun v => v ∈ C) x y)) (fun v => v ∈ C)

noncomputable def leftMoralComponent (D : V → V → Prop) (C : Finset V) (x y : V) : Finset V := by
  classical
  exact (ancestralVertices D C x y).filter (fun v => v ∉ C ∧ ∃ vertices, Route (ancestorMoral D C x y) x vertices v)

theorem mem_leftMoralComponent (D : V → V → Prop) (C : Finset V) (x y v : V) :
    v ∈ leftMoralComponent D C x y ↔
      v ∈ ancestralVertices D C x y ∧ v ∉ C ∧ ∃ vertices, Route (ancestorMoral D C x y) x vertices v := by
  classical
  exact Finset.mem_filter

theorem start_in_left_component (D : V → V → Prop) (C : Finset V) (x y : V) (outside : x ∉ C) :
    x ∈ leftMoralComponent D C x y := by
  apply (mem_leftMoralComponent D C x y x).mpr
  exact ⟨(mem_ancestralVertices D C x y x).mpr ⟨x, ⟨[], .nil x⟩, Or.inl rfl⟩,
    outside, [], .nil x⟩

theorem finish_not_in_left_component (D : V → V → Prop)
    (acyclic : ∀ a xs, Route D a xs a → xs = []) (C : Finset V) (x y : V)
    (separated : ¬ ActiveConnection (arrowGraph D) (fun v => v ∈ C) x y) :
    y ∉ leftMoralComponent D C x y := by
  intro member
  obtain ⟨vertices, route⟩ := ((mem_leftMoralComponent D C x y y).mp member).2.2
  exact separated (ancestral_moral_route_is_active D acyclic (fun v => v ∈ C) x y route)

theorem family_component_closed (D : V → V → Prop) (C : Finset V) (x y child a b : V)
    (childMember : child ∈ ancestralVertices D C x y)
    («first» : FamilyVertex D child a) (firstIn : a ∈ leftMoralComponent D C x y)
    (second : FamilyVertex D child b) (outside : b ∉ C) :
    b ∈ leftMoralComponent D C x y := by
  classical
  by_cases same : a = b
  · exact same ▸ firstIn
  · have firstFacts := (mem_leftMoralComponent D C x y a).mp firstIn
    have step := family_vertices_morally_adjacent D _ (fun v => v ∈ C)
      ((mem_ancestralVertices D C x y child).mp childMember) «first» second same firstFacts.2.1 outside
    obtain ⟨vertices, route⟩ := firstFacts.2.2
    apply (mem_leftMoralComponent D C x y b).mpr
    exact ⟨(mem_ancestralVertices D C x y b).mpr step.2.1, outside,
      vertices ++ [b], route.append (.cons step (.nil b))⟩

noncomputable def leftFactorVertices (D : V → V → Prop) (C : Finset V) (x y : V) : Finset V := by
  classical
  exact (ancestralVertices D C x y).filter
    (fun child => ∃ v, FamilyVertex D child v ∧ v ∈ leftMoralComponent D C x y)

noncomputable def rightMoralVertices (D : V → V → Prop) (C : Finset V) (x y : V) : Finset V :=
  ancestralVertices D C x y \ (C ∪ leftMoralComponent D C x y)

theorem clamped_left_factor_depends (D : V → V → Prop) (θ : Coordinate D → ℚ)
    (C : Finset V) (x y : V) (base : Assignment V) (child : V)
    (member : child ∈ leftFactorVertices D C x y) :
    DependsOn (leftMoralComponent D C x y) (clampedFactor D θ C base child) := by
  classical
  obtain ⟨childMember, a, familyA, inLeft⟩ := Finset.mem_filter.mp member
  apply clamped_factor_depends
  intro b familyB outside
  exact family_component_closed D C x y child a b childMember familyA inLeft familyB outside

theorem clamped_right_factor_depends (D : V → V → Prop) (θ : Coordinate D → ℚ)
    (C : Finset V) (x y : V) (base : Assignment V) (child : V)
    (member : child ∈ ancestralVertices D C x y \ leftFactorVertices D C x y) :
    DependsOn (rightMoralVertices D C x y) (clampedFactor D θ C base child) := by
  classical
  have childMember := (Finset.mem_sdiff.mp member).1
  have noLeft := (Finset.mem_sdiff.mp member).2
  apply clamped_factor_depends
  intro v family outside
  have vAncestral : v ∈ ancestralVertices D C x y := by
    rcases family with atChild | parent
    · exact atChild.symm ▸ childMember
    · exact ancestralVertices_closed D C x y v child parent childMember
  have notLeft : v ∉ leftMoralComponent D C x y := by
    intro inLeft
    apply noLeft
    exact Finset.mem_filter.mpr ⟨childMember, v, family, inLeft⟩
  exact Finset.mem_sdiff.mpr ⟨vAncestral, by
    intro inUnion
    rcases Finset.mem_union.mp inUnion with inC | inL
    · exact outside inC
    · exact notLeft inL⟩

theorem clamped_ancestral_product_factors (D : V → V → Prop) (θ : Coordinate D → ℚ)
    (C : Finset V) (x y : V) (base : Assignment V) :
    ∃ F G : Assignment V → ℚ,
      DependsOn (leftMoralComponent D C x y) F ∧ DependsOn (rightMoralVertices D C x y) G ∧
      (fun w => partialJointMass D θ (ancestralVertices D C x y) (clampCondition C base w)) =
        (fun w => F w * G w) := by
  classical
  let P := leftFactorVertices D C x y
  let A := ancestralVertices D C x y
  let F : Assignment V → ℚ := fun w => ∏ child ∈ P, clampedFactor D θ C base child w
  let G : Assignment V → ℚ := fun w => ∏ child ∈ A \ P, clampedFactor D θ C base child w
  refine ⟨F, G, ?_, ?_, ?_⟩
  · exact finite_product_depends P _ _ (clamped_left_factor_depends D θ C x y base)
  · exact finite_product_depends (A \ P) _ _ (clamped_right_factor_depends D θ C x y base)
  · funext w
    have subset : P ⊆ A := fun child member => (Finset.mem_filter.mp member).1
    have «split» := Finset.prod_sdiff (f := fun child => clampedFactor D θ C base child w) subset
    change (∏ child ∈ A, clampedFactor D θ C base child w) = _
    exact «split».symm.trans (mul_comm _ _)

end RestrictedCausal.ProbabilitySource.BinaryCPT
