import ColliderMinimalActivePaths
import ClosestFirstArrowGeometry

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Actual first-hit prefixes and shortest activation-branch distance facts for
the binary witness. These are not the missing main-path/branch or
branch/branch exclusion theorem; those still require the actual active
splices and collider-count/potential comparison.
-/

namespace RestrictedCausal.SelectedWalk.Route

universe u

theorem acyclic_trace_nodup {V : Type u} {R : V → V → Prop}
    (acyclic : ∀ a xs, Route R a xs a → xs = [])
    {a b : V} {xs : List V} (route : Route R a xs b) : (a :: xs).Nodup := by
  induction route with
  | nil a => exact List.nodup_singleton a
  | @cons a «next» b rest edge tail ih =>
      refine List.Nodup.cons ?_ ih
      intro repeated
      obtain ⟨front, «prefix»⟩ := tail.prefix_of_mem repeated
      have «impossible» := acyclic a («next» :: front) (.cons edge «prefix»)
      cases «impossible»

/-- The prefix ends at the FIRST hit after the initial vertex. It records
the literal full trace and excludes every earlier new vertex from P. -/
theorem first_hit_after_start {V : Type u} {R : V → V → Prop}
    (P : V → Prop) {a b : V} {xs : List V} (route : Route R a xs b)
    (hit : ∃ v ∈ xs, P v) :
    ∃ v front back, xs = front ++ (v :: back) ∧
      Route R a (front ++ [v]) v ∧ Route R v back b ∧ P v ∧
      ∀ w ∈ front, ¬ P w := by
  classical
  revert hit
  induction route with
  | nil a => intro hit; obtain ⟨v, «impossible», _⟩ := hit; cases «impossible»
  | @cons a «next» b rest edge tail ih =>
      intro hit
      by_cases nextHit : P «next»
      · exact ⟨«next», [], rest, rfl, .cons edge (.nil «next»), tail, nextHit,
          fun _ «impossible» => by cases «impossible»⟩
      · have later : ∃ v ∈ rest, P v := by
          obtain ⟨v, member, satisfies⟩ := hit
          rcases List.mem_cons.mp member with same | member
          · subst v; exact (nextHit satisfies).elim
          · exact ⟨v, member, satisfies⟩
        obtain ⟨v, front, back, «trace», «prefix», suffix, satisfies, «first»⟩ := ih later
        refine ⟨v, «next» :: front, back, ?_, .cons edge «prefix», suffix, satisfies, ?_⟩
        · simpa only [List.cons_append, «trace»]
        · intro w member
          rcases List.mem_cons.mp member with same | member
          · simpa only [same] using nextHit
          · exact «first» w member

end RestrictedCausal.SelectedWalk.Route

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation

universe u

theorem minimum_directed_suffix_at_split {V : Type u} (G : MarkedGraph V)
    (C : V → Prop) {a v finish : V} {front back : List V}
    (whole : MinimumDirectedPath G C a (front ++ back) finish)
    («prefix» : Route (Directed G) a front v)
    (suffix : Route (Directed G) v back finish) :
    MinimumDirectedPath G C v back finish := by
  refine ⟨suffix, whole.endpoint, ?_⟩
  intro last alternative route conditioned
  have bound := whole.minimal last (front ++ alternative) («prefix».append route) conditioned
  simp only [List.length_append] at bound
  omega

theorem minimum_directed_distance_at_split {V : Type u} (G : MarkedGraph V)
    (C : V → Prop) {a v finish : V} {front back : List V}
    (whole : MinimumDirectedPath G C a (front ++ back) finish)
    («prefix» : Route (Directed G) a front v)
    (suffix : Route (Directed G) v back finish) :
    directedDistance G C a = front.length + directedDistance G C v := by
  rw [minimum_directed_distance_eq G C whole,
    minimum_directed_distance_eq G C (minimum_directed_suffix_at_split G C whole «prefix» suffix)]
  simp only [List.length_append]

theorem minimum_directed_distance_strict_after_prefix {V : Type u} (G : MarkedGraph V)
    (C : V → Prop) {a v finish : V} {front back : List V}
    (whole : MinimumDirectedPath G C a (front ++ back) finish)
    («prefix» : Route (Directed G) a front v)
    (suffix : Route (Directed G) v back finish) (positive : front ≠ []) :
    directedDistance G C v < directedDistance G C a := by
  have length := minimum_directed_distance_at_split G C whole «prefix» suffix
  have nonzero : front.length ≠ 0 := by
    intro zero
    exact positive (List.length_eq_zero.mp zero)
  omega

theorem minimum_directed_condition_only_at_end {V : Type u} (G : MarkedGraph V)
    (C : V → Prop) {a v finish : V} {xs : List V}
    (path : MinimumDirectedPath G C a xs finish) (member : v ∈ a :: xs)
    (notEnd : v ≠ finish) : ¬ C v := by
  intro conditioned
  obtain ⟨front, back, «trace», «prefix», suffix⟩ := path.route.split_at_mem member
  have bound := path.minimal v front «prefix» conditioned
  rw [«trace», List.length_append] at bound
  have zero : back.length = 0 := by omega
  have empty : back = [] := List.length_eq_zero.mp zero
  subst back
  cases suffix
  exact notEnd rfl

end RestrictedCausal.VertexActivePaths
