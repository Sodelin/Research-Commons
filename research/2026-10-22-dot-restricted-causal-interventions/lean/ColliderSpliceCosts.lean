import SafeDirectedBranches

/-!
Author: dot (OpenAI), 2026-10-23.
SOURCE-ONLY CANDIDATE. No elaboration or execution.

Literal-list cost estimates for the active-path binary witness. Unlike a
shortest-length argument, a branch replacement may be arbitrarily long.
Its interior has no colliders, so only its final join can add a collider.
The exact common prefix/suffix costs suffice: the old path pays for b,
whereas the new path pays at most for v. The actual splice and exclusion
geometry are not assumed by ColliderMinimal and remain separate suppliers.
Classical atomic-completeness attribution: Meek (1995), Lemmas 9 and 11.
-/

namespace RestrictedCausal.VertexActivePaths

open SelectedWalk CanonicalSelection LatentRoots InducingSeparation
open DiscriminatingStatus WeakInducing

universe u

def tripleCost {V : Type u} (f : V → V → V → Nat) : List V → Nat
  | a :: b :: c :: xs => f a b c + tripleCost f (b :: c :: xs)
  | _ => 0

noncomputable def weightedColliders {V : Type u} (G : MarkedGraph V)
    (w : V → Nat) : List V → Nat :=
  tripleCost (fun a b c => @ite Nat (Collider G a b c) (Classical.propDecidable _) (w b) 0)

theorem tripleCost_cons_le {V : Type u} (f : V → V → V → Nat)
    (a : V) (xs : List V) : tripleCost f xs ≤ tripleCost f (a :: xs) := by
  cases xs with
  | nil => exact Nat.le_refl _
  | cons b xs =>
      cases xs with
      | nil => exact Nat.le_refl _
      | cons c rest => change tripleCost f (b :: c :: rest) ≤ f a b c + _; omega

theorem tripleCost_suffix_le {V : Type u} (f : V → V → V → Nat)
    («left» «right» : List V) : tripleCost f «right» ≤ tripleCost f («left» ++ «right») := by
  induction «left» with
  | nil => exact Nat.le_refl _
  | cons a rest ih => exact ih.trans (tripleCost_cons_le f a (rest ++ «right»))

/-- Splitting at an overlap of two vertices leaves no uncounted triple. -/
theorem tripleCost_append_pair {V : Type u} (f : V → V → V → Nat)
    («left» «right» : List V) (a b : V) :
    tripleCost f («left» ++ a :: b :: «right») =
      tripleCost f («left» ++ [a, b]) + tripleCost f (a :: b :: «right») := by
  induction «left» with
  | nil => simp only [List.nil_append, tripleCost, Nat.zero_add]
  | cons p «left» ih =>
      cases «left» with
      | nil => simp only [List.cons_append, List.nil_append, tripleCost]; omega
      | cons q «left» =>
          cases «left» with
          | nil =>
              simp only [List.cons_append, List.nil_append, tripleCost] at ih ⊢
              omega
          | cons r rest =>
              change f p q r + tripleCost f ((q :: r :: rest) ++ a :: b :: «right») =
                (f p q r + tripleCost f ((q :: r :: rest) ++ [a, b])) +
                  tripleCost f (a :: b :: «right»)
              omega

/-- A one-vertex join contributes at most its center's declared weight. -/
theorem tripleCost_join_le {V : Type u} (f : V → V → V → Nat)
    («left» «right» : List V) (v : V) (bound : Nat)
    (atJoin : ∀ a c, f a v c ≤ bound) :
    tripleCost f («left» ++ v :: «right») ≤
      tripleCost f («left» ++ [v]) + bound + tripleCost f (v :: «right») := by
  induction «left» with
  | nil => simp only [List.nil_append, tripleCost]; omega
  | cons a «left» ih =>
      cases «left» with
      | nil =>
          cases «right» with
          | nil => simp only [List.cons_append, List.nil_append, tripleCost]; omega
          | cons c rest =>
              have atV := atJoin a c
              simp only [List.cons_append, List.nil_append, tripleCost]
              omega
      | cons b «left» =>
          cases «left» with
          | nil =>
              simp only [List.cons_append, List.nil_append, tripleCost] at ih ⊢
              omega
          | cons c rest =>
              change f a b c + tripleCost f ((b :: c :: rest) ++ v :: «right») ≤
                (f a b c + tripleCost f ((b :: c :: rest) ++ [v])) + bound +
                  tripleCost f (v :: «right»)
              omega

theorem weightedColliders_eq_count {V : Type u} (G : MarkedGraph V) (xs : List V) :
    weightedColliders G (fun _ => 1) xs = colliderCount G xs := by
  classical
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      cases xs with
      | nil => rfl
      | cons b xs =>
          cases xs with
          | nil => rfl
          | cons c rest =>
              change (if Collider G a b c then 1 else 0) +
                  weightedColliders G (fun _ => 1) (b :: c :: rest) =
                (if Collider G a b c then 1 else 0) + colliderCount G (b :: c :: rest)
              rw [ih]

theorem weightedColliders_eq_potential {V : Type u} (G : MarkedGraph V)
    (C : V → Prop) (xs : List V) :
    weightedColliders G (directedDistance G C) xs = colliderPotential G C xs := by
  classical
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      cases xs with
      | nil => rfl
      | cons b xs =>
          cases xs with
          | nil => rfl
          | cons c rest =>
              change (if Collider G a b c then directedDistance G C b else 0) +
                  weightedColliders G (directedDistance G C) (b :: c :: rest) =
                (if Collider G a b c then directedDistance G C b else 0) +
                  colliderPotential G C (b :: c :: rest)
              rw [ih]

theorem weightedColliders_zero {V : Type u} (G : MarkedGraph V) (w : V → Nat)
    (xs : List V) (noColliders : AllTriples (fun a b c => ¬ Collider G a b c) xs) :
    weightedColliders G w xs = 0 := by
  classical
  revert noColliders
  induction xs with
  | nil => intro _; rfl
  | cons a xs ih =>
      intro noColliders
      cases xs with
      | nil => rfl
      | cons b xs =>
          cases xs with
          | nil => rfl
          | cons c rest =>
              change (if Collider G a b c then w b else 0) +
                weightedColliders G w (b :: c :: rest) = 0
              rw [if_neg noColliders.1, ih noColliders.2, Nat.zero_add]

/-- The old middle can contain arbitrarily many other colliders. No bound
on its length or on their potentials is needed, since all costs are Nat. -/
theorem weighted_old_splice_lower {V : Type u} (G : MarkedGraph V) (w : V → Nat)
    («left» middle «right» : List V) (a b v : V)
    (atB : ∀ c rest, middle ++ v :: «right» = c :: rest → Collider G a b c) :
    weightedColliders G w («left» ++ [a, b]) + w b + weightedColliders G w (v :: «right») ≤
      weightedColliders G w («left» ++ a :: b :: (middle ++ v :: «right»)) := by
  classical
  unfold weightedColliders
  rw [tripleCost_append_pair (fun a b c => if Collider G a b c then w b else 0)
    «left» (middle ++ v :: «right») a b]
  cases middle with
  | nil =>
      have oldCollider := atB v «right» rfl
      have suffix := tripleCost_suffix_le
        (fun a b c => if Collider G a b c then w b else 0) [b] (v :: «right»)
      simp only [List.nil_append, tripleCost, if_pos oldCollider]
      simp only [List.singleton_append] at suffix
      omega
  | cons c rest =>
      have oldCollider := atB c (rest ++ v :: «right») rfl
      have suffix := tripleCost_suffix_le
        (fun a b c => if Collider G a b c then w b else 0) (b :: c :: rest) (v :: «right»)
      simp only [List.cons_append, tripleCost, if_pos oldCollider]
      simp only [List.cons_append] at suffix
      omega

theorem weighted_new_splice_upper {V : Type u} (G : MarkedGraph V) (w : V → Nat)
    («left» branch «right» : List V) (a b v : V)
    (noColliders : AllTriples (fun p q r => ¬ Collider G p q r)
      (a :: b :: (branch ++ [v]))) :
    weightedColliders G w («left» ++ a :: b :: (branch ++ v :: «right»)) ≤
      weightedColliders G w («left» ++ [a, b]) + w v + weightedColliders G w (v :: «right») := by
  classical
  have zero := weightedColliders_zero G w (a :: b :: (branch ++ [v])) noColliders
  have joined := tripleCost_join_le
    (fun p q r => if Collider G p q r then w q else 0) (a :: b :: branch) «right» v (w v)
    (by intro p r; split_ifs <;> omega)
  change weightedColliders G w (a :: b :: (branch ++ v :: «right»)) ≤
    weightedColliders G w (a :: b :: (branch ++ [v])) + w v +
      weightedColliders G w (v :: «right») at joined
  rw [zero] at joined
  unfold weightedColliders
  rw [tripleCost_append_pair (fun p q r => if Collider G p q r then w q else 0)
    «left» (branch ++ v :: «right») a b]
  change weightedColliders G w («left» ++ [a, b]) +
      weightedColliders G w (a :: b :: (branch ++ v :: «right»)) ≤ _
  omega

/-- Quantitative contradiction after the actual replacement path has been
built. This does not assume branch disjointness, an active splice oracle,
or a faithful distribution. All trace and local-status premises are exposed. -/
theorem collider_minimal_rejects_branch_replacement {V : Type u}
    (G : MarkedGraph V) (C : V → Prop) (x y a b v : V)
    («left» middle branch «right» : List V) {old new : List V}
    (minimal : ColliderMinimal G C x y old) (candidate : Path G C x y new)
    (oldTrace : x :: old = «left» ++ a :: b :: (middle ++ v :: «right»))
    (newTrace : x :: new = «left» ++ a :: b :: (branch ++ v :: «right»))
    (atB : ∀ c rest, middle ++ v :: «right» = c :: rest → Collider G a b c)
    (noColliders : AllTriples (fun p q r => ¬ Collider G p q r)
      (a :: b :: (branch ++ [v])))
    (closer : directedDistance G C v < directedDistance G C b) : False := by
  have oldCount := weighted_old_splice_lower G (fun _ => 1) «left» middle «right» a b v atB
  have newCount := weighted_new_splice_upper G (fun _ => 1) «left» branch «right» a b v noColliders
  simp only [weightedColliders_eq_count] at oldCount newCount
  have bound := minimal.2.1 new candidate
  rw [oldTrace, newTrace] at bound
  have equalCount : colliderCount G (x :: new) = colliderCount G (x :: old) := by
    rw [oldTrace, newTrace]
    omega
  have oldPotential := weighted_old_splice_lower G (directedDistance G C)
    «left» middle «right» a b v atB
  have newPotential := weighted_new_splice_upper G (directedDistance G C)
    «left» branch «right» a b v noColliders
  simp only [weightedColliders_eq_potential] at oldPotential newPotential
  have potentialBound := minimal.2.2 new candidate equalCount
  rw [oldTrace, newTrace] at potentialBound
  omega

end RestrictedCausal.VertexActivePaths
