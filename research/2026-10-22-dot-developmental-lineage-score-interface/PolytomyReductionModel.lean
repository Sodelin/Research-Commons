/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No Lean/Lake execution or certificate.

This file declares the actual all-refinement MSSC gadget and target proposition.
It does NOT prove FullReductionClaim or claim formal NP-completeness.
The proposed proved component is exact graft-score decomposition, not a
replacement of the full reduction by a weaker theorem.
No additional axioms or sorry placeholders are introduced.
-/
import Mathlib

namespace PolytomyReductionModel

noncomputable section

universe u v

inductive BTree (A : Type u) where
  | leaf (a : A)
  | node (left right : BTree A)
  deriving DecidableEq

def leaves {A : Type u} : BTree A → List A
  | .leaf a => [a]
  | .node l r => leaves l ++ leaves r

def observed {A : Type u} {S : Type v} [DecidableEq S]
    (tip : A → S) : BTree A → Finset S
  | .leaf a => {tip a}
  | .node l r => observed tip l ∪ observed tip r

def graft {I : Type u} {A : Type v} (blocks : I → BTree A) :
    BTree I → BTree A
  | .leaf i => blocks i
  | .node l r => .node (graft blocks l) (graft blocks r)

def joinedObserved {I : Type u} {S : Type v} [DecidableEq S]
    (B : I → Finset S) : BTree I → Finset S
  | .leaf i => B i
  | .node l r => joinedObserved B l ∪ joinedObserved B r

def starScore {A : Type u} {S : Type v} [DecidableEq S]
    (univ : Finset S) (tip : A → S) : BTree A → ℕ
  | .leaf _ => 0
  | .node l r => starScore univ tip l + starScore univ tip r +
      (univ \ (observed tip l ∪ observed tip r)).card

def joiningScore {I : Type u} {S : Type v} [DecidableEq S]
    (univ : Finset S) (B : I → Finset S) : BTree I → ℕ
  | .leaf _ => 0
  | .node l r => joiningScore univ B l + joiningScore univ B r +
      (univ \ (joinedObserved B l ∪ joinedObserved B r)).card

def blockScoreSum {I : Type u} (cost : I → ℕ) : BTree I → ℕ
  | .leaf i => cost i
  | .node l r => blockScoreSum cost l + blockScoreSum cost r

theorem observed_graft {I : Type u} {A : Type v} {S : Type*}
    [DecidableEq S] (tip : A → S) (blocks : I → BTree A) (t : BTree I) :
    observed tip (graft blocks t) =
      joinedObserved (fun i => observed tip (blocks i)) t := by
  induction t with
  | leaf i => rfl
  | node l r ihl ihr =>
      simp only [graft, observed, joinedObserved, ihl, ihr]

theorem star_graft_score {I : Type u} {A : Type v} {S : Type*}
    [DecidableEq S] (univ : Finset S) (tip : A → S)
    (blocks : I → BTree A) (t : BTree I) :
    starScore univ tip (graft blocks t) =
      blockScoreSum (fun i => starScore univ tip (blocks i)) t +
      joiningScore univ (fun i => observed tip (blocks i)) t := by
  induction t with
  | leaf i => simp [graft, starScore, blockScoreSum, joiningScore]
  | node l r ihl ihr =>
      simp only [graft, starScore, blockScoreSum, joiningScore,
        observed_graft, ihl, ihr]
      omega

inductive IsCaterpillar {A : Type u} : BTree A → Prop where
  | leaf (a : A) : IsCaterpillar (.leaf a)
  | extend {t : BTree A} (h : IsCaterpillar t) (a : A) :
      IsCaterpillar (.node t (.leaf a))

def support {A : Type u} [DecidableEq A] (t : BTree A) : Finset A :=
  (leaves t).toFinset

def mergeScore {A : Type u} [DecidableEq A]
    (f : Finset A → ℕ) : BTree A → ℕ
  | .leaf _ => 0
  | .node l r => mergeScore f l + mergeScore f r +
      f (support l ∪ support r)

/-- Full structural lemma still to be formalized; this is a proposition,
    not an axiom or an accepted proof. Permutation retains every block. -/
def CaterpillarLemmaClaim : Prop :=
  ∀ (A : Type) [DecidableEq A] (f : Finset A → ℕ),
    (∀ J K, J ⊆ K → f K ≤ f J) →
    ∀ t : BTree A, ∃ c : BTree A,
      (leaves c).Perm (leaves t) ∧ IsCaterpillar c ∧
      mergeScore f c ≤ mergeScore f t

structure MSSCInstance (N m : ℕ) where
  sets : Fin m → Finset (Fin N)
  covers : ∀ x : Fin N, ∃ i : Fin m, x ∈ sets i

def firstCover {N m : ℕ} (D : MSSCInstance N m)
    (order : List (Fin m)) (x : Fin N) : ℕ :=
  (order.takeWhile (fun i => decide (x ∉ D.sets i))).length + 1

def msscCost {N m : ℕ} (D : MSSCInstance N m)
    (order : List (Fin m)) : ℕ :=
  ∑ x : Fin N, firstCover D order x

def MSSCDecision {N m : ℕ} (D : MSSCInstance N m) (K : ℕ) : Prop :=
  ∃ order : List (Fin m),
    order.Perm (Finset.univ : Finset (Fin m)).toList ∧ msscCost D order ≤ K

def privateCount (N m : ℕ) : ℕ := m * N + 1
abbrev Terminal (N m : ℕ) := Sum (Fin N) (Sum (Fin (privateCount N m)) (Fin 2))
abbrev Block (m : ℕ) := Option (Fin m)
abbrev Cell (N m : ℕ) := Block m × Terminal N m

def marker0 (N m : ℕ) : Terminal N m := Sum.inr (Sum.inr 0)

def markers (N m : ℕ) : Finset (Terminal N m) :=
  (Finset.univ : Finset (Fin 2)).image (fun x => Sum.inr (Sum.inr x))

def blockTypes {N m : ℕ} (D : MSSCInstance N m) :
    Block m → Finset (Terminal N m)
  | none =>
      (Finset.univ : Finset (Fin (privateCount N m))).image
        (fun z => Sum.inr (Sum.inl z)) ∪ markers N m
  | some i => (D.sets i).image Sum.inl ∪ markers N m

def combFrom {A : Type u} (start : A) (rest : List A) : BTree A :=
  rest.foldl (fun t a => BTree.node t (BTree.leaf a)) (BTree.leaf start)

def blockCells {N m : ℕ} (D : MSSCInstance N m) (b : Block m) :
    List (Cell N m) :=
  ((blockTypes D b).toList).map (fun s => (b,s))

def fixedBlockTree {N m : ℕ} (D : MSSCInstance N m) (b : Block m) :
    BTree (Cell N m) :=
  let xs := blockCells D b
  combFrom (xs.headD (b, marker0 N m)) xs.tail

def fullScore {N m : ℕ} (D : MSSCInstance N m) (t : BTree (Block m)) : ℕ :=
  starScore Finset.univ Prod.snd (graft (fixedBlockTree D) t)

def fixedCost {N m : ℕ} (D : MSSCInstance N m) : ℕ :=
  ∑ b : Block m, starScore Finset.univ Prod.snd (fixedBlockTree D b)

def ValidJoiningTree {m : ℕ} (t : BTree (Block m)) : Prop :=
  (leaves t).Perm (Finset.univ : Finset (Block m)).toList

/-- Quantifies over every binary joining topology, not a chosen caterpillar
    or a disjoint-triple subproblem. Grafting retains all original blocks. -/
def RefinementDecision {N m : ℕ} (D : MSSCInstance N m) (K : ℕ) : Prop :=
  ∃ t : BTree (Block m), ValidJoiningTree t ∧
    fullScore D t ≤ fixedCost D + K - N

/-- The complete finite mathematical reduction target. UNPROVED in this file.
    Polynomial encoding bounds and classical NP-hardness are separate tasks. -/
def FullReductionClaim : Prop :=
  ∀ (N m : ℕ) (D : MSSCInstance N m) (K : ℕ),
    0 < N → 2 ≤ m → N ≤ K → K ≤ m * N →
    (MSSCDecision D K ↔ RefinementDecision D K)

/- Remaining proof obligations, not supplied as assumptions:
1. blockCells is nonempty, nodup, with exactly the declared block types;
   fixedBlockTree preserves these cells, all internal descendants are mixed.
2. ValidJoiningTree grafts are exactly binary refinements of the one-polytomy
   input with these fixed blocks; all star-map internal labels are forced.
3. Prove CaterpillarLemmaClaim by the q-1-node flattening comparison.
4. Derive the missing-type first-position sum for each caterpillar.
5. Prove the H=m*N+1 anchor exclusion and first-two swap invariance.
6. Derive both directions of FullReductionClaim with the natural-number
   threshold subtraction justified by N <= K; no optimum oracle is assumed.
7. Give polynomial encoding/size bounds and an NP certificate checker.
8. Formalize the separate general-DAG full-score subset recurrence and its
   correctness/complexity, rather than treating it as this star special case.
-/

end

end PolytomyReductionModel
