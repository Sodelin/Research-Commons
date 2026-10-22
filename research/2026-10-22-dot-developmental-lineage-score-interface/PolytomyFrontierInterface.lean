/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No compiler/kernel execution or certificate.

An explicit cut/frontier representation of refinement of the root polytomy.
Left/right orientation is quotiented by generated rooted-tree isomorphisms.
The final relation still ranges over all binary topologies, not caterpillars.
An independent graph-edge-contraction/clade-set representation is not defined
or claimed verified in this file.
-/
import PolytomyStarSemantics

namespace PolytomyReductionModel

noncomputable section
universe u v

inductive TreeIso {A : Type u} : BTree A → BTree A → Prop where
  | refl (t : BTree A) : TreeIso t t
  | symm {t u : BTree A} : TreeIso t u → TreeIso u t
  | trans {t u v : BTree A} : TreeIso t u → TreeIso u v → TreeIso t v
  | node {l l' r r' : BTree A} : TreeIso l l' → TreeIso r r' →
      TreeIso (.node l r) (.node l' r')
  | swap (l r : BTree A) : TreeIso (.node l r) (.node r l)

theorem TreeIso.observed_eq {A : Type u} {S : Type v} [DecidableEq S]
    (tip : A → S) {t q : BTree A} (h : TreeIso t q) : observed tip t = observed tip q := by
  induction h with
  | refl t => rfl
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | node hl hr ihl ihr => simp only [observed, ihl, ihr]
  | swap l r => exact Finset.union_comm _ _

theorem TreeIso.starScore_eq {A : Type u} {S : Type v} [DecidableEq S]
    (univ : Finset S) (tip : A → S) {t q : BTree A} (h : TreeIso t q) :
    starScore univ tip t = starScore univ tip q := by
  induction h with
  | refl t => rfl
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | node hl hr ihl ihr =>
      simp only [starScore, ihl, ihr, TreeIso.observed_eq tip hl, TreeIso.observed_eq tip hr]
  | swap l r =>
      simp only [starScore, Finset.union_comm (observed tip l) (observed tip r)]
      omega

theorem TreeIso.mixed_iff {A : Type u} {S : Type v} [DecidableEq S]
    (tip : A → S) {t q : BTree A} (h : TreeIso t q) :
    AllInternalMixed tip t ↔ AllInternalMixed tip q := by
  induction h with
  | refl t => rfl
  | symm h ih => exact ih.symm
  | trans h₁ h₂ ih₁ ih₂ => exact ih₁.trans ih₂
  | node hl hr ihl ihr =>
      simp only [AllInternalMixed, observed, TreeIso.observed_eq tip hl, TreeIso.observed_eq tip hr,
        ihl, ihr]
  | swap l r =>
      simp only [AllInternalMixed, observed,
        Finset.union_comm (observed tip l) (observed tip r)]
      tauto

/-- A cut/frontier whose pieces are the unchanged original block trees.
    `join` traverses an actual cell-tree root; `iso` ignores child orientation.
    The list records block identities, not terminal type labels. -/
inductive BlockFrontier {I : Type u} {A : Type v} (blocks : I → BTree A) :
    BTree A → List I → Prop where
  | block (i : I) : BlockFrontier blocks (blocks i) [i]
  | join {l r : BTree A} {xs ys : List I} :
      BlockFrontier blocks l xs → BlockFrontier blocks r ys →
      BlockFrontier blocks (.node l r) (xs ++ ys)
  | iso {t q : BTree A} {xs : List I} :
      TreeIso t q → BlockFrontier blocks q xs → BlockFrontier blocks t xs

/-- Construct a binary skeleton from a frontier certificate. No ordering or
    shape restriction is imposed on the skeleton. -/
theorem BlockFrontier.has_skeleton {I : Type u} {A : Type v}
    (blocks : I → BTree A) {T : BTree A} {xs : List I}
    (h : BlockFrontier blocks T xs) :
    ∃ t : BTree I, leaves t = xs ∧ TreeIso T (graft blocks t) := by
  induction h with
  | block i => exact ⟨.leaf i, rfl, .refl _⟩
  | join hl hr ihl ihr =>
      obtain ⟨l, hll, hil⟩ := ihl
      obtain ⟨r, hlr, hir⟩ := ihr
      exact ⟨.node l r, by simp only [leaves, hll, hlr], .node hil hir⟩
  | iso hi hf ih =>
      obtain ⟨t, ht, he⟩ := ih
      exact ⟨t, ht, .trans hi he⟩

theorem graft_has_frontier {I : Type u} {A : Type v}
    (blocks : I → BTree A) (t : BTree I) :
    BlockFrontier blocks (graft blocks t) (leaves t) := by
  induction t with
  | leaf i => exact .block i
  | node l r ihl ihr => exact .join ihl ihr

def FrontierRefinement {N m : ℕ} (D : MSSCInstance N m)
    (T : BTree (Cell N m)) : Prop :=
  ∃ xs : List (Block m), xs.Perm (Finset.univ : Finset (Block m)).toList ∧
    BlockFrontier (fixedBlockTree D) T xs

theorem frontierRefinement_iff_graft {N m : ℕ} (D : MSSCInstance N m)
    (T : BTree (Cell N m)) :
    FrontierRefinement D T ↔ ∃ t : BTree (Block m),
      ValidJoiningTree t ∧ TreeIso T (graft (fixedBlockTree D) t) := by
  constructor
  · rintro ⟨xs, hp, hf⟩
    obtain ⟨t, hl, hi⟩ := BlockFrontier.has_skeleton (fixedBlockTree D) hf
    exact ⟨t, by simpa only [ValidJoiningTree, hl] using hp, hi⟩
  · rintro ⟨t, ht, hi⟩
    exact ⟨leaves t, ht, .iso hi (graft_has_frontier _ t)⟩

def FrontierCartaDecision {N m : ℕ} (D : MSSCInstance N m)
    (lambda : ℝ) (K : ℕ) : Prop :=
  ∃ L : StarLabeledTree (Cell N m) (Terminal N m),
    FrontierRefinement D (eraseStar L) ∧ StarFeasible Prod.snd L ∧
      cartaStarScore Prod.snd lambda L ≤ (fixedCost D + K - N : ℕ)

/-- Both directions between actual cut-certified cell trees with compatible
    labels and the entire indexed-graft finite decision problem. -/
theorem frontierCartaDecision_iff_refinementDecision {N m : ℕ}
    (D : MSSCInstance N m) (lambda : ℝ) (K : ℕ) :
    FrontierCartaDecision D lambda K ↔ RefinementDecision D K := by
  constructor
  · rintro ⟨L, hfront, hf, hcost⟩
    obtain ⟨t, ht, hi⟩ := (frontierRefinement_iff_graft D _).mp hfront
    have hm : AllInternalMixed Prod.snd (eraseStar L) :=
      (TreeIso.mixed_iff Prod.snd hi).mpr (every_graft_internal_mixed D t)
    rw [feasible_mixed_score_exact Prod.snd lambda L hf hm,
      TreeIso.starScore_eq Finset.univ Prod.snd hi] at hcost
    refine ⟨t, ht, ?_⟩
    change (fullScore D t : ℝ) ≤ (fixedCost D + K - N : ℕ) at hcost
    exact_mod_cast hcost
  · intro h
    obtain ⟨t, L, ht, he, hf, hcost⟩ :=
      (cartaStarDecision_iff_refinementDecision D lambda K).mpr h
    refine ⟨L, ?_, hf, hcost⟩
    apply (frontierRefinement_iff_graft D _).mpr
    refine ⟨t, ht, ?_⟩
    rw [he]
    exact .refl _

theorem full_frontier_carta_reduction {N m : ℕ} (D : MSSCInstance N m)
    (lambda : ℝ) (K : ℕ) (hN : 0 < N) (hm : 2 ≤ m)
    (hNK : N ≤ K) (hKmN : K ≤ m * N) :
    MSSCDecision D K ↔ FrontierCartaDecision D lambda K := by
  rw [frontierCartaDecision_iff_refinementDecision]
  exact fullReductionClaim N m D K hN hm hNK hKmN

end
end PolytomyReductionModel
