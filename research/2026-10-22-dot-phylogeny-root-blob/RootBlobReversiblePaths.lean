import RootBlobRetainedPortSemantics

/-!
# Arbitrary-edge reversible tree marginals, retaining original occurrences

Author: dot (OpenAI), 23 October 2026.
UNELABORATED SOURCE ONLY. No compiler, runtime, or kernel check was run.
API baseline: mathlib 0df444a360eaa60ab8c11dca51a86af692955474.

This is the missing arbitrary-edge path semantics for the literal Fourier
and CT-K2P joins. It does NOT identify either restricted domain with the
open H-equivariant domain. Every path below is constructed before matrices
are assigned and contains original selected incoming-edge occurrences.

The matrix order is real: detailed balance moves a left terminal edge to
the LEFT of the remaining path product. No commutation hypothesis is used.
-/

open scoped BigOperators
open RootBlobInterfaces RootBlobTreeMarginals
namespace RootBlobReversiblePaths
universe u v w
variable {S : Type u} [Fintype S] [DecidableEq S]

def identityMatrix : Mat S := fun i j => if i = j then 1 else 0

theorem matMul_identity (A : Mat S) : matMul A identityMatrix = A := by
  classical
  funext i j
  simp [matMul, identityMatrix]

theorem identity_matMul (A : Mat S) : matMul identityMatrix A = A := by
  classical
  funext i j
  simp [matMul, identityMatrix]

theorem matMul_assoc (A B C : Mat S) :
    matMul (matMul A B) C = matMul A (matMul B C) := by
  funext i j
  simp only [matMul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- A fold-right helper, proved equal to the original fold-left matProduct. -/
noncomputable def product : List (Mat S) → Mat S
  | [] => identityMatrix
  | A :: L => matMul A (product L)

theorem foldl_product (L : List (Mat S)) (A : Mat S) :
    L.foldl matMul A = matMul A (product L) := by
  induction L generalizing A with
  | nil => exact (matMul_identity A).symm
  | cons B L ih =>
    change L.foldl matMul (matMul A B) = matMul A (matMul B (product L))
    rw [ih, matMul_assoc]

theorem product_eq_matProduct (L : List (Mat S)) : product L = matProduct L := by
  unfold matProduct
  change product L = L.foldl matMul identityMatrix
  rw [foldl_product, identity_matMul]

theorem product_append (L R : List (Mat S)) :
    product (L ++ R) = matMul (product L) (product R) := by
  induction L with
  | nil => exact (identity_matMul (product R)).symm
  | cons A L ih =>
    change matMul A (product (L ++ R)) =
      matMul (matMul A (product L)) (product R)
    rw [ih, matMul_assoc]

theorem product_singleton (A : Mat S) : product [A] = A := matMul_identity A

def RowNormalized (A : Mat S) : Prop := ∀ i, (∑ j, A i j) = 1

def Reversible (μ : S → ℝ) (A : Mat S) : Prop :=
  ∀ i j, μ i * A i j = μ j * A j i

theorem stationary_of_reversible (μ : S → ℝ) (A : Mat S)
    (hrow : RowNormalized A) (hrev : Reversible μ A) (j : S) :
    (∑ i, μ i * A i j) = μ j := by
  calc
    (∑ i, μ i * A i j) = ∑ i, μ j * A j i := by
      apply Finset.sum_congr rfl
      intro i _
      exact hrev i j
    _ = μ j := by rw [← Finset.mul_sum, hrow, mul_one]

namespace ParentTree
variable {V : Type v} [Fintype V] [DecidableEq V]
variable (T : RootBlobTreeMarginals.ParentTree V)

/-- Actual right-terminal contraction, with the remaining pair orientation
unchanged. This follows from the already written assignment-sum elimination. -/
theorem joint_other_leaf [Nonempty S]
    (v : T.NR) (hv : T.IsLeaf v.val) (μ : S → ℝ) (K : T.NR → Mat S)
    (a : {a : V // a ≠ v.val}) :
    T.joint μ K a.val v.val = fun i j =>
      ∑ k, (T.prune v hv).joint μ (T.prunedMatrices v hv K)
        a ⟨T.parent v, hv v⟩ i k * K v k j := by
  funext i j
  rw [T.joint_swap, T.joint_leaf_other v hv μ K a]
  apply Finset.sum_congr rfl
  intro k _
  rw [(T.prune v hv).joint_swap]

/-- Graph-only path with a fully derived arbitrary-edge joint law. Row sums
and detailed balance are assumptions on actual edge matrices, not a replacement
pair oracle. The source certificate is constructed by leaf induction below. -/
structure PathCertificate where
  edges : V → V → List T.NR
  nil_iff : ∀ a b, edges a b = [] ↔ a = b
  formula : ∀ (μ : S → ℝ) (K : T.NR → Mat S),
    (∀ e, RowNormalized (K e)) → (∀ e, Reversible μ (K e)) →
    ∀ a b i j, T.joint μ K a b i j =
      μ i * product ((edges a b).map K) i j

theorem pathCertificate_nonempty [Nonempty S] :
    Nonempty (PathCertificate (S := S) T) := by
  classical
  have aux : ∀ n : ℕ, ∀ (U : Type v) [Fintype U] [DecidableEq U]
      (R : RootBlobTreeMarginals.ParentTree U), Fintype.card U = n →
      Nonempty (PathCertificate (S := S) R) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro U _ _ R hcard
      by_cases hn : ∃ q : U, q ≠ R.root
      · obtain ⟨v, hv⟩ := R.exists_nonroot_leaf hn
        let U' := {q : U // q ≠ v.val}
        let R' := R.prune v hv
        let p : U' := ⟨R.parent v, hv v⟩
        have hlt : Fintype.card U' < n := by
          rw [← hcard]
          exact Fintype.card_subtype_lt (by simp : ¬(v.val ≠ v.val))
        obtain ⟨D⟩ := ih (Fintype.card U') hlt U' R' rfl
        let lift : List R'.NR → List R.NR := List.map (R.oldNonroot v hv)
        let path : U → U → List R.NR := fun a b =>
          if ha : a = v.val then
            if hb : b = v.val then [] else v :: lift (D.edges p ⟨b, hb⟩)
          else if hb : b = v.val then lift (D.edges ⟨a, ha⟩ p) ++ [v]
          else lift (D.edges ⟨a, ha⟩ ⟨b, hb⟩)
        have hnil : ∀ a b, path a b = [] ↔ a = b := by
          intro a b
          by_cases ha : a = v.val
          · subst a
            by_cases hb : b = v.val
            · subst b; simp [path]
            · simp [path, hb, Ne.symm hb]
          · by_cases hb : b = v.val
            · subst b; simp [path, ha]
            · simp only [path, dif_neg ha, dif_neg hb]
              change List.map _ (D.edges ⟨a, ha⟩ ⟨b, hb⟩) = [] ↔ a = b
              rw [List.map_eq_nil_iff, D.nil_iff]
              exact Subtype.ext_iff
        refine ⟨⟨path, hnil, ?_⟩⟩
        intro μ K hrow hrev a b i j
        let K' := R.prunedMatrices v hv K
        have hr' : ∀ e, RowNormalized (K' e) := fun e => hrow (R.oldNonroot v hv e)
        have hv' : ∀ e, Reversible μ (K' e) := fun e => hrev (R.oldNonroot v hv e)
        have hm : ∀ L, (lift L).map K = L.map K' := by
          intro L
          simp [lift, K', RootBlobTreeMarginals.ParentTree.prunedMatrices, List.map_map]
        by_cases ha : a = v.val
        · subst a
          by_cases hb : b = v.val
          · subst b
            rw [R.joint_leaf_self v hv μ K]
            have hpp : ∀ k, R'.joint μ K' p p k k = μ k := by
              intro k
              rw [D.formula μ K' hr' hv', (D.nil_iff p p).mpr rfl]
              simp [product, identityMatrix]
            change (if i = j then ∑ k, R'.joint μ K' p p k k * K v k i else 0) = _
            simp_rw [hpp]
            rw [stationary_of_reversible μ (K v) (hrow v) (hrev v)]
            by_cases hij : i = j <;> simp [path, product, identityMatrix, hij]
          · rw [R.joint_leaf_other v hv μ K ⟨b, hb⟩]
            change (∑ k, R'.joint μ K' p ⟨b, hb⟩ k j * K v k i) = _
            simp_rw [D.formula μ K' hr' hv']
            simp only [path, dif_pos rfl, dif_neg hb, List.map_cons, product, hm]
            rw [matMul, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            calc
              (μ k * product ((D.edges p ⟨b, hb⟩).map K') k j) * K v k i =
                  (μ k * K v k i) * product ((D.edges p ⟨b, hb⟩).map K') k j := by ring
              _ = _ := by rw [hrev v k i]; ring
        · by_cases hb : b = v.val
          · subst b
            rw [joint_other_leaf R v hv μ K ⟨a, ha⟩]
            change (∑ k, R'.joint μ K' ⟨a, ha⟩ p i k * K v k j) = _
            simp_rw [D.formula μ K' hr' hv']
            simp only [path, dif_neg ha, dif_pos rfl, List.map_append, List.map_cons,
              List.map_nil, product_append, product_singleton, hm]
            rw [matMul, Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _
            ring
          · rw [R.joint_keep_leaf v hv μ K (hrow v) ⟨a, ha⟩ ⟨b, hb⟩]
            change R'.joint μ K' ⟨a, ha⟩ ⟨b, hb⟩ i j = _
            rw [D.formula μ K' hr' hv']
            simp only [path, dif_neg ha, dif_neg hb, hm]
      · have hs : ∀ q : U, q = R.root := by
          intro q
          by_contra hq
          exact hn ⟨q, hq⟩
        refine ⟨⟨fun _ _ => [], ?_, ?_⟩⟩
        · intro a b
          constructor
          · intro _; exact (hs a).trans (hs b).symm
          · intro _; rfl
        · intro μ K hrow hrev a b i j
          rw [R.joint_singleton hs μ K a b, stationaryPair_one]
          by_cases hij : i = j <;> simp [product, identityMatrix, hij]
  exact aux (Fintype.card V) V T rfl

noncomputable def pathCertificate [Nonempty S] : PathCertificate (S := S) T :=
  Classical.choice (pathCertificate_nonempty T)

end ParentTree

namespace Network
open RootBlobRetainedPortSemantics
variable {V : Type v} [Fintype V] [DecidableEq V]
variable {E : Type w} [Fintype E]
variable (N : RootBlobEdgeIndexed.Network V E (Fin 2))

/-- Begin at the real terminal port, using its selected incoming edge;
the remaining ordered list is computed in the actual pruned parent tree.
Mapping back selects ORIGINAL edge occurrences, not freely copied factors. -/
noncomputable def portEdges [Nonempty S] (hN : PortAdmitted N)
    (σ : RootBlobSwitching.Switching N) : List E :=
  (σ (firstVertex N hN σ)).val ::
    ((ParentTree.pathCertificate (S := S) (prunedTree N hN σ)).edges
      (parentPort N hN σ) (secondVertex N hN)).map
      (fun e => (σ ((selectedTree N hN σ).oldNonroot
        (firstVertex N hN σ) (firstLeaf N hN σ) e)).val)

theorem portEdges_nonempty [Nonempty S] (hN : PortAdmitted N)
    (σ : RootBlobSwitching.Switching N) : portEdges (S := S) N hN σ ≠ [] := by
  simp [portEdges]

theorem portEdges_long_iff [Nonempty S] (hN : PortAdmitted N)
    (σ : RootBlobSwitching.Switching N) :
    2 ≤ (portEdges (S := S) N hN σ).length ↔
      parentPort N hN σ ≠ secondVertex N hN := by
  classical
  let D := ParentTree.pathCertificate (S := S) (prunedTree N hN σ)
  have hnil := D.nil_iff (parentPort N hN σ) (secondVertex N hN)
  have hlen := List.length_pos_iff (l := D.edges (parentPort N hN σ) (secondVertex N hN))
  simp only [portEdges, List.length_cons, List.length_map]
  change 2 ≤ (D.edges (parentPort N hN σ) (secondVertex N hN)).length + 1 ↔ _
  rw [show (2 ≤ (D.edges (parentPort N hN σ) (secondVertex N hN)).length + 1) ↔
    0 < (D.edges (parentPort N hN σ) (secondVertex N hN)).length by omega]
  exact hlen.trans (not_congr hnil)

theorem resolved_pair_path [Nonempty S] (hN : PortAdmitted N)
    (σ : RootBlobSwitching.Switching N) (μ : S → ℝ) (M : E → Mat S)
    (hrow : ∀ e, RowNormalized (M e)) (hrev : ∀ e, Reversible μ (M e)) :
    RootBlobSwitching.resolvedPair N μ M σ = fun i j =>
      μ i * product ((portEdges (S := S) N hN σ).map M) i j := by
  classical
  let T := selectedTree N hN σ
  let b := firstVertex N hN σ
  let hb := firstLeaf N hN σ
  let a := secondVertex N hN
  let K : T.NR → Mat S := fun v => M (σ v).val
  let K' := T.prunedMatrices b hb K
  let D := ParentTree.pathCertificate (S := S) (prunedTree N hN σ)
  have hr' : ∀ e, RowNormalized (K' e) := fun e => hrow _
  have hv' : ∀ e, Reversible μ (K' e) := fun e => hrev _
  rw [← selectedTree_joint N hN σ]
  change T.joint μ K b.val a.val = _
  rw [T.joint_leaf_other b hb μ K a]
  funext i j
  change (∑ k, (prunedTree N hN σ).joint μ K'
    (parentPort N hN σ) a k j * K b k i) = _
  simp_rw [D.formula μ K' hr' hv']
  simp only [portEdges, List.map_cons, List.map_map, product]
  change (∑ k, (μ k * product ((D.edges (parentPort N hN σ) a).map K') k j) * K b k i) =
    μ i * matMul (K b) (product ((D.edges (parentPort N hN σ) a).map K')) i j
  rw [matMul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  calc
    (μ k * product ((D.edges (parentPort N hN σ) a).map K') k j) * K b k i =
        (μ k * K b k i) * product ((D.edges (parentPort N hN σ) a).map K') k j := by ring
    _ = _ := by rw [hrev (σ b).val k i]; ring

/-- Direct equality of the original network assignment sum and its shared-
parameter path mixture. Every weight is the old product inheritance weight. -/
theorem pairLaw_path_mixture [Nonempty S] (hN : PortAdmitted N)
    (W : E → ℝ) (μ : S → ℝ) (M : E → Mat S)
    (hrow : ∀ e, RowNormalized (M e)) (hrev : ∀ e, Reversible μ (M e)) :
    RootBlobEdgeIndexed.pairLaw N μ W M = fun i j =>
      μ i * ∑ σ : RootBlobSwitching.Switching N,
        RootBlobSwitching.weight N W σ *
          product ((portEdges (S := S) N hN σ).map M) i j := by
  rw [RootBlobSwitching.pairLaw_expansion]
  simp_rw [resolved_pair_path N hN _ μ M hrow hrev]
  funext i j
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro σ _
  ring

/-- The previously derived positive exponent and the new arbitrary-edge
list agree on the precise property needed for strict nucleotide positivity.
No equality of independently chosen whole path certificates is assumed. -/
theorem long_of_positive_exponent [Nonempty S] (hN : PortAdmitted N)
    (σ : RootBlobSwitching.Switching N)
    (h : 0 < pathExponent (S := S) N hN σ) :
    2 ≤ (portEdges (S := S) N hN σ).length := by
  rw [portEdges_long_iff]
  intro he
  have hz := ((prunedTree N hN σ).distanceCertificate (S := S)).zero_iff
    (parentPort N hN σ) (secondVertex N hN)
  have hh : pathExponent (S := S) N hN σ = 0 := hz.mpr he
  omega

end Network

end RootBlobReversiblePaths
