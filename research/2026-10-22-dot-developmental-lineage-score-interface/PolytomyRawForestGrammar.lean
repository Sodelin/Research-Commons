/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

The original tree token grammar, with the TWO original unary cell fields
retained. This layer checks syntax only, not dimension/range, uniqueness,
clades or score. It accepts arbitrary binary tree shapes, never only combs.
The complete independent original verifier remains the downstream target.
-/
import PolytomySaturatingDecoderMachine
import PolytomyBinaryFrameMachine

namespace PolytomyReductionModel

def rawCellTreeBits : BTree (ℕ × ℕ) → List Bool
  | .leaf a => true :: (unaryFrame a.1 ++ unaryFrame a.2)
  | .node l r => false :: (rawCellTreeBits l ++ rawCellTreeBits r)

def rawForestWord (ts : List (BTree (ℕ × ℕ))) : List Bool :=
  ts.flatMap rawCellTreeBits

def rawForestNodes (ts : List (BTree (ℕ × ℕ))) : ℕ :=
  (ts.map vertexCount).sum

/-- Fuel is proof-side recursion only. The concrete machine below stores
    the pending-slot count physically and does not have this fuel register. -/
def rawForestSkip : ℕ → ℕ → List Bool → Option (List Bool)
  | _, 0, bits => some bits
  | 0, _ + 1, _ => none
  | _ + 1, _ + 1, [] => none
  | fuel + 1, q + 1, false :: bits => rawForestSkip fuel (q + 2) bits
  | fuel + 1, q + 1, true :: bits =>
      match readUnaryFrame bits with
      | none => none
      | some (_, afterBlock) =>
          match readUnaryFrame afterBlock with
          | none => none
          | some (_, afterType) => rawForestSkip fuel q afterType

theorem rawCellTree_vertex_pos (T : BTree (ℕ × ℕ)) : 0 < vertexCount T := by
  cases T <;> simp [vertexCount]

theorem rawCellTree_vertex_bound (T : BTree (ℕ × ℕ)) :
    vertexCount T ≤ (rawCellTreeBits T).length := by
  induction T with
  | leaf a => simp [vertexCount, rawCellTreeBits, unaryFrame]
  | node l r ihl ihr =>
      simp only [vertexCount, rawCellTreeBits, List.length_cons, List.length_append]
      omega

theorem rawForestNodes_word_bound (ts : List (BTree (ℕ × ℕ))) :
    rawForestNodes ts ≤ (rawForestWord ts).length := by
  induction ts with
  | nil => simp [rawForestNodes, rawForestWord]
  | cons t ts ih =>
      have ht := rawCellTree_vertex_bound t
      simp only [rawForestNodes, List.map_cons, List.sum_cons, rawForestWord,
        List.flatMap_cons, List.length_append] at *
      omega

theorem rawForestSkip_encode (fuel : ℕ) :
    ∀ (ts : List (BTree (ℕ × ℕ))) (rest : List Bool),
      rawForestNodes ts ≤ fuel →
      rawForestSkip fuel ts.length (rawForestWord ts ++ rest) = some rest := by
  induction fuel with
  | zero =>
      intro ts rest hf
      cases ts with
      | nil => simp [rawForestWord, rawForestSkip]
      | cons t ts =>
          have ht := rawCellTree_vertex_pos t
          simp only [rawForestNodes, List.map_cons, List.sum_cons] at hf
          omega
  | succ fuel ih =>
      intro ts rest hf
      cases ts with
      | nil => simp [rawForestWord, rawForestSkip]
      | cons t ts =>
          cases t with
          | leaf a =>
              have hsmall : rawForestNodes ts ≤ fuel := by
                simp only [rawForestNodes, List.map_cons, List.sum_cons, vertexCount] at hf ⊢
                omega
              simpa [rawForestWord, rawCellTreeBits, rawForestSkip, List.append_assoc,
                readUnaryFrame_encode] using ih ts rest hsmall
          | node l r =>
              have hsmall : rawForestNodes (l :: r :: ts) ≤ fuel := by
                simp only [rawForestNodes, List.map_cons, List.sum_cons, vertexCount] at hf ⊢
                omega
              simpa [rawForestWord, rawCellTreeBits, rawForestSkip, List.append_assoc,
                Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
                ih (l :: r :: ts) rest hsmall

theorem rawForestSkip_sound (fuel q : ℕ) (bits rest : List Bool)
    (h : rawForestSkip fuel q bits = some rest) :
    ∃ ts : List (BTree (ℕ × ℕ)), ts.length = q ∧ bits = rawForestWord ts ++ rest := by
  induction fuel generalizing q bits rest with
  | zero =>
      cases q with
      | zero =>
          have he : bits = rest := by simpa [rawForestSkip] using h
          exact ⟨[], rfl, by simpa [rawForestWord] using he⟩
      | succ q => simp [rawForestSkip] at h
  | succ fuel ih =>
      cases q with
      | zero =>
          have he : bits = rest := by simpa [rawForestSkip] using h
          exact ⟨[], rfl, by simpa [rawForestWord] using he⟩
      | succ q =>
          cases bits with
          | nil => simp [rawForestSkip] at h
          | cons b bits =>
              cases b with
              | false =>
                  obtain ⟨ts, hlen, hword⟩ := ih (q + 2) bits rest h
                  cases ts with
                  | nil => simp at hlen
                  | cons l ts =>
                      cases ts with
                      | nil => simp at hlen
                      | cons r ts =>
                          refine ⟨.node l r :: ts, by simp only [List.length_cons] at hlen ⊢; omega, ?_⟩
                          rw [hword]
                          simp [rawForestWord, rawCellTreeBits, List.append_assoc]
              | true =>
                  cases hb : readUnaryFrame bits with
                  | none => simp [rawForestSkip, hb] at h
                  | some pb =>
                      rcases pb with ⟨a, afterBlock⟩
                      cases ht : readUnaryFrame afterBlock with
                      | none => simp [rawForestSkip, hb, ht] at h
                      | some pt =>
                          rcases pt with ⟨b, afterType⟩
                          have hr : rawForestSkip fuel q afterType = some rest := by
                            simpa only [rawForestSkip, hb, ht] using h
                          obtain ⟨ts, hlen, hword⟩ := ih q afterType rest hr
                          refine ⟨.leaf (a, b) :: ts, by simp [hlen], ?_⟩
                          rw [readUnaryFrame_decomposition bits a afterBlock hb,
                            readUnaryFrame_decomposition afterBlock b afterType ht, hword]
                          simp [rawForestWord, rawCellTreeBits, List.append_assoc]

/-- Exact all-word grammar statement. The suffix is not silently discarded.
    Range and target/certificate predicates deliberately remain separate. -/
theorem rawForestSkip_all_words (bits rest : List Bool) (q : ℕ) :
    rawForestSkip bits.length q bits = some rest ↔
      ∃ ts : List (BTree (ℕ × ℕ)), ts.length = q ∧ bits = rawForestWord ts ++ rest := by
  constructor
  · exact rawForestSkip_sound bits.length q bits rest
  · rintro ⟨ts, hlen, hword⟩
    have hb := rawForestNodes_word_bound ts
    have hf : rawForestNodes ts ≤ bits.length := by
      rw [hword, List.length_append]
      omega
    rw [← hlen, hword]
    exact rawForestSkip_encode _ ts rest (by simpa only [hword] using hf)

def rawTreeCodes {N m : ℕ} : BTree (Cell N m) → BTree (ℕ × ℕ)
  | .leaf a => .leaf (blockCode a.1, terminalCode N m a.2)
  | .node l r => .node (rawTreeCodes l) (rawTreeCodes r)

theorem rawTreeCodes_bits {N m : ℕ} (T : BTree (Cell N m)) :
    rawCellTreeBits (rawTreeCodes T) = treeBits T := by
  induction T with
  | leaf a => rfl
  | node l r ihl ihr => simp only [rawTreeCodes, rawCellTreeBits, treeBits, ihl, ihr]

theorem rawForestSkip_typed_tree {N m : ℕ} (T : BTree (Cell N m)) (rest : List Bool) :
    rawForestSkip (treeBits T ++ rest).length 1 (treeBits T ++ rest) = some rest := by
  apply (rawForestSkip_all_words _ _ _).mpr
  refine ⟨[rawTreeCodes T], rfl, ?_⟩
  simp [rawForestWord, rawTreeCodes_bits]

/-- Parseable suffixes are NOT necessarily actual tree-node positions.
    The second bit here belongs to the first leaf's unary block field. -/
theorem rawTree_spurious_suffix :
    (rawCellTreeBits (.leaf (1, 0))).drop 1 = rawCellTreeBits (.leaf (0, 0)) ∧
      rawForestSkip 3 1 [true, false, false] = some [] := by
  constructor <;> rfl

end PolytomyReductionModel
