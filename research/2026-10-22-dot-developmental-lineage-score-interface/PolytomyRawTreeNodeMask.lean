/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Exact legal-node mask for the ORIGINAL arbitrary binary tree grammar.
The specification distinguishes node tokens from unary payload bits.
Its operational logger and the full independent verifier remain separate.
-/
import PolytomyRawForestGrammar
import PolytomyListScanVerifier

namespace PolytomyReductionModel

def rawNodeMask : BTree (ℕ × ℕ) → List Bool
  | .leaf a => true :: List.replicate (a.1 + a.2 + 2) false
  | .node l r => true :: (rawNodeMask l ++ rawNodeMask r)

def rawForestNodeMask (ts : List (BTree (ℕ × ℕ))) : List Bool := ts.flatMap rawNodeMask

def rawMaskPrefix (prefix : List Bool) (r : Option (List Bool × List Bool)) :
    Option (List Bool × List Bool) := r.map (fun p => (p.1, prefix ++ p.2))

theorem rawMaskPrefix_fst (prefix : List Bool) (r : Option (List Bool × List Bool)) :
    (rawMaskPrefix prefix r).map Prod.fst = r.map Prod.fst := by cases r <;> rfl

def rawForestMaskParse : ℕ → ℕ → List Bool → Option (List Bool × List Bool)
  | _, 0, bits => some (bits, [])
  | 0, _ + 1, _ => none
  | _ + 1, _ + 1, [] => none
  | fuel + 1, q + 1, false :: bits =>
      rawMaskPrefix [true] (rawForestMaskParse fuel (q + 2) bits)
  | fuel + 1, q + 1, true :: bits =>
      match readUnaryFrame bits with
      | none => none
      | some (a, afterBlock) =>
          match readUnaryFrame afterBlock with
          | none => none
          | some (b, afterType) =>
              rawMaskPrefix (true :: List.replicate (a + b + 2) false)
                (rawForestMaskParse fuel q afterType)

theorem rawForestMaskParse_fst (fuel q : ℕ) (bits : List Bool) :
    (rawForestMaskParse fuel q bits).map Prod.fst = rawForestSkip fuel q bits := by
  induction fuel generalizing q bits with
  | zero => cases q <;> rfl
  | succ fuel ih =>
      cases q with
      | zero => rfl
      | succ q =>
          cases bits with
          | nil => rfl
          | cons b bits =>
              cases b with
              | false => exact (rawMaskPrefix_fst [true] _).trans (ih (q + 2) bits)
              | true =>
                  cases hb : readUnaryFrame bits with
                  | none => simp [rawForestMaskParse, rawForestSkip, hb]
                  | some pb =>
                      rcases pb with ⟨a, afterBlock⟩
                      cases ht : readUnaryFrame afterBlock with
                      | none => simp [rawForestMaskParse, rawForestSkip, hb, ht]
                      | some pt =>
                          rcases pt with ⟨b, afterType⟩
                          simpa only [rawForestMaskParse, rawForestSkip, hb, ht] using
                            (rawMaskPrefix_fst (true :: List.replicate (a + b + 2) false) _).trans
                              (ih q afterType)

theorem rawNodeMask_length (T : BTree (ℕ × ℕ)) :
    (rawNodeMask T).length = (rawCellTreeBits T).length := by
  induction T with
  | leaf a => simp [rawNodeMask, rawCellTreeBits, unaryFrame]; omega
  | node l r ihl ihr =>
      simp only [rawNodeMask, rawCellTreeBits, List.length_cons, List.length_append, ihl, ihr]

theorem rawForestNodeMask_length (ts : List (BTree (ℕ × ℕ))) :
    (rawForestNodeMask ts).length = (rawForestWord ts).length := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
      simp only [rawForestNodeMask, rawForestWord, List.flatMap_cons, List.length_append,
        rawNodeMask_length] at ih ⊢
      exact congrArg (fun n => (rawCellTreeBits t).length + n) ih

theorem rawForestMaskParse_encode (fuel : ℕ) :
    ∀ (ts : List (BTree (ℕ × ℕ))) (rest : List Bool), rawForestNodes ts ≤ fuel →
      rawForestMaskParse fuel ts.length (rawForestWord ts ++ rest) =
        some (rest, rawForestNodeMask ts) := by
  induction fuel with
  | zero =>
      intro ts rest hf
      cases ts with
      | nil => rfl
      | cons t ts =>
          have ht := rawCellTree_vertex_pos t
          simp only [rawForestNodes, List.map_cons, List.sum_cons] at hf
          omega
  | succ fuel ih =>
      intro ts rest hf
      cases ts with
      | nil => rfl
      | cons t ts =>
          cases t with
          | leaf a =>
              have hsmall : rawForestNodes ts ≤ fuel := by
                simp only [rawForestNodes, List.map_cons, List.sum_cons, vertexCount] at hf ⊢
                omega
              simp only [rawForestWord, List.flatMap_cons, rawCellTreeBits, List.cons_append,
                List.length_cons, rawForestMaskParse, List.append_assoc, readUnaryFrame_encode]
              rw [ih ts rest hsmall]
              rfl
          | node l r =>
              have hsmall : rawForestNodes (l :: r :: ts) ≤ fuel := by
                simp only [rawForestNodes, List.map_cons, List.sum_cons, vertexCount] at hf ⊢
                omega
              have hh := ih (l :: r :: ts) rest hsmall
              simp only [List.length_cons, rawForestWord, List.flatMap_cons,
                List.append_assoc] at hh
              simp only [rawForestWord, List.flatMap_cons, rawCellTreeBits, List.cons_append,
                List.length_cons, rawForestMaskParse, List.append_assoc]
              rw [show ts.length + 1 + 1 = ts.length + 2 by omega] at hh
              rw [hh]
              simp [rawMaskPrefix, rawForestNodeMask, rawNodeMask, List.append_assoc]

/-- On every byte string, the computed mask marks exactly the node tokens
    of an actual q-tree prefix, never an interior unary-field suffix. -/
theorem rawForestMaskParse_all_words (bits rest mask : List Bool) (q : ℕ) :
    rawForestMaskParse bits.length q bits = some (rest, mask) ↔
      ∃ ts : List (BTree (ℕ × ℕ)), ts.length = q ∧
        bits = rawForestWord ts ++ rest ∧ mask = rawForestNodeMask ts := by
  constructor
  · intro h
    have hp := congrArg (Option.map Prod.fst) h
    rw [rawForestMaskParse_fst] at hp
    obtain ⟨ts, hlen, hword⟩ := rawForestSkip_sound bits.length q bits rest hp
    have hb := rawForestNodes_word_bound ts
    have hf : rawForestNodes ts ≤ bits.length := by rw [hword, List.length_append]; omega
    have he := rawForestMaskParse_encode bits.length ts rest hf
    rw [hlen, ← hword] at he
    have hm : mask = rawForestNodeMask ts := by
      have hh := h.symm.trans he
      exact congrArg Prod.snd (Option.some.inj hh)
    exact ⟨ts, hlen, hword, hm⟩
  · rintro ⟨ts, hlen, hword, hmask⟩
    have hb := rawForestNodes_word_bound ts
    have hf : rawForestNodes ts ≤ bits.length := by rw [hword, List.length_append]; omega
    have he := rawForestMaskParse_encode bits.length ts rest hf
    simpa only [hlen, ← hword, ← hmask] using he

theorem rawForestMaskParse_consumption (bits rest mask : List Bool) (q : ℕ)
    (h : rawForestMaskParse bits.length q bits = some (rest, mask)) :
    mask.length + rest.length = bits.length := by
  obtain ⟨ts, hlen, hword, hmask⟩ := (rawForestMaskParse_all_words bits rest mask q).mp h
  rw [hmask, rawForestNodeMask_length, hword, List.length_append]

/-- Each pair is a real subtree and the suffix AFTER it in the surrounding
    word. The left child carries the right child's bytes in that suffix. -/
def rawNodeViews (T : BTree (ℕ × ℕ)) (rest : List Bool) :
    List (BTree (ℕ × ℕ) × List Bool) :=
  (T, rest) :: match T with
    | .leaf _ => []
    | .node l r => rawNodeViews l (rawCellTreeBits r ++ rest) ++ rawNodeViews r rest

def rawViewSuffix (v : BTree (ℕ × ℕ) × List Bool) : List Bool :=
  rawCellTreeBits v.1 ++ v.2

def rawMarkedSuffixes : List Bool → List Bool → List (List Bool)
  | [], _ => []
  | _, [] => []
  | b :: bits, mark :: mask =>
      if mark then (b :: bits) :: rawMarkedSuffixes bits mask else rawMarkedSuffixes bits mask

theorem rawMarkedSuffixes_false_prefix (prefix rest mask : List Bool) :
    rawMarkedSuffixes (prefix ++ rest) (List.replicate prefix.length false ++ mask) =
      rawMarkedSuffixes rest mask := by
  induction prefix with
  | nil => rfl
  | cons b prefix ih =>
      simpa only [List.length_cons, List.replicate_succ, List.cons_append,
        rawMarkedSuffixes, Bool.false_eq_true, ↓reduceIte] using ih

/-- Exact legal-node navigation, with arbitrary external suffix/mask.
    This is a semantic identity, not an unimplemented machine-time claim. -/
theorem rawMarkedSuffixes_tree (T : BTree (ℕ × ℕ)) (rest mask : List Bool) :
    rawMarkedSuffixes (rawCellTreeBits T ++ rest) (rawNodeMask T ++ mask) =
      (rawNodeViews T rest).map rawViewSuffix ++ rawMarkedSuffixes rest mask := by
  induction T generalizing rest mask with
  | leaf a =>
      have hlen : (unaryFrame a.1 ++ unaryFrame a.2).length = a.1 + a.2 + 2 := by
        simp [unaryFrame]; omega
      change (rawCellTreeBits (.leaf a) ++ rest) ::
          rawMarkedSuffixes ((unaryFrame a.1 ++ unaryFrame a.2) ++ rest)
            (List.replicate (a.1 + a.2 + 2) false ++ mask) = _
      rw [← hlen, rawMarkedSuffixes_false_prefix]
      rfl
  | node l r ihl ihr =>
      simp only [rawCellTreeBits, rawNodeMask, List.cons_append, rawMarkedSuffixes,
        Bool.true_eq_true, ↓reduceIte, rawNodeViews, List.map_cons, List.map_append,
        rawViewSuffix, List.append_assoc]
      rw [ihl, ihr]

theorem rawNodeViews_clades (T : BTree (ℕ × ℕ)) (rest : List Bool) :
    (rawNodeViews T rest).map (fun v => scanLeaves v.1) = scanClades T := by
  induction T generalizing rest with
  | leaf a => rfl
  | node l r ihl ihr =>
      simp only [rawNodeViews, List.map_cons, List.map_append, scanClades, scanLeaves,
        ihl, ihr]

theorem rawNodeViews_count (T : BTree (ℕ × ℕ)) (rest : List Bool) :
    (rawNodeViews T rest).length = vertexCount T := by
  induction T generalizing rest with
  | leaf a => rfl
  | node l r ihl ihr =>
      simp only [rawNodeViews, List.length_cons, List.length_append, ihl, ihr, vertexCount]
      omega

/- The physical node-mask logger and bounded interval/clade scans must still
   be emitted and connected to this exact identity. A pure mask function is
   not a completed verifier machine or a substitute for independent input. -/

end PolytomyReductionModel
