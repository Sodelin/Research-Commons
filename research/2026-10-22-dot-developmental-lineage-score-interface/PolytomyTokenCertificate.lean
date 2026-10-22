/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No runtime or certificate.

Total prefix-token parsing and full reduction to checker acceptance.
Malformed tree syntax and trailing tokens are rejected. Tokens still carry
typed finite cell identities; a fixed-bit alphabet/payload decoder and a
polynomial Turing-machine realization remain separate obligations.
-/
import PolytomyCertificateChecker

namespace PolytomyReductionModel
universe u

inductive TreeToken (A : Type u) where
  | tip (a : A)
  | fork
  deriving DecidableEq

def treeTokens {A : Type u} : BTree A → List (TreeToken A)
  | .leaf a => [.tip a]
  | .node l r => .fork :: (treeTokens l ++ treeTokens r)

theorem treeTokens_length {A : Type u} (T : BTree A) :
    (treeTokens T).length = vertexCount T := by
  induction T with
  | leaf a => rfl
  | node l r ihl ihr => simp [treeTokens, vertexCount, ihl, ihr]; omega

/-- The fuel bounds recursion depth. Input length is sufficient for every
    valid prefix tree, and both failed and successful parses terminate. -/
def parseTreePrefix {A : Type u} :
    ℕ → List (TreeToken A) → Option (BTree A × List (TreeToken A))
  | 0, _ => none
  | _ + 1, [] => none
  | _ + 1, .tip a :: rest => some (.leaf a, rest)
  | fuel + 1, .fork :: rest =>
      match parseTreePrefix fuel rest with
      | none => none
      | some (l, afterLeft) =>
          match parseTreePrefix fuel afterLeft with
          | none => none
          | some (r, afterRight) => some (.node l r, afterRight)

theorem parseTreePrefix_encode {A : Type u} (T : BTree A) :
    ∀ (fuel : ℕ) (rest : List (TreeToken A)), vertexCount T ≤ fuel →
      parseTreePrefix fuel (treeTokens T ++ rest) = some (T, rest) := by
  induction T with
  | leaf a =>
      intro fuel rest hf
      cases fuel with
      | zero => simp [vertexCount] at hf
      | succ fuel => simp [treeTokens, parseTreePrefix]
  | node l r ihl ihr =>
      intro fuel rest hf
      cases fuel with
      | zero => simp [vertexCount] at hf
      | succ fuel =>
          have hl : vertexCount l ≤ fuel := by simp only [vertexCount] at hf; omega
          have hr : vertexCount r ≤ fuel := by simp only [vertexCount] at hf; omega
          simp only [treeTokens, List.cons_append, List.append_assoc, parseTreePrefix]
          rw [ihl fuel (treeTokens r ++ rest) hl, ihr fuel rest hr]

theorem parseTreePrefix_sound {A : Type u} (fuel : ℕ) :
    ∀ (tokens rest : List (TreeToken A)) (T : BTree A),
      parseTreePrefix fuel tokens = some (T, rest) → tokens = treeTokens T ++ rest := by
  induction fuel with
  | zero => intro tokens rest T h; simp [parseTreePrefix] at h
  | succ fuel ih =>
      intro tokens rest T h
      cases tokens with
      | nil => simp [parseTreePrefix] at h
      | cons token tokens =>
          cases token with
          | tip a =>
              simp only [parseTreePrefix, Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, rfl⟩ := h
              rfl
          | fork =>
              cases hl : parseTreePrefix fuel tokens with
              | none => simp [parseTreePrefix, hl] at h
              | some pair =>
                  obtain ⟨l, afterLeft⟩ := pair
                  cases hr : parseTreePrefix fuel afterLeft with
                  | none => simp [parseTreePrefix, hl, hr] at h
                  | some pair =>
                      obtain ⟨r, afterRight⟩ := pair
                      simp only [parseTreePrefix, hl, hr, Option.some.injEq,
                        Prod.mk.injEq] at h
                      have hleft := ih tokens afterLeft l hl
                      have hright := ih afterLeft afterRight r hr
                      calc
                        .fork :: tokens = .fork :: (treeTokens l ++ afterLeft) := by rw [hleft]
                        _ = treeTokens (.node l r) ++ afterRight := by
                          rw [hright]
                          simp [treeTokens, List.append_assoc]
                        _ = treeTokens T ++ rest := by rw [h.1, h.2]

/-- A whole-certificate parser rejects incomplete syntax and any trailing
    material rather than silently accepting the first complete tree. -/
def parseTreeTokens {A : Type u} (tokens : List (TreeToken A)) : Option (BTree A) :=
  match parseTreePrefix tokens.length tokens with
  | some (T, []) => some T
  | _ => none

theorem parseTreeTokens_spec {A : Type u} (tokens : List (TreeToken A)) (T : BTree A) :
    parseTreeTokens tokens = some T ↔ tokens = treeTokens T := by
  constructor
  · intro h
    cases hp : parseTreePrefix tokens.length tokens with
    | none => simp [parseTreeTokens, hp] at h
    | some pair =>
        obtain ⟨R, rest⟩ := pair
        cases rest with
        | cons a rest => simp [parseTreeTokens, hp] at h
        | nil =>
            have he : R = T := by simpa [parseTreeTokens, hp] using h
            subst R
            simpa using parseTreePrefix_sound tokens.length tokens [] T hp
  · intro h
    subst tokens
    have hp := parseTreePrefix_encode T (treeTokens T).length []
      (by rw [treeTokens_length])
    simp only [List.append_nil] at hp
    simp [parseTreeTokens, hp]

noncomputable def checkCanonicalTokens {N m : ℕ} (D : MSSCInstance N m) (K : ℕ)
    (tokens : List (TreeToken (Cell N m))) : Bool :=
  match parseTreeTokens tokens with
  | none => false
  | some T => checkCanonicalTree D K T

theorem checkCanonicalTokens_spec {N m : ℕ} (D : MSSCInstance N m) (K : ℕ)
    (tokens : List (TreeToken (Cell N m))) :
    checkCanonicalTokens D K tokens = true ↔
      ∃ T : BTree (Cell N m), tokens = treeTokens T ∧ checkCanonicalTree D K T = true := by
  constructor
  · intro h
    cases hp : parseTreeTokens tokens with
    | none => simp [checkCanonicalTokens, hp] at h
    | some T =>
        refine ⟨T, (parseTreeTokens_spec tokens T).mp hp, ?_⟩
        simpa [checkCanonicalTokens, hp] using h
  · rintro ⟨T, ht, hc⟩
    have hp := (parseTreeTokens_spec tokens T).mpr ht
    simpa [checkCanonicalTokens, hp] using hc

theorem checked_tokens_length_bound {N m : ℕ} (D : MSSCInstance N m) (K : ℕ)
    (tokens : List (TreeToken (Cell N m))) (h : checkCanonicalTokens D K tokens = true) :
    tokens.length < 2 * ((m + 1) * (N + m * N + 3)) := by
  obtain ⟨T, rfl, hT⟩ := (checkCanonicalTokens_spec D K tokens).mp h
  rw [treeTokens_length]
  have hl := checked_tree_leaf_bound D K T hT
  have he := vertexCount_add_one T
  omega

theorem standardCanonicalCartaDecision_iff_checked_tokens {N m : ℕ}
    (D : MSSCInstance N m) (lambda : ℝ) (K : ℕ) :
    StandardCanonicalCartaDecision D lambda K ↔
      ∃ tokens : List (TreeToken (Cell N m)), checkCanonicalTokens D K tokens = true := by
  rw [standardCanonicalCartaDecision_iff_checked_tree]
  constructor
  · rintro ⟨T, hT⟩
    exact ⟨treeTokens T, (checkCanonicalTokens_spec D K _).mpr ⟨T, rfl, hT⟩⟩
  · rintro ⟨tokens, h⟩
    obtain ⟨T, ht, hT⟩ := (checkCanonicalTokens_spec D K tokens).mp h
    exact ⟨T, hT⟩

theorem full_exactTripleCover_token_reduction {q m : ℕ}
    (D : TripleCoverInstance q m) (hq : 0 < q) (hm : 2 ≤ m) :
    ExactTripleCoverDecision D ↔
      ∃ tokens : List (TreeToken (Cell (3 * q) m)),
        checkCanonicalTokens D.toMSSCInstance (tripleThreshold q m) tokens = true := by
  exact (full_exactTripleCover_carta_reduction D 0 hq hm).trans
    (standardCanonicalCartaDecision_iff_checked_tokens D.toMSSCInstance 0
      (tripleThreshold q m))

end PolytomyReductionModel
