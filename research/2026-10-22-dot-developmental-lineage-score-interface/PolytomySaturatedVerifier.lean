/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No runtime, compilation or certificate.

Separate all-input bounded-header/budget adapter for the ORIGINAL
independent verifier. No MSSC source witness and no promise that the
certificate is short, valid, canonical or a refinement is supplied.
-/
import PolytomySaturatedSource

namespace PolytomyReductionModel

def readBoundedNatFrame (L : ℕ) (bits : List Bool) : Option (ℕ × List Bool) :=
  match readSaturatedBinaryNatFrame (L + 1) bits with
  | none => none
  | some (n, rest) => if n ≤ L then some (n, rest) else none

theorem readBoundedNatFrame_eq (L : ℕ) (bits : List Bool) :
    readBoundedNatFrame L bits = (readBinaryNatFrame bits).bind
      (fun p => if p.1 ≤ L then some p else none) := by
  unfold readBoundedNatFrame
  rw [readSaturatedBinaryNatFrame_eq]
  cases h : readBinaryNatFrame bits with
  | none => rfl
  | some p =>
      rcases p with ⟨n, rest⟩
      by_cases hn : n ≤ L
      · have hmin : min n (L + 1) = n := min_eq_left (by omega)
        simp [hn, hmin]
      · have hmin : ¬ min n (L + 1) ≤ L := by omega
        simp [hn, hmin]

def clipTargetBudget {N m : ℕ} (cap : ℕ) (R : RawTargetRows N m) : RawTargetRows N m :=
  { R with budget := min R.budget cap }

def boundedTargetView (L cap : ℕ) (R : AnyRawTargetRows) : Option AnyRawTargetRows :=
  if R.1 ≤ L ∧ R.2.1 ≤ L then
    some ⟨R.1, R.2.1, clipTargetBudget cap R.2.2⟩
  else none

/-- Headers are saturated and checked BEFORE parsing dimension-dependent
    tree cells. The budget is never first materialized as an unbounded value. -/
def parseBoundedTargetPrefix (L cap : ℕ) (bits : List Bool) :
    Option (AnyRawTargetRows × List Bool) :=
  match readBoundedNatFrame L bits with
  | none => none
  | some (N, r1) =>
      match readBoundedNatFrame L r1 with
      | none => none
      | some (m, r2) =>
          match readSaturatedBinaryNatFrame cap r2 with
          | none => none
          | some (budget, r3) =>
              match readFramedList (readTargetTree N m) r3 with
              | none => none
              | some (rows, rest) => some (⟨N, m, ⟨budget, rows⟩⟩, rest)

theorem parseBoundedTargetPrefix_eq (L cap : ℕ) (bits : List Bool) :
    parseBoundedTargetPrefix L cap bits = (parseRawTargetPrefix bits).bind
      (fun p => (boundedTargetView L cap p.1).map (fun R => (R, p.2))) := by
  cases h1 : readBinaryNatFrame bits with
  | none =>
      simp [parseBoundedTargetPrefix, readBoundedNatFrame_eq, parseRawTargetPrefix, h1]
  | some p =>
      rcases p with ⟨N, r1⟩
      cases h2 : readBinaryNatFrame r1 with
      | none =>
          by_cases hN : N ≤ L <;>
            simp [parseBoundedTargetPrefix, readBoundedNatFrame_eq, parseRawTargetPrefix,
              h1, h2, hN]
      | some p =>
          rcases p with ⟨m, r2⟩
          cases h3 : readBinaryNatFrame r2 with
          | none =>
              by_cases hN : N ≤ L <;> by_cases hm : m ≤ L <;>
                simp [parseBoundedTargetPrefix, readBoundedNatFrame_eq,
                  readSaturatedBinaryNatFrame_eq, parseRawTargetPrefix, h1, h2, h3, hN, hm]
          | some p =>
              rcases p with ⟨budget, r3⟩
              cases h4 : readFramedList (readTargetTree N m) r3 with
              | none =>
                  by_cases hN : N ≤ L <;> by_cases hm : m ≤ L <;>
                    simp [parseBoundedTargetPrefix, readBoundedNatFrame_eq,
                      readSaturatedBinaryNatFrame_eq, parseRawTargetPrefix,
                      h1, h2, h3, h4, hN, hm]
              | some p =>
                  rcases p with ⟨rows, rest⟩
                  by_cases hN : N ≤ L <;> by_cases hm : m ≤ L <;>
                    simp [parseBoundedTargetPrefix, readBoundedNatFrame_eq,
                      readSaturatedBinaryNatFrame_eq, parseRawTargetPrefix,
                      h1, h2, h3, h4, hN, hm, boundedTargetView, clipTargetBudget]

def parseBoundedTarget (L cap : ℕ) (bits : List Bool) : Option AnyRawTargetRows :=
  match parseBoundedTargetPrefix L cap bits with
  | some (R, []) => some R
  | _ => none

theorem parseBoundedTarget_eq (L cap : ℕ) (bits : List Bool) :
    parseBoundedTarget L cap bits = (parseRawTarget bits).bind (boundedTargetView L cap) := by
  unfold parseBoundedTarget parseRawTarget
  rw [parseBoundedTargetPrefix_eq]
  cases hp : parseRawTargetPrefix bits with
  | none => rfl
  | some p =>
      rcases p with ⟨R, rest⟩
      cases hv : boundedTargetView L cap R <;> cases rest <;> simp [hv]

theorem parseBoundedTarget_bounds (L cap : ℕ) (bits : List Bool)
    (R : AnyRawTargetRows) (h : parseBoundedTarget L cap bits = some R) :
    R.1 ≤ L ∧ R.2.1 ≤ L ∧ R.2.2.budget ≤ cap ∧ rawAnyTargetSize R ≤ bits.length := by
  rw [parseBoundedTarget_eq] at h
  cases hp : parseRawTarget bits with
  | none => simp [hp] at h
  | some Q =>
      rcases Q with ⟨N, m, Q⟩
      by_cases hd : N ≤ L ∧ m ≤ L
      · have he : (⟨N, m, clipTargetBudget cap Q⟩ : AnyRawTargetRows) = R := by
          simpa [hp, boundedTargetView, hd] using h
        rw [← he]
        refine ⟨hd.1, hd.2, min_le_right _ _, ?_⟩
        exact parseRawTarget_size_bound bits ⟨N, m, Q⟩ hp
      · simp [hp, boundedTargetView, hd] at h

theorem parsed_valid_target_bounds (input : List Bool) {N m : ℕ}
    (R : RawTargetRows N m)
    (hp : parseRawTarget input = some ⟨N, m, R⟩) (hv : RawTargetRowsValid R) :
    N ≤ input.length ∧ m ≤ input.length ∧ N + m * N + 3 ≤ input.length := by
  have hs := parseRawTarget_size_bound input ⟨N, m, R⟩ hp
  obtain ⟨hS, hm⟩ := raw_target_dimensions_bounded R hv
  simp only [rawAnyTargetSize] at hs
  omega

theorem parseBitTree_vertices_bounded (N m : ℕ) (bits : List Bool)
    (T : BTree (Cell N m)) (h : parseBitTree N m bits = some T) :
    vertexCount T ≤ bits.length := by
  cases hp : parseBitPrefix N m bits.length bits with
  | none => simp [parseBitTree, hp] at h
  | some p =>
      rcases p with ⟨U, rest⟩
      cases rest with
      | cons b rest => simp [parseBitTree, hp] at h
      | nil =>
          have he : U = T := by simpa [parseBitTree, hp] using h
          subst U
          simpa using parseBitPrefix_consumption N m bits.length bits T [] hp

theorem scanStarScore_vertices_bound {A S : Type} [DecidableEq S]
    (s : ℕ) (tip : A → S) (T : BTree A) :
    scanStarScore s tip T ≤ s * vertexCount T := by
  induction T with
  | leaf a => simp [scanStarScore, vertexCount]
  | node l r ihl ihr =>
      have hsub := Nat.sub_le s (scanTypeCount tip (.node l r))
      simp only [scanStarScore, vertexCount]
      nlinarith

def verifierBudgetCap (input cert : List Bool) : ℕ :=
  (input.length + cert.length + 1) ^ 2

theorem readVerifierPair_payload_length (bits input cert : List Bool)
    (h : readVerifierPair bits = some (input, cert)) :
    input.length + cert.length ≤ bits.length := by
  cases hp : readUnaryFrame bits with
  | none => simp [readVerifierPair, hp] at h
  | some p =>
      rcases p with ⟨width, rest⟩
      by_cases hw : width ≤ rest.length
      · simp only [readVerifierPair, hp, if_pos hw, Option.some.injEq,
          Prod.mk.injEq] at h
        have hi := congrArg List.length h.1
        have hc := congrArg List.length h.2
        simp only [List.length_take, List.length_drop] at hi hc
        have hlen := readUnaryFrame_consumption bits width rest hp
        omega
      · simp [readVerifierPair, hp, hw] at h

theorem verifierBudgetCap_pair_bound (bits input cert : List Bool)
    (h : readVerifierPair bits = some (input, cert)) :
    verifierBudgetCap input cert ≤ (bits.length + 1) ^ 2 := by
  have hp := readVerifierPair_payload_length bits input cert h
  have hlen : input.length + cert.length + 1 ≤ bits.length + 1 := by omega
  simpa only [verifierBudgetCap, pow_two] using Nat.mul_le_mul hlen hlen

/-- No certificate-validity or bounded-witness assumption: every parsed
    tree, even a wrong-cell or gigantic candidate, has this score bound. -/
theorem parsed_verifier_score_bound (input cert : List Bool) {N m : ℕ}
    (R : RawTargetRows N m) (hp : parseRawTarget input = some ⟨N, m, R⟩)
    (hv : RawTargetRowsValid R) (T : BTree (Cell N m))
    (hc : parseBitTree N m cert = some T) :
    scanStarScore (N + m * N + 3) Prod.snd T ≤ verifierBudgetCap input cert := by
  have hs := (parsed_valid_target_bounds input R hp hv).2.2
  have ht := parseBitTree_vertices_bounded N m cert T hc
  have hb := scanStarScore_vertices_bound (N + m * N + 3) Prod.snd T
  have hm := Nat.mul_le_mul hs ht
  unfold verifierBudgetCap
  nlinarith

theorem scanRawTargetValid_clip_budget {N m : ℕ} (cap : ℕ) (R : RawTargetRows N m) :
    scanRawTargetValid (clipTargetBudget cap R) = scanRawTargetValid R := rfl

theorem scanRawCertificate_clip_budget {N m : ℕ} (cap : ℕ) (R : RawTargetRows N m)
    (T : BTree (Cell N m)) (h : scanStarScore (N + m * N + 3) Prod.snd T ≤ cap) :
    scanRawCertificate (clipTargetBudget cap R) T = scanRawCertificate R T := by
  simp only [scanRawCertificate, clipTargetBudget, le_min_iff, h, and_true]

def scanTargetRecord (cert : List Bool) (R : AnyRawTargetRows) : Bool :=
  match R with
  | ⟨N, m, R⟩ =>
      if scanRawTargetValid R then
        match parseBitTree N m cert with
        | none => false
        | some T => scanRawCertificate R T
      else false

theorem scanEncodedTarget_as_record (input cert : List Bool) :
    scanEncodedTarget input cert =
      match parseRawTarget input with
      | none => false
      | some R => scanTargetRecord cert R := rfl

theorem scanTargetRecord_clip_budget (input cert : List Bool) {N m : ℕ}
    (R : RawTargetRows N m) (hp : parseRawTarget input = some ⟨N, m, R⟩) :
    scanTargetRecord cert ⟨N, m, clipTargetBudget (verifierBudgetCap input cert) R⟩ =
      scanTargetRecord cert ⟨N, m, R⟩ := by
  by_cases hv : RawTargetRowsValid R
  · have hs := (scanRawTargetValid_spec R).mpr hv
    cases hc : parseBitTree N m cert with
    | none => simp [scanTargetRecord, scanRawTargetValid_clip_budget, hs, hc]
    | some T =>
        have hbound := parsed_verifier_score_bound input cert R hp hv T hc
        have he := scanRawCertificate_clip_budget (verifierBudgetCap input cert) R T hbound
        simpa [scanTargetRecord, scanRawTargetValid_clip_budget, hs, hc] using he
  · have hs : scanRawTargetValid R = false := by
      cases hb : scanRawTargetValid R with
      | false => rfl
      | true => exact (hv ((scanRawTargetValid_spec R).mp hb)).elim
    simp [scanTargetRecord, scanRawTargetValid_clip_budget, hs]

theorem scanTargetRecord_large_header (input cert : List Bool) {N m : ℕ}
    (R : RawTargetRows N m) (hp : parseRawTarget input = some ⟨N, m, R⟩)
    (h : ¬ (N ≤ input.length ∧ m ≤ input.length)) :
    scanTargetRecord cert ⟨N, m, R⟩ = false := by
  have hv : ¬ RawTargetRowsValid R := by
    intro hv
    have hb := parsed_valid_target_bounds input R hp hv
    exact h ⟨hb.1, hb.2.1⟩
  have hs : scanRawTargetValid R = false := by
    cases hb : scanRawTargetValid R with
    | false => rfl
    | true => exact (hv ((scanRawTargetValid_spec R).mp hb)).elim
  simp [scanTargetRecord, hs]

def boundedEncodedTarget (input cert : List Bool) : Bool :=
  match parseBoundedTarget input.length (verifierBudgetCap input cert) input with
  | none => false
  | some R => scanTargetRecord cert R

/-- EXACT Boolean agreement on all independent target/certificate pairs,
    not just on reductions, well-formed inputs or NP-bounded certificates. -/
theorem boundedEncodedTarget_eq (input cert : List Bool) :
    boundedEncodedTarget input cert = scanEncodedTarget input cert := by
  rw [scanEncodedTarget_as_record]
  unfold boundedEncodedTarget
  rw [parseBoundedTarget_eq]
  cases hp : parseRawTarget input with
  | none => rfl
  | some R =>
      rcases R with ⟨N, m, R⟩
      by_cases h : N ≤ input.length ∧ m ≤ input.length
      · simp only [Option.bind_some, boundedTargetView, if_pos h]
        exact scanTargetRecord_clip_budget input cert R hp
      · simp only [Option.bind_some, boundedTargetView, if_neg h]
        exact (scanTargetRecord_large_header input cert R hp h).symm

def boundedPairVerifier (bits : List Bool) : Bool :=
  match readVerifierPair bits with
  | none => false
  | some (input, cert) => boundedEncodedTarget input cert

theorem boundedPairVerifier_eq (bits : List Bool) :
    boundedPairVerifier bits = scanPairVerifier bits := by
  unfold boundedPairVerifier scanPairVerifier
  cases h : readVerifierPair bits with
  | none => rfl
  | some p => rcases p with ⟨input, cert⟩; exact boundedEncodedTarget_eq input cert

def originalVerifierMachineOfBounded
    (h : Turing.TM2ComputableInPolyTime
      (fun bits : List Bool => bits) (fun b : Bool => [b]) boundedPairVerifier) :
    VerifierMachineWitness := by
  have he : boundedPairVerifier = scanPairVerifier := funext boundedPairVerifier_eq
  simpa only [he] using h

theorem full_bounded_algorithms_interface (input : List Bool) (lambda : ℝ) :
    (saturatedEncodedConstructor input).length ≤ sourceOutputSizeBound input.length ∧
      (SourceBitMSSCDecision input ↔
        EncodedTargetCartaDecision (saturatedEncodedConstructor input) lambda) ∧
      (EncodedTargetCartaDecision (saturatedEncodedConstructor input) lambda ↔
        ∃ cert : List Bool,
          cert.length ≤ targetBitCertificateBound (saturatedEncodedConstructor input).length ∧
          boundedEncodedTarget (saturatedEncodedConstructor input) cert = true) := by
  simpa only [boundedEncodedTarget_eq] using full_saturated_source_reduction input lambda

/- Full emitted finite programs, exact nested-parser and clade/serialization
execution proofs, polynomial bounds/cleanup, encoded upstream hardness,
dependency closure and all authorized kernel checks remain open. The adapter
does not certify Lean evaluation cost or solve stochastic identifiability.
-/

end PolytomyReductionModel
