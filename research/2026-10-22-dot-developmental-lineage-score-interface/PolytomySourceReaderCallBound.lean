/-
Author: dot (OpenAI), 22 October 2026.
SOURCE ONLY, UNELABORATED. No execution or certificate.

All-input primitive-reader CALL counting for the ORIGINAL full nested
source parser, including failures and trailing garbage. A charge is one
reader invocation, NOT one TM2 transition. Exact erasure recovers the
original parser. Actual loop/copy/stack implementations remain required.
-/
import PolytomyNumericFrameCaller

namespace PolytomyReductionModel
universe u v

abbrev CountedReader (A : Type u) := List Bool → Option (A × List Bool) × ℕ

def countedPure {A : Type u} (a : A) : CountedReader A := fun bits => (some (a, bits), 0)

def countedBind {A : Type u} {B : Type v} (r : CountedReader A)
    (f : A → CountedReader B) : CountedReader B := fun bits =>
  let (result, c) := r bits
  match result with
  | none => (none, c)
  | some (a, rest) =>
      let (result', d) := f a rest
      (result', c + d)

/-- Success charges only consumed input; failure has one final attempted
    reader call. This potential telescopes through arbitrary bind/nesting. -/
def ReaderSpanBound {A : Type u} (r : CountedReader A) : Prop :=
  ∀ bits, match r bits with
  | (none, c) => c ≤ bits.length + 1
  | (some (_, rest), c) => c + rest.length ≤ bits.length

theorem countedPure_span {A : Type u} (a : A) : ReaderSpanBound (countedPure a) := by
  intro bits
  simp [countedPure]

theorem countedBind_span {A : Type u} {B : Type v} (r : CountedReader A)
    (f : A → CountedReader B) (hr : ReaderSpanBound r)
    (hf : ∀ a, ReaderSpanBound (f a)) : ReaderSpanBound (countedBind r f) := by
  intro bits
  have hfirst := hr bits
  cases hR : r bits with
  | mk result c =>
      cases result with
      | none => simpa only [countedBind, hR] using hfirst
      | some p =>
          rcases p with ⟨a, rest⟩
          have hc : c + rest.length ≤ bits.length := by simpa only [hR] using hfirst
          have hsecond := hf a rest
          cases hS : f a rest with
          | mk result' d =>
              cases result' with
              | none =>
                  have hd : d ≤ rest.length + 1 := by simpa only [hS] using hsecond
                  simp only [countedBind, hR, hS]
                  omega
              | some p' =>
                  rcases p' with ⟨b, after⟩
                  have hd : d + after.length ≤ rest.length := by simpa only [hS] using hsecond
                  simp only [countedBind, hR, hS]
                  omega

theorem countedBind_erase {A : Type u} {B : Type v} (r : CountedReader A)
    (f : A → CountedReader B) (bits : List Bool) :
    (countedBind r f bits).1 =
      match (r bits).1 with
      | none => none
      | some (a, rest) => (f a rest).1 := by
  cases hR : r bits with
  | mk result c => cases result with
    | none => simp only [countedBind, hR]
    | some p =>
        rcases p with ⟨a, rest⟩
        simp only [countedBind, hR]
        cases f a rest
        rfl

theorem counted_span_total {A : Type u} (r : CountedReader A)
    (hr : ReaderSpanBound r) (bits : List Bool) : (r bits).2 ≤ bits.length + 1 := by
  have h := hr bits
  cases he : r bits with
  | mk result c =>
      cases result with
      | none => simpa only [he] using h
      | some p =>
          rcases p with ⟨a, rest⟩
          have hc : c + rest.length ≤ bits.length := by simpa only [he] using h
          simp only [he]
          omega

def countedUnary : CountedReader ℕ := fun bits => (readUnaryFrame bits, 1)
def countedNumeric (cap : ℕ) : CountedReader ℕ :=
  fun bits => (readSaturatedBinaryNatFrame cap bits, 1)

theorem countedUnary_span : ReaderSpanBound countedUnary := by
  intro bits
  unfold countedUnary
  cases hp : readUnaryFrame bits with
  | none => simp
  | some p =>
      rcases p with ⟨n, rest⟩
      have he := readUnaryFrame_decomposition bits n rest hp
      have hlen : bits.length = n + 1 + rest.length := by rw [he]; simp [unaryFrame, Nat.add_assoc]
      omega

theorem countedNumeric_span (cap : ℕ) : ReaderSpanBound (countedNumeric cap) := by
  intro bits
  unfold countedNumeric readSaturatedBinaryNatFrame
  cases hp : readUnaryFrame bits with
  | none => simp
  | some p =>
      rcases p with ⟨n, rest⟩
      have he := readUnaryFrame_decomposition bits n rest hp
      have hlen : bits.length = n + 1 + rest.length := by rw [he]; simp [unaryFrame, Nat.add_assoc]
      by_cases hn : n ≤ rest.length
      · simp only [hn, ↓reduceIte, List.length_drop]
        omega
      · simp [hn]

def countedMany {A : Type u} (r : CountedReader A) : ℕ → CountedReader (List A)
  | 0 => countedPure []
  | n + 1 => countedBind r (fun a =>
      countedBind (countedMany r n) (fun xs => countedPure (a :: xs)))

def countedFramed {A : Type u} (r : CountedReader A) : CountedReader (List A) :=
  countedBind countedUnary (countedMany r)

theorem countedMany_span {A : Type u} (r : CountedReader A) (hr : ReaderSpanBound r)
    (n : ℕ) : ReaderSpanBound (countedMany r n) := by
  induction n with
  | zero => exact countedPure_span []
  | succ n ih => exact countedBind_span r _ hr
      (fun a => countedBind_span (countedMany r n) _ ih (fun xs => countedPure_span (a :: xs)))

theorem countedFramed_span {A : Type u} (r : CountedReader A) (hr : ReaderSpanBound r) :
    ReaderSpanBound (countedFramed r) :=
  countedBind_span countedUnary (countedMany r) countedUnary_span (countedMany_span r hr)

theorem countedMany_erase {A : Type u} (r : CountedReader A) (n : ℕ) (bits : List Bool) :
    (countedMany r n bits).1 = readMany (fun xs => (r xs).1) n bits := by
  induction n generalizing bits with
  | zero => rfl
  | succ n ih =>
      simp only [countedMany, countedBind_erase]
      cases hp : (r bits).1 with
      | none => simp only [readMany, hp]
      | some p =>
          rcases p with ⟨a, rest⟩
          simp only [readMany, hp, countedBind_erase, ih, countedPure]
          cases readMany (fun xs => (r xs).1) n rest <;> rfl

theorem countedFramed_erase {A : Type u} (r : CountedReader A) (bits : List Bool) :
    (countedFramed r bits).1 = readFramedList (fun xs => (r xs).1) bits := by
  simp only [countedFramed, countedBind_erase, countedUnary, readFramedList]
  cases hp : readUnaryFrame bits with
  | none => rfl
  | some p => rcases p with ⟨n, rest⟩; exact countedMany_erase r n rest

def countedSourcePrefix (L : ℕ) : CountedReader RawMSSCRecord :=
  countedBind (countedNumeric (L + 1)) fun N =>
    countedBind (countedNumeric (L + 1)) fun m =>
      countedBind (countedNumeric ((L + 1) ^ 2)) fun K =>
        countedBind (countedFramed (countedFramed (countedNumeric (L + 1)))) fun rows =>
          countedPure ⟨N, m, K, rows⟩

theorem countedSourcePrefix_span (L : ℕ) : ReaderSpanBound (countedSourcePrefix L) := by
  apply countedBind_span _ _ (countedNumeric_span (L + 1))
  intro N
  apply countedBind_span _ _ (countedNumeric_span (L + 1))
  intro m
  apply countedBind_span _ _ (countedNumeric_span ((L + 1) ^ 2))
  intro K
  apply countedBind_span _ _
    (countedFramed_span _ (countedFramed_span _ (countedNumeric_span (L + 1))))
  intro rows
  exact countedPure_span ⟨N, m, K, rows⟩

theorem countedSourcePrefix_erase (L : ℕ) (bits : List Bool) :
    (countedSourcePrefix L bits).1 = parseSaturatedSourcePrefix L bits := by
  simp only [countedSourcePrefix, countedBind_erase, countedNumeric,
    countedFramed_erase, countedPure, parseSaturatedSourcePrefix]

def countedSaturatedSource (bits : List Bool) : Option RawMSSCRecord × ℕ :=
  let (result, c) := countedSourcePrefix bits.length bits
  (match result with
    | some (R, []) => some R
    | _ => none, c)

theorem countedSaturatedSource_erase (bits : List Bool) :
    (countedSaturatedSource bits).1 = parseSaturatedSource bits := by
  unfold countedSaturatedSource parseSaturatedSource
  have he := countedSourcePrefix_erase bits.length bits
  cases hp : countedSourcePrefix bits.length bits with
  | mk result c =>
      have hr : result = parseSaturatedSourcePrefix bits.length bits := by simpa only [hp] using he
      rw [← hr]

/-- The charge is number of primitive reader invocations, not TM2 time.
    The bound covers malformed frames/counts and trailing garbage too. -/
theorem countedSaturatedSource_calls (bits : List Bool) :
    (countedSaturatedSource bits).2 ≤ bits.length + 1 := by
  have h := counted_span_total (countedSourcePrefix bits.length)
    (countedSourcePrefix_span bits.length) bits
  unfold countedSaturatedSource
  cases hp : countedSourcePrefix bits.length bits with
  | mk result c => simpa only [hp] using h

theorem countedSaturatedSource_success_calls (bits : List Bool) (R : RawMSSCRecord)
    (h : (countedSaturatedSource bits).1 = some R) :
    (countedSaturatedSource bits).2 ≤ bits.length := by
  have hs := countedSourcePrefix_span bits.length bits
  cases hp : countedSourcePrefix bits.length bits with
  | mk result c =>
      cases result with
      | none => simp [countedSaturatedSource, hp] at h
      | some p =>
          rcases p with ⟨Q, rest⟩
          have hc : c + rest.length ≤ bits.length := by simpa only [hp] using hs
          simpa only [countedSaturatedSource, hp] using (show c ≤ bits.length by omega)

theorem full_reduction_with_source_call_bound (input : List Bool) (lambda : ℝ) :
    (rawRowConstructor input).length ≤ sourceOutputSizeBound input.length ∧
      (SourceBitMSSCDecision input ↔ EncodedTargetCartaDecision (rawRowConstructor input) lambda) ∧
      (EncodedTargetCartaDecision (rawRowConstructor input) lambda ↔
        ∃ cert : List Bool,
          cert.length ≤ targetBitCertificateBound (rawRowConstructor input).length ∧
          boundedEncodedTarget (rawRowConstructor input) cert = true) ∧
      (countedSaturatedSource input).1 = parseSaturatedSource input ∧
      (countedSaturatedSource input).2 ≤ input.length + 1 := by
  have h := full_raw_row_constructor_interface input lambda
  exact ⟨h.1, h.2.1, h.2.2, countedSaturatedSource_erase input, countedSaturatedSource_calls input⟩

/- Call counting does NOT charge stack-loop dispatch, copying, emitted
record storage, cap construction or cleanup. Those require actual nested
programs and the complete operational proofs, not a new interpretation of
this charge as a Turing step. Full constructor/checker, encoded hardness
and all kernel checks remain open; original target/model are unchanged.
-/

end PolytomyReductionModel
