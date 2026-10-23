/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

The fixed pipeline's Boolean is tied to the ORIGINAL independent target
and certificate words, including prefix failures. Saturation is removed
only through the pre-existing semantic budget bound, never through the
looser operational alphabet bound. Clean halt and complexity packaging
are not supplied by this semantic equality.
-/
import PolytomyRestrictedVerifierGuardSemantics

namespace PolytomyReductionModel.WholeVerifierController

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def restrictedBodyAnswer (N m B : ℕ) (rows cert : List Bool) : Bool :=
  match readFramedList (readTargetTree N m) rows with
  | some (Ts, []) =>
      match parseBitTree N m cert with
      | none => false
      | some T => scanRawTargetValid (⟨B, Ts⟩ : RawTargetRows N m) &&
          scanRawCertificate (⟨B, Ts⟩ : RawTargetRows N m) T
  | _ => false

theorem restrictedBodyAnswer_true_iff (N m B : ℕ) (rows cert : List Bool) :
    restrictedBodyAnswer N m B rows cert = true ↔
      ∃ Ts T, readFramedList (readTargetTree N m) rows = some (Ts, []) ∧
        parseBitTree N m cert = some T ∧
        scanRawTargetValid (⟨B, Ts⟩ : RawTargetRows N m) = true ∧
        scanRawCertificate (⟨B, Ts⟩ : RawTargetRows N m) T = true := by
  cases hr : readFramedList (readTargetTree N m) rows with
  | none => simp [restrictedBodyAnswer, hr]
  | some pair =>
      rcases pair with ⟨Ts, rest⟩
      cases rest with
      | cons b bs => simp [restrictedBodyAnswer, hr]
      | nil =>
          cases hc : parseBitTree N m cert with
          | none => simp [restrictedBodyAnswer, hr, hc]
          | some T => simp [restrictedBodyAnswer, hr, hc, Bool.and_eq_true]

theorem restrictedBodyAnswer_bad_dimensions (N m B : ℕ) (rows cert : List Bool)
    (h : ¬ (0 < N ∧ 2 ≤ m)) : restrictedBodyAnswer N m B rows cert = false := by
  cases ha : restrictedBodyAnswer N m B rows cert with
  | false => rfl
  | true =>
      obtain ⟨Ts, T, _, _, hv, _⟩ := (restrictedBodyAnswer_true_iff N m B rows cert).mp ha
      have hg : 0 < N ∧ 2 ≤ m := by
        simp only [scanRawTargetValid, Bool.and_eq_true, decide_eq_true_eq] at hv
        exact ⟨hv.1.1.1.1.1.1, hv.1.1.1.1.1.2⟩
      exact (h hg).elim

theorem restrictedSyntax_accepts_iff (N m L : ℕ) (s : RestrictedStore)
    (hf : s.state.2 = true)
    (ht : GrammarEntry restrictedTargetGrammarPorts N m L s)
    (hc : GrammarEntry restrictedCertGrammarPorts N m L s) :
    (restrictedSyntaxEval N m s).state.2 = true ↔
      ∃ Ts T, Ts.length = m + 1 ∧
        readFramedList (readTargetTree N m) (s.stk (.inl .source)) = some (Ts, []) ∧
        parseBitTree N m (s.stk (restrictedHeader .certificate)) = some T := by
  let u := originalTargetForestEval restrictedTargetGrammarPorts N m s
  have htarget := originalTargetForest_accepts_iff restrictedTargetGrammarPorts N m L s ht
  have hcert := originalCertificateGrammar_accepts_iff restrictedCertGrammarPorts N m L u
    (restrictedTarget_cert_entry N m L s hc)
  have hw := originalTargetForest_outside restrictedTargetGrammarPorts N m s
    (restrictedHeader .certificate) (by intro j; cases j <;> decide)
  change (originalTargetForestEval restrictedTargetGrammarPorts N m s).stk
    (restrictedHeader .certificate) = _ at hw
  have hcert' : (originalCertificateGrammarEval restrictedCertGrammarPorts N m u).state.2 = true ↔
      ∃ T : BTree (Cell N m), parseBitTree N m (s.stk (restrictedHeader .certificate)) = some T := by
    simpa only [restrictedCertGrammarPorts, restrictedCertGrammarMap, u, hw] using hcert
  cases hu : u.state.2 with
  | false =>
      constructor
      · simp [restrictedSyntaxEval, hf, u, hu]
      · rintro ⟨Ts, T, hq, hp, _⟩
        have hx := htarget.mpr ⟨Ts, hq, hp⟩
        simp only [← u, hu, Bool.false_eq_true] at hx
  | true =>
      constructor
      · intro h
        have hv : (originalCertificateGrammarEval restrictedCertGrammarPorts N m u).state.2 = true := by
          simpa only [restrictedSyntaxEval, hf, hu, ↓reduceIte, u] using h
        obtain ⟨Ts, hq, hp⟩ := htarget.mp hu
        obtain ⟨T, hT⟩ := hcert'.mp hv
        exact ⟨Ts, T, hq, hp, hT⟩
      · rintro ⟨Ts, T, hq, hp, hT⟩
        have hv := hcert'.mpr ⟨T, hT⟩
        simpa only [restrictedSyntaxEval, hf, hu, ↓reduceIte, u] using hv

/-- Both original decoders are read from the ACTUAL successful saved
tapes. The certificate has no added caller-facing count or delimiter. -/
theorem restrictedSyntax_view_decodes (N m L : ℕ) (s : RestrictedStore)
    (hf : s.state.2 = true)
    (he : GrammarEntry restrictedTargetGrammarPorts N m L s)
    (hc : GrammarEntry restrictedCertGrammarPorts N m L s)
    (hs : (restrictedSyntaxEval N m s).state.2 = true)
    (Ts : List (BTree (Cell N m))) (T : BTree (Cell N m))
    (ht : RestrictedTypedView N m (restrictedSyntaxEval N m s) Ts T) :
    readFramedList (readTargetTree N m) (s.stk (.inl .source)) = some (Ts, []) ∧
      parseBitTree N m (s.stk (restrictedHeader .certificate)) = some T := by
  let u := originalTargetForestEval restrictedTargetGrammarPorts N m s
  let v := originalCertificateGrammarEval restrictedCertGrammarPorts N m u
  have hu : u.state.2 = true := by
    cases h : u.state.2 with
    | true => rfl
    | false => simp [restrictedSyntaxEval, hf, u, h] at hs
  have hout : restrictedSyntaxEval N m s = v := by simp [restrictedSyntaxEval, hf, hu, u, v]
  have hv : v.state.2 = true := by simpa only [hout] using hs
  have hto := originalTargetForest_saved_observation restrictedTargetGrammarPorts N m L s he hu
  have hco := originalCertificateGrammar_saved_observation restrictedCertGrammarPorts N m L u
    (restrictedTarget_cert_entry N m L s hc) hv
  have htw : v.stk restrictedTargetWord = u.stk restrictedTargetWord :=
    originalCertificateGrammar_outside restrictedCertGrammarPorts N m u restrictedTargetWord
      (by intro j; cases j <;> decide)
  have hcw : u.stk (restrictedHeader .certificate) = s.stk (restrictedHeader .certificate) :=
    originalTargetForest_outside restrictedTargetGrammarPorts N m s
      (restrictedHeader .certificate) (by intro j; cases j <;> decide)
  have hword : u.stk restrictedTargetWord = Ts.flatMap treeBits := by
    rw [← htw]
    simpa only [hout] using ht.target
  have hcount : readUnaryFrame (s.stk (.inl .source)) = some (Ts.length, Ts.flatMap treeBits) := by
    simpa only [restrictedTargetGrammarPorts, restrictedTargetGrammarMap, ← ht.count, hword] using hto.2.2.1
  constructor
  · have hm := readMany_encode treeBits (readTargetTree N m) readTargetTree_encode Ts []
    simpa only [readFramedList, hcount, List.append_nil] using hm
  · have hbits : s.stk (restrictedHeader .certificate) = treeBits T := by
      have hx : v.stk restrictedCertWord = s.stk (restrictedHeader .certificate) :=
        hco.2.2.1.trans hcw
      exact hx.symm.trans (by simpa only [hout] using ht.certificate)
    rw [hbits, parseBitTree_encode]

theorem restrictedPrefix_front_accepts (bits input cert rest : List Bool) (N m B : ℕ)
    (hp : readVerifierPair bits = some (input, cert))
    (hh : readDimensionedVerifierHeaders input.length (verifierBudgetCap input cert) input =
      some ((N, m, B), rest)) :
    (restrictedPrefixResult bits).state.2 = true ↔
      ∃ Ts T, Ts.length = m + 1 ∧
        readFramedList (readTargetTree N m) rest = some (Ts, []) ∧
        parseBitTree N m cert = some T := by
  have hr := (readVerifierFront_some bits input cert rest N m B).mpr ⟨hp, hh⟩
  have hd := verifierFront_success_fields restrictedFrontPorts bits input cert rest
    (fun _ => []) (by intro j; rfl) () N m B hp hh
  have hw := verifierFront_saved restrictedFrontPorts bits input cert (fun _ => []) () hp
  have hs := restrictedSyntax_accepts_iff N m bits.length (restrictedFrontStore bits) hd.1
    (restrictedFront_target_entry bits input cert rest N m B hp hh)
    (restrictedFront_cert_entry bits input cert rest N m B hp hh)
  simpa only [restrictedPrefixResult, hr, restrictedFrontStore, hd.2.1, hw.2] using hs

theorem restrictedPrefix_front_decodes (bits input cert rest : List Bool) (N m B : ℕ)
    (hp : readVerifierPair bits = some (input, cert))
    (hh : readDimensionedVerifierHeaders input.length (verifierBudgetCap input cert) input =
      some ((N, m, B), rest))
    (hf : (restrictedPrefixResult bits).state.2 = true)
    (Ts : List (BTree (Cell N m))) (T : BTree (Cell N m))
    (ht : RestrictedTypedView N m (restrictedPrefixResult bits) Ts T) :
    readFramedList (readTargetTree N m) rest = some (Ts, []) ∧ parseBitTree N m cert = some T := by
  have hr := (readVerifierFront_some bits input cert rest N m B).mpr ⟨hp, hh⟩
  have hd := verifierFront_success_fields restrictedFrontPorts bits input cert rest
    (fun _ => []) (by intro j; rfl) () N m B hp hh
  have hw := verifierFront_saved restrictedFrontPorts bits input cert (fun _ => []) () hp
  have he : restrictedPrefixResult bits = restrictedSyntaxEval N m (restrictedFrontStore bits) := by
    simp only [restrictedPrefixResult, hr]
  have hs := restrictedSyntax_view_decodes N m bits.length (restrictedFrontStore bits) hd.1
    (restrictedFront_target_entry bits input cert rest N m B hp hh)
    (restrictedFront_cert_entry bits input cert rest N m B hp hh)
    (by simpa only [he] using hf) Ts T (by simpa only [he] using ht)
  simpa only [restrictedFrontStore, hd.2.1, hw.2] using hs

theorem restrictedPipeline_front_semantics (bits input cert rest : List Bool) (N m B : ℕ)
    (hp : readVerifierPair bits = some (input, cert))
    (hh : readDimensionedVerifierHeaders input.length (verifierBudgetCap input cert) input =
      some ((N, m, B), rest)) :
    (restrictedPipelineResult bits).state.2 = restrictedBodyAnswer N m B rest cert := by
  have hr := (readVerifierFront_some bits input cert rest N m B).mpr ⟨hp, hh⟩
  cases hf : (restrictedPrefixResult bits).state.2 with
  | false =>
      have hv := restrictedPipelineResult_failed bits hf
      have hb : restrictedBodyAnswer N m B rest cert = false := by
        cases h : restrictedBodyAnswer N m B rest cert with
        | false => rfl
        | true =>
            obtain ⟨Ts, T, hrows, hcert, hvalid, _⟩ := (restrictedBodyAnswer_true_iff N m B rest cert).mp h
            have hq : Ts.length = m + 1 := by
              simp only [scanRawTargetValid, Bool.and_eq_true, decide_eq_true_eq] at hvalid
              exact hvalid.1.1.1.1.2
            have hyes := (restrictedPrefix_front_accepts bits input cert rest N m B hp hh).mpr
              ⟨Ts, T, hq, hrows, hcert⟩
            simp only [hf, Bool.false_eq_true] at hyes
      simpa only [hv, hf] using hb.symm
  | true =>
      obtain ⟨hi, ho⟩ := restrictedPrefix_success_boundary bits input cert rest N m B hp hh hf
      obtain ⟨_, hN, hm⟩ := (readDimensionedVerifierHeaders_some input.length
        (verifierBudgetCap input cert) input rest N m B).mp hh
      obtain ⟨Ts, T, ht, hans⟩ := restrictedGuards_original N m B bits.length
        (restrictedPrefixResult bits) hi ho hN hm
      obtain ⟨hrows, hcert⟩ := restrictedPrefix_front_decodes bits input cert rest N m B hp hh hf Ts T ht
      simpa only [restrictedPipelineResult, hr, restrictedBodyAnswer, hrows, hcert,
        hf, Bool.true_and] using hans

def restrictedSemanticAnswer (bits : List Bool) : Bool :=
  match readVerifierFront bits with
  | none => false
  | some ((_, cert), ((N, m, B), rest)) => restrictedBodyAnswer N m B rest cert

theorem restrictedPipeline_semantic_answer (bits : List Bool) :
    (restrictedPipelineResult bits).state.2 = restrictedSemanticAnswer bits := by
  cases hr : readVerifierFront bits with
  | none =>
      have ho := verifierFront_observation restrictedFrontPorts bits (fun _ => []) (by intro j; rfl) ()
      have hf : (restrictedFrontStore bits).state.2 = false :=
        (observeVerifierFront_none restrictedFrontPorts _).mp (by simpa [restrictedFrontStore, hr] using ho)
      simp only [restrictedPipelineResult, restrictedPrefixResult, restrictedSemanticAnswer, hr, hf]
  | some q =>
      rcases q with ⟨⟨input, cert⟩, ⟨⟨N, m, B⟩, rest⟩⟩
      obtain ⟨hp, hh⟩ := (readVerifierFront_some bits input cert rest N m B).mp hr
      simpa only [restrictedSemanticAnswer, hr] using restrictedPipeline_front_semantics bits input cert rest N m B hp hh

theorem restrictedBodyAnswer_as_record (N m B : ℕ) (rows cert : List Bool) :
    restrictedBodyAnswer N m B rows cert =
      match readFramedList (readTargetTree N m) rows with
      | some (Ts, []) => scanTargetRecord cert ⟨N, m, ⟨B, Ts⟩⟩
      | _ => false := by
  cases hr : readFramedList (readTargetTree N m) rows with
  | none => rfl
  | some pair =>
      rcases pair with ⟨Ts, rest⟩
      cases rest with
      | cons b bs => rfl
      | nil =>
          cases hc : parseBitTree N m cert <;>
            cases hv : scanRawTargetValid (⟨B, Ts⟩ : RawTargetRows N m) <;>
            simp [restrictedBodyAnswer, scanTargetRecord, hr, hc, hv]

/-- Merely regroup the ORIGINAL bounded header parser. No additional
well-formedness hypothesis or constructor-origin restriction is used. -/
theorem boundedEncodedTarget_headers (input cert : List Bool) :
    boundedEncodedTarget input cert =
      match readVerifierHeaders input.length (verifierBudgetCap input cert) input with
      | none => false
      | some ((N, m, B), rest) => restrictedBodyAnswer N m B rest cert := by
  cases h1 : readBoundedNatFrame input.length input with
  | none => simp [boundedEncodedTarget, parseBoundedTarget, parseBoundedTargetPrefix, readVerifierHeaders, h1]
  | some p =>
      rcases p with ⟨N, r1⟩
      cases h2 : readBoundedNatFrame input.length r1 with
      | none => simp [boundedEncodedTarget, parseBoundedTarget, parseBoundedTargetPrefix, readVerifierHeaders, h1, h2]
      | some p =>
          rcases p with ⟨m, r2⟩
          cases h3 : readSaturatedBinaryNatFrame (verifierBudgetCap input cert) r2 with
          | none => simp [boundedEncodedTarget, parseBoundedTarget, parseBoundedTargetPrefix, readVerifierHeaders, h1, h2, h3]
          | some p =>
              rcases p with ⟨B, rest⟩
              simp only [readVerifierHeaders, h1, h2, h3, Option.bind_some, Option.map_some]
              rw [restrictedBodyAnswer_as_record]
              cases h4 : readFramedList (readTargetTree N m) rest with
              | none => simp [boundedEncodedTarget, parseBoundedTarget, parseBoundedTargetPrefix, readVerifierHeaders, h1, h2, h3, h4]
              | some p =>
                  rcases p with ⟨Ts, after⟩
                  cases after <;>
                    simp [boundedEncodedTarget, parseBoundedTarget, parseBoundedTargetPrefix, readVerifierHeaders, h1, h2, h3, h4]

theorem boundedEncodedTarget_dimensioned (input cert : List Bool) :
    boundedEncodedTarget input cert =
      match readDimensionedVerifierHeaders input.length (verifierBudgetCap input cert) input with
      | none => false
      | some ((N, m, B), rest) => restrictedBodyAnswer N m B rest cert := by
  rw [boundedEncodedTarget_headers]
  cases hh : readVerifierHeaders input.length (verifierBudgetCap input cert) input with
  | none => simp [readDimensionedVerifierHeaders, hh]
  | some q =>
      rcases q with ⟨⟨N, m, B⟩, rest⟩
      by_cases hd : 0 < N ∧ 2 ≤ m
      · simp [readDimensionedVerifierHeaders, hh, hd]
      · simp [readDimensionedVerifierHeaders, hh, hd,
          restrictedBodyAnswer_bad_dimensions N m B rest cert hd]

theorem restrictedSemanticAnswer_eq_bounded (bits : List Bool) :
    restrictedSemanticAnswer bits = boundedPairVerifier bits := by
  cases hp : readVerifierPair bits with
  | none => simp [restrictedSemanticAnswer, readVerifierFront, boundedPairVerifier, hp]
  | some pair =>
      rcases pair with ⟨input, cert⟩
      rw [boundedPairVerifier, hp, boundedEncodedTarget_dimensioned]
      cases hh : readDimensionedVerifierHeaders input.length (verifierBudgetCap input cert) input with
      | none => simp [restrictedSemanticAnswer, readVerifierFront, hp, hh]
      | some q =>
          rcases q with ⟨⟨N, m, B⟩, rest⟩
          simp [restrictedSemanticAnswer, readVerifierFront, hp, hh]

/-- ALL original Boolean pair words, including malformed/count-too-large
headers, bad dimensions, wrong row counts, trailing bytes and out-of-range
cells. Exact budget clipping is removed by boundedPairVerifier_eq, whose
proof uses parsed_valid_target_bounds and parsed_verifier_score_bound.
The operational Q=(L+2)^2 bound is NOT a clipping justification. -/
theorem restrictedPipeline_original_bit (bits : List Bool) :
    (restrictedPipelineResult bits).state.2 = scanPairVerifier bits :=
  (restrictedPipeline_semantic_answer bits).trans
    ((restrictedSemanticAnswer_eq_bounded bits).trans (boundedPairVerifier_eq bits))

/- Still unclosed: the final ALL-PATH public tape-mass bound, final clean
one-bit routine composition and exact compiled haltList/FinTM2 package.
VerifierMachineWitness is not asserted here. EncodedSourceHardness is an
independent missing premise; source elaboration and kernel checks have not
occurred. The language is the restricted marked-star language only. -/

end PolytomyReductionModel.WholeVerifierController
