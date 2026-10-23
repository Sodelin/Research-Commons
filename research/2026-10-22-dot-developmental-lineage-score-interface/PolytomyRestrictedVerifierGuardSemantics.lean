/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

One observed typed forest and certificate for the EIGHT concrete guards.
Codec determinism identifies the existential typed outputs of different
components; it is not an assumption of biological identifiability. The
whole original-input parser equivalence and clean halt remain separate.
-/
import PolytomyRestrictedVerifierPipeline

namespace PolytomyReductionModel.WholeVerifierController

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

theorem typedForest_bits_injective_length {N m : ℕ}
    (Ts Us : List (BTree (Cell N m))) (hl : Ts.length = Us.length)
    (hw : Ts.flatMap treeBits = Us.flatMap treeBits) : Ts = Us := by
  have ht := readMany_encode treeBits (readTargetTree N m) readTargetTree_encode Ts []
  have hu := readMany_encode treeBits (readTargetTree N m) readTargetTree_encode Us []
  simp only [List.append_nil] at ht hu
  rw [hl, hw, hu] at ht
  exact (Prod.mk.inj (Option.some.inj ht)).1.symm

theorem typedTree_bits_injective {N m : ℕ} (T U : BTree (Cell N m))
    (hw : treeBits T = treeBits U) : T = U := by
  have ht := parseBitTree_encode T
  rw [hw, parseBitTree_encode U] at ht
  exact (Option.some.inj ht).symm

structure RestrictedTypedView (N m : ℕ) (s : RestrictedStore)
    (Ts : List (BTree (Cell N m))) (T : BTree (Cell N m)) : Prop where
  count : Ts.length = m + 1
  target : s.stk restrictedTargetWord = Ts.flatMap treeBits
  certificate : s.stk restrictedCertWord = treeBits T

theorem RestrictedTypedView.transport (N m : ℕ) (s t : RestrictedStore)
    (Ts : List (BTree (Cell N m))) (T : BTree (Cell N m))
    (hs : RestrictedTypedView N m s Ts T) (he : t.stk = s.stk) :
    RestrictedTypedView N m t Ts T :=
  ⟨hs.count, by simpa only [he] using hs.target, by simpa only [he] using hs.certificate⟩

theorem restrictedTypedView_observed (N m : ℕ) (s : RestrictedStore)
    (hs : RestrictedSyntaxObservation N m s) :
    ∃ Ts T, RestrictedTypedView N m s Ts T := by
  obtain ⟨Ts, T, hq, hw, hc, _⟩ := allCladesAnswer_observed_typed N m (m + 1)
    (s.stk restrictedTargetWord) (s.stk restrictedTargetMask)
    (s.stk restrictedCertWord) (s.stk restrictedCertMask) [] []
    hs.target_parse hs.cert_parse hs.target_range hs.cert_range
  exact ⟨Ts, T, hq, by simpa only [List.append_nil] using hw,
    by simpa only [List.append_nil] using hc⟩

/-- The score's actual Eval flag, proved from its masked aggregate rather
than from an unproved uniqueness-of-execution principle. -/
theorem scoreBudget_flag_observed_typed {K F : Type} [DecidableEq K]
    (p : ScorePorts K) (N m B L : ℕ) (s : CountdownStore K F)
    (hs : ScoreAllEntry p m (N + m * N + 3) L s)
    (hscore : s.stk (p .score) = []) (rest : List Bool)
    (hparse : rawForestMaskParse (s.stk (p (.outer .originalWord))).length 1
      (s.stk (p (.outer .originalWord))) = some (rest, s.stk (p (.outer .originalMask))))
    (hcheck : forestMaskCellCheck N m (s.stk (p (.outer .originalWord)))
      (s.stk (p (.outer .originalMask))) = true) :
    ∃ T : BTree (Cell N m), s.stk (p (.outer .originalWord)) = treeBits T ++ rest ∧
      (scoreBudgetResult p m (N + m * N + 3) B s).state.2 =
        decide (scanStarScore (N + m * N + 3) Prod.snd T ≤ B) := by
  obtain ⟨Rs, hlen, hw, hm⟩ := (rawForestMaskParse_all_words _ rest _ 1).mp hparse
  cases Rs with
  | nil => simp at hlen
  | cons R Rs =>
      have hz : Rs = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hlen; omega)
      subst Rs
      have hR := (forestMaskCellCheck_iff N m [R] rest).mp (by simpa only [← hw, ← hm] using hcheck)
      obtain ⟨T, hT⟩ := (rawTreeValid_iff_typed N m R).mp (hR R (by simp))
      have hword : s.stk (p (.outer .originalWord)) = treeBits T ++ rest := by
        simpa [rawForestWord, ← hT, rawTreeCodes_bits] using hw
      have hmask : s.stk (p (.outer .originalMask)) = rawNodeMask (rawTreeCodes T) := by
        simpa [rawForestNodeMask, ← hT] using hm
      have hv := scoreMask_tree N m (rawTreeCodes T) rest (rawTreeCodes_valid T)
      rw [rawTreeCodes_bits, scanStarScore_rawTreeCodes] at hv
      have hsuccess := scoreAll_success p m (N + m * N + 3) L s hs
        (by simpa only [hword, hmask] using hv.1)
      have hsval : ((scoreAllEval p m (N + m * N + 3) s).stk (p .score)).length =
          scanStarScore (N + m * N + 3) Prod.snd T := by
        rw [hsuccess.2, hword, hmask, hv.2, hscore, List.append_nil, List.length_replicate]
      exact ⟨T, hword, by simp only [scoreBudgetResult, hsuccess.1, hsval, Bool.true_and]⟩

def restrictedStepSpec {N m : ℕ} (Ts : List (BTree (Cell N m)))
    (T : BTree (Cell N m)) (B : ℕ) : RestrictedGuardStep → Bool
  | .uniqueTarget => decide ((Ts.flatMap scanLeaves).Nodup)
  | .mixed => Ts.all (scanMixed Prod.snd)
  | .coverage => decide (scanDistinctCount ((Ts.flatMap scanLeaves).map Prod.snd) = N + m * N + 3)
  | .markers => Ts.all scanMarkers
  | .uniqueCert => decide ((scanLeaves T).Nodup)
  | .sets => scanSetEq (scanLeaves T) (Ts.flatMap scanLeaves)
  | .clades => Ts.all (fun U => scanRefines U T)
  | .score => decide (scanStarScore (N + m * N + 3) Prod.snd T ≤ B)

theorem restrictedStep_flag (g : RestrictedGuardStep) (N m B L : ℕ)
    (s : RestrictedStore) (Ts : List (BTree (Cell N m))) (T : BTree (Cell N m))
    (hi : RestrictedGuardInv m (N + m * N + 3) B L s)
    (ho : RestrictedSyntaxObservation N m s) (ht : RestrictedTypedView N m s Ts T) :
    (restrictedStepEval m (N + m * N + 3) B g s).state.2 = restrictedStepSpec Ts T B g := by
  have target_unique (Us : List (BTree (Cell N m))) (hq : Us.length = m + 1)
      (hw : s.stk restrictedTargetWord = Us.flatMap treeBits ++ []) : Us = Ts := by
    apply typedForest_bits_injective_length Us Ts (hq.trans ht.count.symm)
    simpa only [List.append_nil] using hw.symm.trans ht.target
  have cert_unique (Us : List (BTree (Cell N m))) (hq : Us.length = 1)
      (hw : s.stk restrictedCertWord = Us.flatMap treeBits ++ []) : Us = [T] := by
    apply typedForest_bits_injective_length Us [T] (by simpa only [List.length_singleton] using hq)
    simpa only [List.append_nil, List.flatMap_cons, List.flatMap_nil] using hw.symm.trans ht.certificate
  cases g with
  | uniqueTarget =>
      obtain ⟨Us, hq, hw, ha⟩ := uniqueAllAnswer_observed_typed N m (m + 1)
        (s.stk restrictedTargetWord) (s.stk restrictedTargetMask) [] ho.target_parse ho.target_range
      rw [target_unique Us hq hw] at ha
      exact ha
  | mixed =>
      obtain ⟨Us, hq, hw, ha⟩ := mixedAllAnswer_observed_typed N m (m + 1)
        (s.stk restrictedTargetWord) (s.stk restrictedTargetMask) [] ho.target_parse ho.target_range
      rw [target_unique Us hq hw] at ha
      exact ha
  | coverage =>
      obtain ⟨Us, hq, hw, ha⟩ := coverageAnswer_observed_typed N m (m + 1)
        (s.stk restrictedTargetWord) (s.stk restrictedTargetMask) [] ho.target_parse ho.target_range
      rw [target_unique Us hq hw] at ha
      exact ha
  | markers =>
      exact rowMarkersAll_flag_typed restrictedMarkerPorts restrictedTargetWord (.inr .markerCounter)
        (by intro j; cases j <;> decide) (by intro j; cases j <;> decide) (by decide)
        N m L s (restricted_marker_entry m (N + m * N + 3) B L s hi) Ts []
        (by simpa only [List.append_nil] using ht.target) ht.count
  | uniqueCert =>
      obtain ⟨Us, hq, hw, ha⟩ := uniqueAllAnswer_observed_typed N m 1
        (s.stk restrictedCertWord) (s.stk restrictedCertMask) [] ho.cert_parse ho.cert_range
      rw [cert_unique Us hq hw] at ha
      simpa only [restrictedStepEval, restrictedStepSpec, uniqueAllResult,
        List.flatMap_cons, List.flatMap_nil, List.append_nil] using ha
  | sets =>
      obtain ⟨Us, Vs, hq, hr, hw, hc, ha⟩ := cellSetAnswer_observed_typed_forests
        restrictedSetPorts N m (m + 1) 1 s [] [] ho.target_parse ho.cert_parse ho.target_range ho.cert_range
      rw [target_unique Us hq hw, cert_unique Vs hr hc] at ha
      simpa only [restrictedStepEval, restrictedStepSpec, cellSetResult,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, scanSetEq, Bool.and_comm] using ha
  | clades =>
      obtain ⟨Us, U, hq, hw, hc, ha⟩ := allCladesAnswer_observed_typed N m (m + 1)
        (s.stk restrictedTargetWord) (s.stk restrictedTargetMask)
        (s.stk restrictedCertWord) (s.stk restrictedCertMask) [] []
        ho.target_parse ho.cert_parse ho.target_range ho.cert_range
      have hU : U = T := typedTree_bits_injective U T (by
        simpa only [List.append_nil] using hc.symm.trans ht.certificate)
      rw [target_unique Us hq hw, hU] at ha
      exact ha
  | score =>
      obtain ⟨U, hw, ha⟩ := scoreBudget_flag_observed_typed restrictedScorePorts N m B L s
        (restricted_score_entry m (N + m * N + 3) B L s hi) (hi.fresh _ rfl) []
        ho.cert_parse ho.cert_range
      have hU : U = T := typedTree_bits_injective U T (by
        simpa only [List.append_nil] using hw.symm.trans ht.certificate)
      rw [hU] at ha
      exact ha

/-- Every later guard sees the SAME typed trees because every concrete
step restores the full stack function. Rejection is absorbing even when
the local guard's standalone flag would overwrite a previous failure. -/
theorem restrictedSteps_flag (gs : List RestrictedGuardStep) (N m B L : ℕ)
    (s : RestrictedStore) (Ts : List (BTree (Cell N m))) (T : BTree (Cell N m))
    (hi : RestrictedGuardInv m (N + m * N + 3) B L s)
    (ho : RestrictedSyntaxObservation N m s) (ht : RestrictedTypedView N m s Ts T) :
    (restrictedStepsEval m (N + m * N + 3) B gs s).state.2 =
      s.state.2 && gs.all (restrictedStepSpec Ts T B) := by
  induction gs generalizing s with
  | nil => simp only [restrictedStepsEval, List.all_nil, Bool.and_true]
  | cons g gs ih =>
      cases hf : s.state.2 with
      | false =>
          have he := (restrictedSteps_failed (g :: gs) m (N + m * N + 3) B s hf).2
          simp only [he, hf, Bool.false_and]
      | true =>
          obtain ⟨_, _, _, hstk, _⟩ := restrictedStep_executes g m (N + m * N + 3) B L s hi
          have hu := RestrictedGuardInv.transport _ _ _ _ s _ hi hstk
          have hou := RestrictedSyntaxObservation.transport N m s _ ho hstk
          have htu := RestrictedTypedView.transport N m s _ Ts T ht hstk
          have hr := ih _ hu hou htu
          have hg := restrictedStep_flag g N m B L s Ts T hi ho ht
          simpa only [restrictedStepsEval, hf, ↓reduceIte, List.all_cons,
            Bool.true_and, hg] using hr

theorem restrictedStepSpec_original (N m B : ℕ) (Ts : List (BTree (Cell N m)))
    (T : BTree (Cell N m)) (hN : 0 < N) (hm : 2 ≤ m) (hq : Ts.length = m + 1) :
    restrictedGuardSteps.all (restrictedStepSpec Ts T B) =
      scanRawTargetValid (⟨B, Ts⟩ : RawTargetRows N m) &&
        scanRawCertificate (⟨B, Ts⟩ : RawTargetRows N m) T := by
  have hcode : scanDistinctCount ((Ts.flatMap scanLeaves).map (fun a => terminalCode N m a.2)) =
      scanDistinctCount ((Ts.flatMap scanLeaves).map Prod.snd) := by
    have he : (Ts.flatMap scanLeaves).map (fun a => terminalCode N m a.2) =
        ((Ts.flatMap scanLeaves).map Prod.snd).map (terminalCode N m) := by
      simp only [List.map_map, Function.comp_def]
    rw [he, scanDistinctCount_map_injective (terminalCode N m) (terminalCode_injective N m)]
  simp only [restrictedGuardSteps, List.all_cons, List.all_nil, restrictedStepSpec,
    scanRawTargetValid, scanRawCertificate, scanRowLeaves, hN, hm, hq, decide_true,
    Bool.true_and, Bool.and_true, hcode, Bool.and_assoc, Bool.and_left_comm, Bool.and_comm]

/-- The complete eight-guard semantic conjunction for the exact marked
star language, on observed parser outputs. This does NOT yet identify the
all-word prefix failure cases with the original target decoder. -/
theorem restrictedGuards_original (N m B L : ℕ) (s : RestrictedStore)
    (hi : RestrictedGuardInv m (N + m * N + 3) B L s)
    (ho : RestrictedSyntaxObservation N m s) (hN : 0 < N) (hm : 2 ≤ m) :
    ∃ Ts T, RestrictedTypedView N m s Ts T ∧
      (restrictedStepsEval m (N + m * N + 3) B restrictedGuardSteps s).state.2 =
        s.state.2 && (scanRawTargetValid (⟨B, Ts⟩ : RawTargetRows N m) &&
          scanRawCertificate (⟨B, Ts⟩ : RawTargetRows N m) T) := by
  obtain ⟨Ts, T, ht⟩ := restrictedTypedView_observed N m s ho
  refine ⟨Ts, T, ht, ?_⟩
  rw [restrictedSteps_flag restrictedGuardSteps N m B L s Ts T hi ho ht,
    restrictedStepSpec_original N m B Ts T hN hm ht.count]

end PolytomyReductionModel.WholeVerifierController
