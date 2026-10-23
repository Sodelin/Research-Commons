/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

The front-to-ORIGINAL-syntax join in the one fixed restricted inventory.
No caller supplies fresh banks anew between phases. The first grammar
receives the actual post-header residual; the second receives the saved
unframed certificate. Both calls are success-gated in the final program.
-/
import PolytomyRestrictedVerifierProgram

namespace PolytomyReductionModel.WholeVerifierController

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def restrictedFrontStore (bits : List Bool) : RestrictedStore :=
  verifierFrontResult restrictedFrontPorts bits (fun _ => []) ()

theorem restrictedFront_target_entry (bits input cert rest : List Bool) (N m B : ℕ)
    (hp : readVerifierPair bits = some (input, cert))
    (hh : readDimensionedVerifierHeaders input.length (verifierBudgetCap input cert) input =
      some ((N, m, B), rest)) :
    GrammarEntry restrictedTargetGrammarPorts N m bits.length (restrictedFrontStore bits) := by
  have hd := verifierFront_success_fields restrictedFrontPorts bits input cert rest
    (fun _ => []) (by intro j; rfl) () N m B hp hh
  have hlen := readVerifierPair_payload_length bits input cert hp
  rcases hd with ⟨hf, hrest, hrL, hN, hm, hB, hA, hNpos, hmpos, hNl, hml, hBl, hAl⟩
  refine ⟨?_, hm, hA, ?_⟩
  · change ((restrictedFrontStore bits).stk (.inl .source)).length ≤ bits.length
    rw [hrest]
    omega
  · intro j hjs hjm hjA
    have he := verifierFront_outside restrictedFrontPorts bits (fun _ => []) ()
      (.targetGrammar j) (by intro k; cases k <;> decide)
    cases j <;> simp_all [restrictedTargetGrammarPorts, restrictedTargetGrammarMap,
      restrictedFrontStore, restrictedHeader, restrictedFrontPorts]

theorem restrictedFront_cert_entry (bits input cert rest : List Bool) (N m B : ℕ)
    (hp : readVerifierPair bits = some (input, cert))
    (hh : readDimensionedVerifierHeaders input.length (verifierBudgetCap input cert) input =
      some ((N, m, B), rest)) :
    GrammarEntry restrictedCertGrammarPorts N m bits.length (restrictedFrontStore bits) := by
  have hd := verifierFront_success_fields restrictedFrontPorts bits input cert rest
    (fun _ => []) (by intro j; rfl) () N m B hp hh
  have hs := verifierFront_saved restrictedFrontPorts bits input cert (fun _ => []) () hp
  have hlen := readVerifierPair_payload_length bits input cert hp
  rcases hd with ⟨hf, hrest, hrL, hN, hm, hB, hA, hNpos, hmpos, hNl, hml, hBl, hAl⟩
  refine ⟨?_, hm, hA, ?_⟩
  · change ((restrictedFrontStore bits).stk (restrictedHeader .certificate)).length ≤ bits.length
    rw [hs.2]
    omega
  · intro j hjs hjm hjA
    have he := verifierFront_outside restrictedFrontPorts bits (fun _ => []) ()
      (.certGrammar j) (by intro k; cases k <;> decide)
    cases j <;> simp_all [restrictedCertGrammarPorts, restrictedCertGrammarMap,
      restrictedFrontStore, restrictedHeader, restrictedFrontPorts]

variable {K F : Type} [DecidableEq K]

theorem originalTargetForest_outside (p : GrammarPorts K) (N m : ℕ)
    (s : CountdownStore K F) (k : K) (hk : ∀ j : GrammarPort, k ≠ p j) :
    (originalTargetForestEval p N m s).stk k = s.stk k := by
  have hs : (originalForestGrammarEval p N m s).stk k = s.stk k := by
    rw [originalForestGrammar_stacks]
    exact forestSyntax_extra (grammarSyntaxPorts p) s k
      (hk .source) (hk .count) (hk .tail) (hk .pending) (hk .reverse) (hk .nodeMask)
  simpa [originalTargetForestEval, targetForestEndEval, targetCountExpected,
    targetCountPushOp, wholeInputOp, clearStackEval, guardedCellCompare_stacks,
    wordDuplicateEval, Op.apply, hk .cellSource] using hs

theorem originalTargetForest_operand (p : GrammarPorts K) (N m : ℕ)
    (s : CountdownStore K F) (j : GrammarPort) (hj : j = .rows ∨ j = .types) :
    (originalTargetForestEval p N m s).stk (p j) = s.stk (p j) := by
  have hs : (originalForestGrammarEval p N m s).stk (p j) = s.stk (p j) := by
    apply originalForestGrammar_extra
    all_goals rcases hj with rfl | rfl <;> decide
  have hjc : j ≠ .cellSource := by rcases hj with rfl | rfl <;> decide
  simpa [originalTargetForestEval, targetForestEndEval, targetCountExpected,
    targetCountPushOp, wholeInputOp, clearStackEval, guardedCellCompare_stacks,
    wordDuplicateEval, Op.apply, hjc] using hs

/-- The first grammar does not consume the saved certificate or touch its
fresh work bank. Shared m,A operands are restored, on rejected paths too. -/
theorem restrictedTarget_cert_entry (N m L : ℕ) (s : RestrictedStore)
    (hs : GrammarEntry restrictedCertGrammarPorts N m L s) :
    GrammarEntry restrictedCertGrammarPorts N m L
      (originalTargetForestEval restrictedTargetGrammarPorts N m s) := by
  have hc := originalTargetForest_outside restrictedTargetGrammarPorts N m s
    (restrictedHeader .certificate) (by intro j; cases j <;> decide)
  have hm := originalTargetForest_operand restrictedTargetGrammarPorts N m s .rows (by simp)
  have hA := originalTargetForest_operand restrictedTargetGrammarPorts N m s .types (by simp)
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa only [restrictedCertGrammarPorts, restrictedCertGrammarMap, hc] using hs.1
  · exact hm.trans hs.2.1
  · exact hA.trans hs.2.2.1
  · intro j hjs hjm hjA
    have hx := originalTargetForest_outside restrictedTargetGrammarPorts N m s
      (.inr (.certGrammar j)) (by intro k; cases k <;> decide)
    have hz := hs.2.2.2 j hjs hjm hjA
    cases j <;> simp_all [restrictedCertGrammarPorts, restrictedCertGrammarMap]

theorem restrictedGate_failed (r : RestrictedRoutine) (s : RestrictedStore)
    (hf : s.state.2 = false) : (restrictedGate r).Executes s s 2 := by
  simpa [restrictedGate, cleanupNoop, Op.apply] using
    RoutineControl.branch_false Prod.snd r (Atom.routine cleanupNoop) hf (Atom.executes cleanupNoop s)

theorem restrictedGate_passed (r : RestrictedRoutine) (s t : RestrictedStore) (n : ℕ)
    (hf : s.state.2 = true) (he : r.Executes s t n) :
    (restrictedGate r).Executes s t (n + 1) :=
  RoutineControl.branch_true Prod.snd r (Atom.routine cleanupNoop) hf he

def restrictedSyntaxEval (N m : ℕ) (s : RestrictedStore) : RestrictedStore :=
  if s.state.2 then
    let u := originalTargetForestEval restrictedTargetGrammarPorts N m s
    if u.state.2 then originalCertificateGrammarEval restrictedCertGrammarPorts N m u else u
  else s

def restrictedSyntaxBound (N m L : ℕ) : ℕ :=
  L * (18 * L + 4 * m + 4 * (N + m * N + 3) + 45) + 29 * L + 8 * m + 56 +
  ((L + 2) * (18 * (L + 2) + 4 * m + 4 * (N + m * N + 3) + 45) + 25 * (L + 2) + 38) + 4

/-- Actual two-grammar join with one entry store. An initial rejection
skips BOTH syntax routines. Target rejection also skips the local-reset
certificate parser, so it cannot resurrect acceptance. -/
theorem restrictedSyntax_executes (N m L : ℕ) (s : RestrictedStore)
    (ht : GrammarEntry restrictedTargetGrammarPorts N m L s)
    (hc : GrammarEntry restrictedCertGrammarPorts N m L s) :
    ∃ n ≤ restrictedSyntaxBound N m L,
      restrictedSyntaxRoutine.Executes s (restrictedSyntaxEval N m s) n := by
  cases hf : s.state.2 with
  | false =>
      have h1 := restrictedGate_failed (originalTargetForestRoutine restrictedTargetGrammarPorts) s hf
      have h2 := restrictedGate_failed (originalCertificateGrammarRoutine restrictedCertGrammarPorts) s hf
      exact ⟨2 + 2, by unfold restrictedSyntaxBound; omega,
        by simpa [restrictedSyntaxRoutine, restrictedSyntaxEval, hf] using
          RoutineComposition.seq_executes _ _ h1 h2⟩
  | true =>
      obtain ⟨a, ha, h1⟩ := originalTargetForest_executes restrictedTargetGrammarPorts N m L s ht
      have hfirst := restrictedGate_passed _ s _ a hf h1
      let u := originalTargetForestEval restrictedTargetGrammarPorts N m s
      cases hu : u.state.2 with
      | false =>
          have hlast := restrictedGate_failed (originalCertificateGrammarRoutine restrictedCertGrammarPorts) u hu
          exact ⟨(a + 1) + 2, by unfold restrictedSyntaxBound; omega,
            by simpa [restrictedSyntaxRoutine, restrictedSyntaxEval, hf, hu, u] using
              RoutineComposition.seq_executes _ _ hfirst hlast⟩
      | true =>
          obtain ⟨b, hb, h2⟩ := originalCertificateGrammar_executes restrictedCertGrammarPorts N m L u
            (restrictedTarget_cert_entry N m L s hc)
          have hlast := restrictedGate_passed _ u _ b hu h2
          exact ⟨(a + 1) + (b + 1), by unfold restrictedSyntaxBound; omega,
            by simpa [restrictedSyntaxRoutine, restrictedSyntaxEval, hf, hu, u] using
              RoutineComposition.seq_executes _ _ hfirst hlast⟩

/- This is the concrete front-to-two-grammar boundary, not the final
verifier proof. The all-word front/syntax composition must still expose
the two successful saved masks and prove the one guard-bank invariant;
the eight guards, exact semantic answer, mass/time and haltList join are
not supplied by a declaration name or by this entry theorem. -/

theorem restrictedSyntax_failed (s : RestrictedStore) (hf : s.state.2 = false) :
    restrictedSyntaxRoutine.Executes s s 4 := by
  exact RoutineComposition.seq_executes _ _
    (restrictedGate_failed (originalTargetForestRoutine restrictedTargetGrammarPorts) s hf)
    (restrictedGate_failed (originalCertificateGrammarRoutine restrictedCertGrammarPorts) s hf)

def restrictedPrefixResult (bits : List Bool) : RestrictedStore :=
  match readVerifierFront bits with
  | none => restrictedFrontStore bits
  | some q => restrictedSyntaxEval q.2.1.1 q.2.1.2.1 (restrictedFrontStore bits)

def restrictedPrefixBound (L : ℕ) : ℕ := verifierFrontBound L + restrictedSyntaxBound L L L

theorem restrictedPrefixBound_expansion (L : ℕ) :
    restrictedPrefixBound L = 14 * L ^ 3 + 110 * L ^ 2 + 447 * L + 603 := by
  rw [restrictedPrefixBound, verifierFrontBound_expansion]
  unfold restrictedSyntaxBound
  ring

theorem restrictedSyntaxBound_uniform (N m L : ℕ) (hN : N ≤ L) (hm : m ≤ L) :
    restrictedSyntaxBound N m L ≤ restrictedSyntaxBound L L L := by
  have hp := Nat.mul_le_mul hm hN
  have hA : N + m * N + 3 ≤ L + L * L + 3 := by omega
  have hfirst := Nat.mul_le_mul_left L (show 18 * L + 4 * m + 4 * (N + m * N + 3) + 45 ≤
    18 * L + 4 * L + 4 * (L + L * L + 3) + 45 by omega)
  have hsecond := Nat.mul_le_mul_left (L + 2)
    (show 18 * (L + 2) + 4 * m + 4 * (N + m * N + 3) + 45 ≤
      18 * (L + 2) + 4 * L + 4 * (L + L * L + 3) + 45 by omega)
  unfold restrictedSyntaxBound
  omega

/-- ONE emitted prefix on ALL original pair words. Neither malformed
headers nor rejected target syntax enter a flag-resetting later parser.
The original target/certificate words may be arbitrary Boolean lists. -/
theorem restrictedPrefix_executes (bits : List Bool) :
    ∃ n ≤ restrictedPrefixBound bits.length,
      restrictedPrefixRoutine.Executes (restrictedInitialStore bits) (restrictedPrefixResult bits) n := by
  obtain ⟨a, ha, hfront⟩ := verifierFront_executes restrictedFrontPorts bits
    (fun _ => []) (by intro j; rfl) () false false
  have ho := verifierFront_observation restrictedFrontPorts bits (fun _ => []) (by intro j; rfl) ()
  cases hr : readVerifierFront bits with
  | none =>
      have hf : (restrictedFrontStore bits).state.2 = false :=
        (observeVerifierFront_none restrictedFrontPorts _).mp (by simpa [restrictedFrontStore, hr] using ho)
      have hsyn := restrictedSyntax_failed (restrictedFrontStore bits) hf
      refine ⟨a + 4, by unfold restrictedPrefixBound restrictedSyntaxBound; omega, ?_⟩
      simpa only [restrictedPrefixRoutine, restrictedInitialStore, restrictedPrefixResult,
        hr, restrictedFrontStore] using RoutineComposition.seq_executes _ _ hfront hsyn
  | some q =>
      rcases q with ⟨⟨input, cert⟩, ⟨⟨N, m, B⟩, rest⟩⟩
      obtain ⟨hp, hh⟩ := (readVerifierFront_some bits input cert rest N m B).mp hr
      have ht := restrictedFront_target_entry bits input cert rest N m B hp hh
      have hc := restrictedFront_cert_entry bits input cert rest N m B hp hh
      obtain ⟨b, hb, hsyn⟩ := restrictedSyntax_executes N m bits.length (restrictedFrontStore bits) ht hc
      have hlen := readVerifierPair_payload_length bits input cert hp
      obtain ⟨hread, hdN, hdm⟩ :=
        (readDimensionedVerifierHeaders_some input.length (verifierBudgetCap input cert) input rest N m B).mp hh
      obtain ⟨hN, hm, hB, hA⟩ :=
        readVerifierHeaders_bounds input.length (verifierBudgetCap input cert) input rest N m B hread
      have hbound := restrictedSyntaxBound_uniform N m bits.length (by omega) (by omega)
      refine ⟨a + b, by unfold restrictedPrefixBound; omega, ?_⟩
      simpa only [restrictedPrefixRoutine, restrictedInitialStore, restrictedPrefixResult,
        hr, restrictedFrontStore] using RoutineComposition.seq_executes _ _ hfront hsyn

/-- Successful grammar output retains the exact RAW parser observation
and checked finite leaf ranges needed by EVERY subsequent typed bridge.
The saved word is the real post-count input, not a reconstructed encoding. -/
theorem originalForestGrammar_saved_observation (p : GrammarPorts K) (N m L : ℕ)
    (s : CountdownStore K F) (hs : GrammarEntry p N m L s)
    (hf : (originalForestGrammarEval p N m s).state.2 = true) :
    let v := originalForestGrammarEval p N m s
    readUnaryFrame (s.stk (p .source)) = some ((v.stk (p .count)).length, v.stk (p .tail)) ∧
      rawForestMaskParse (v.stk (p .tail)).length (v.stk (p .count)).length (v.stk (p .tail)) =
        some (v.stk (p .source), v.stk (p .nodeMask)) ∧
      forestMaskCellCheck N m (v.stk (p .tail)) (v.stk (p .nodeMask)) = true ∧
      (v.stk (p .tail)).length ≤ L ∧ (v.stk (p .nodeMask)).length ≤ (v.stk (p .tail)).length := by
  let u := forestSyntaxEval (grammarSyntaxPorts p) s
  have hu : u.state.2 = true := by
    cases h : u.state.2 with
    | true => rfl
    | false =>
        simp [originalForestGrammarEval, u, h, countdownReset, countdownResetOp, Op.apply] at hf
  have ho := forestSyntax_observation (grammarSyntaxPorts p) s (grammarEntry_syntax p N m L s hs)
  have hraw : originalForestSyntaxRead (s.stk (p .source)) =
      some ((u.stk (p .count)).length, u.stk (p .tail), u.stk (p .source), u.stk (p .nodeMask)) := by
    simpa only [forestSyntaxObservation, grammarSyntaxPorts, hu, ↓reduceIte] using ho.symm
  obtain ⟨hcount, hmask⟩ := (originalForestSyntaxRead_success _ _ _ _ _).mp hraw
  have hfun : rawRangeCheck m (N + m * N + 3) = legalSuffixCellCheck N m :=
    funext (rawRangeCheck_original N m)
  have hcheck : forestMaskCellCheck N m (u.stk (p .tail)) (u.stk (p .nodeMask)) = true := by
    simpa [originalForestGrammarEval, u, hu, countdownReset, countdownResetOp,
      Op.apply, rangeAllResult, grammarRangePorts, hfun, forestMaskCellCheck] using hf
  have hb := forestSyntax_success_bounds (grammarSyntaxPorts p) L s hs.1
    (grammarEntry_syntax p N m L s hs) hu
  have hx := originalForestGrammar_stacks p N m s
  dsimp only
  simpa only [hx, grammarSyntaxPorts] using And.intro hcount ⟨hmask, hcheck, hb⟩

/-- Whole target success supplies q=m+1 and empty residual in the saved
raw mask observation. Thus no later scan may infer consumption merely
from one of its own subtree-scoped component theorems. -/
theorem originalTargetForest_saved_observation (p : GrammarPorts K) (N m L : ℕ)
    (s : CountdownStore K F) (hs : GrammarEntry p N m L s)
    (hf : (originalTargetForestEval p N m s).state.2 = true) :
    let v := originalTargetForestEval p N m s
    v.stk (p .source) = [] ∧ (v.stk (p .count)).length = m + 1 ∧
      readUnaryFrame (s.stk (p .source)) = some (m + 1, v.stk (p .tail)) ∧
      rawForestMaskParse (v.stk (p .tail)).length (m + 1) (v.stk (p .tail)) =
        some ([], v.stk (p .nodeMask)) ∧
      forestMaskCellCheck N m (v.stk (p .tail)) (v.stk (p .nodeMask)) = true ∧
      (v.stk (p .tail)).length ≤ L ∧ (v.stk (p .nodeMask)).length ≤ (v.stk (p .tail)).length := by
  let u := originalForestGrammarEval p N m s
  have hc : u.stk (p .cellSource) = [] :=
    (originalForestGrammar_extra p N m s .cellSource (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)).trans
      (hs.2.2.2 .cellSource (by decide) (by decide) (by decide))
  have he := targetForestEnd_result p m (u.stk (p .count)).length u hc
  have hflag : (u.state.2 && decide ((u.stk (p .count)).length = m + 1)) &&
      !(u.stk (p .source)).head?.isSome = true := by
    simpa only [originalTargetForestEval, he, cellCompareFlagStore] using hf
  obtain ⟨hfirst, hlast⟩ := Bool.and_eq_true.mp hflag
  obtain ⟨hgrammar, hcountBool⟩ := Bool.and_eq_true.mp hfirst
  have hcount : (u.stk (p .count)).length = m + 1 := of_decide_eq_true hcountBool
  have hempty : u.stk (p .source) = [] := by
    cases hw : u.stk (p .source) <;> simp_all
  have ho := originalForestGrammar_saved_observation p N m L s hs hgrammar
  have hstk : (originalTargetForestEval p N m s).stk = u.stk := by
    change (targetForestEndEval p m (u.stk (p .count)).length u).stk = _
    rw [he]
    rfl
  dsimp only
  rw [hstk]
  refine ⟨hempty, hcount, ?_, ?_, ho.2.2.1, ho.2.2.2⟩
  · simpa only [hcount] using ho.1
  · simpa only [hcount, hempty] using ho.2.1

theorem originalCertificateGrammar_outside (p : GrammarPorts K) (N m : ℕ)
    (s : CountdownStore K F) (k : K) (hk : ∀ j : GrammarPort, k ≠ p j) :
    (originalCertificateGrammarEval p N m s).stk k = s.stk k := by
  have hx := forestSyntax_extra (grammarSyntaxPorts p) (certificatePrefixEval p s) k
    (hk .source) (hk .count) (hk .tail) (hk .pending) (hk .reverse) (hk .nodeMask)
  simpa [originalCertificateGrammarEval, wholeInputOp, Op.apply,
    originalForestGrammar_stacks, certificatePrefixEval, certificatePushOp, hk .source] using hx

theorem originalCertificateGrammar_operand (p : GrammarPorts K) (N m : ℕ)
    (s : CountdownStore K F) (j : GrammarPort) (hj : j = .rows ∨ j = .types) :
    (originalCertificateGrammarEval p N m s).stk (p j) = s.stk (p j) := by
  have hx : (originalForestGrammarEval p N m (certificatePrefixEval p s)).stk (p j) =
      (certificatePrefixEval p s).stk (p j) := by
    apply originalForestGrammar_extra
    all_goals rcases hj with rfl | rfl <;> decide
  have hjs : j ≠ .source := by rcases hj with rfl | rfl <;> decide
  simpa [originalCertificateGrammarEval, wholeInputOp, certificatePrefixEval,
    certificatePushOp, Op.apply, hjs] using hx

/-- The internally paid U(1) adapter leaves the saved word equal to the
ORIGINAL unframed certificate. The returned mask covers precisely that
whole tree, with q=1 and empty remainder established by actual guards. -/
theorem originalCertificateGrammar_saved_observation (p : GrammarPorts K) (N m L : ℕ)
    (s : CountdownStore K F) (hs : GrammarEntry p N m L s)
    (hf : (originalCertificateGrammarEval p N m s).state.2 = true) :
    let v := originalCertificateGrammarEval p N m s
    v.stk (p .source) = [] ∧ (v.stk (p .count)).length = 1 ∧
      v.stk (p .tail) = s.stk (p .source) ∧
      rawForestMaskParse (v.stk (p .tail)).length 1 (v.stk (p .tail)) =
        some ([], v.stk (p .nodeMask)) ∧
      forestMaskCellCheck N m (v.stk (p .tail)) (v.stk (p .nodeMask)) = true ∧
      (v.stk (p .tail)).length ≤ L ∧ (v.stk (p .nodeMask)).length ≤ (v.stk (p .tail)).length := by
  let u := originalForestGrammarEval p N m (certificatePrefixEval p s)
  have hf' : ((wholeInputOp (p .source)).apply u).state.2 = true := hf
  obtain ⟨hgrammar, hempty⟩ := (wholeInput_true_iff (p .source) u).mp hf'
  have ho := originalForestGrammar_saved_observation p N m (L + 2) (certificatePrefixEval p s)
    (certificatePrefix_entry p N m L s hs) hgrammar
  have hqt : (1, s.stk (p .source)) = ((u.stk (p .count)).length, u.stk (p .tail)) := by
    apply Option.some.inj
    simpa only [certificatePrefix_source, readUnaryFrame_encode] using ho.1
  have hcount : (u.stk (p .count)).length = 1 := (congrArg Prod.fst hqt).symm
  have htail : u.stk (p .tail) = s.stk (p .source) := (congrArg Prod.snd hqt).symm
  have hstk : (originalCertificateGrammarEval p N m s).stk = u.stk := rfl
  dsimp only
  rw [hstk]
  refine ⟨hempty, hcount, htail, ?_, ho.2.2.1, ?_, ho.2.2.2.2⟩
  · simpa only [hcount, hempty] using ho.2.1
  · simpa only [htail] using hs.1

end PolytomyReductionModel.WholeVerifierController
