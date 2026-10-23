/-
Author: dot (OpenAI), 23 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

The successful ORIGINAL prefix enters the one shared guard inventory.
Fresh work banks and exact raw/parser/range observations are derived from
the real preceding stores, not reintroduced as component assumptions.
-/
import PolytomyRestrictedVerifierPrefix

namespace PolytomyReductionModel.WholeVerifierController

open Turing Lax218471.Subroutine Lax218471.Programs Lax218471Proofs

def restrictedGuardBank : RestrictedExtraPort → Bool
  | .front _ => false
  | .targetGrammar _ => false
  | .certGrammar _ => false
  | _ => true

theorem restrictedGuard_not_front (j : RestrictedExtraPort) (hj : restrictedGuardBank j = true)
    (k : VerifierFrontPort) : j ≠ .front k := by
  cases j <;> simp_all [restrictedGuardBank]

theorem restrictedGuard_not_target (j : RestrictedExtraPort) (hj : restrictedGuardBank j = true)
    (k : GrammarPort) : (.inr j : RestrictedPort) ≠ restrictedTargetGrammarPorts k := by
  cases j <;> cases k <;> simp_all [restrictedGuardBank, restrictedTargetGrammarPorts,
    restrictedTargetGrammarMap, restrictedHeader]

theorem restrictedGuard_not_cert (j : RestrictedExtraPort) (hj : restrictedGuardBank j = true)
    (k : GrammarPort) : (.inr j : RestrictedPort) ≠ restrictedCertGrammarPorts k := by
  cases j <;> cases k <;> simp_all [restrictedGuardBank, restrictedCertGrammarPorts,
    restrictedCertGrammarMap, restrictedHeader]

structure RestrictedGuardInv (m A B L : ℕ) (s : RestrictedStore) : Prop where
  target_length : (s.stk restrictedTargetWord).length ≤ L
  target_mask : (s.stk restrictedTargetMask).length ≤ (s.stk restrictedTargetWord).length
  cert_length : (s.stk restrictedCertWord).length ≤ L
  cert_mask : (s.stk restrictedCertMask).length ≤ (s.stk restrictedCertWord).length
  rows : s.stk (restrictedHeader .rows) = List.replicate m true
  types : s.stk (restrictedHeader .types) = List.replicate A true
  budget : s.stk (restrictedHeader .budget) = List.replicate B true
  fresh : ∀ j : RestrictedExtraPort, restrictedGuardBank j = true → s.stk (.inr j) = []

theorem RestrictedGuardInv.transport (m A B L : ℕ) (s t : RestrictedStore)
    (hs : RestrictedGuardInv m A B L s) (he : t.stk = s.stk) : RestrictedGuardInv m A B L t := by
  rcases hs with ⟨ht, htm, hc, hcm, hm, hA, hB, hz⟩
  exact ⟨by simpa [he] using ht, by simpa [he] using htm,
    by simpa [he] using hc, by simpa [he] using hcm,
    by simpa [he] using hm, by simpa [he] using hA,
    by simpa [he] using hB, by simpa [he] using hz⟩

structure RestrictedSyntaxObservation (N m : ℕ) (s : RestrictedStore) : Prop where
  target_parse : rawForestMaskParse (s.stk restrictedTargetWord).length (m + 1)
    (s.stk restrictedTargetWord) = some ([], s.stk restrictedTargetMask)
  target_range : forestMaskCellCheck N m (s.stk restrictedTargetWord) (s.stk restrictedTargetMask) = true
  cert_parse : rawForestMaskParse (s.stk restrictedCertWord).length 1
    (s.stk restrictedCertWord) = some ([], s.stk restrictedCertMask)
  cert_range : forestMaskCellCheck N m (s.stk restrictedCertWord) (s.stk restrictedCertMask) = true

theorem RestrictedSyntaxObservation.transport (N m : ℕ) (s t : RestrictedStore)
    (hs : RestrictedSyntaxObservation N m s) (he : t.stk = s.stk) : RestrictedSyntaxObservation N m t := by
  rcases hs with ⟨ht, htr, hc, hcr⟩
  exact ⟨by simpa [he] using ht, by simpa [he] using htr,
    by simpa [he] using hc, by simpa [he] using hcr⟩

/-- The actual successful front and both original grammars establish ONE
guard invariant and BOTH observed raw/typed bridges. No constructor-image
or freshly reset bank is a premise. Whole consumption has already been
checked, so every downstream residual is now explicitly the empty list. -/
theorem restrictedPrefix_success_boundary (bits input cert rest : List Bool) (N m B : ℕ)
    (hp : readVerifierPair bits = some (input, cert))
    (hh : readDimensionedVerifierHeaders input.length (verifierBudgetCap input cert) input =
      some ((N, m, B), rest))
    (hf : (restrictedPrefixResult bits).state.2 = true) :
    RestrictedGuardInv m (N + m * N + 3) B bits.length (restrictedPrefixResult bits) ∧
      RestrictedSyntaxObservation N m (restrictedPrefixResult bits) := by
  let u := restrictedFrontStore bits
  let v := originalTargetForestEval restrictedTargetGrammarPorts N m u
  let w := originalCertificateGrammarEval restrictedCertGrammarPorts N m v
  have hread := (readVerifierFront_some bits input cert rest N m B).mpr ⟨hp, hh⟩
  have hd := verifierFront_success_fields restrictedFrontPorts bits input cert rest
    (fun _ => []) (by intro j; rfl) () N m B hp hh
  rcases hd with ⟨huf, hur, hrL, huN, hum, huB, huA, hNpos, hmpos, hNl, hml, hBl, hAl⟩
  have hvf : v.state.2 = true := by
    cases hv : v.state.2 with
    | true => rfl
    | false =>
        simp [restrictedPrefixResult, hread, restrictedSyntaxEval, u, v, huf, hv] at hf
  have hout : restrictedPrefixResult bits = w := by
    simp [restrictedPrefixResult, hread, restrictedSyntaxEval, huf, hvf, u, v, w]
  have hwf : w.state.2 = true := by simpa only [hout] using hf
  have hte := restrictedFront_target_entry bits input cert rest N m B hp hh
  have hce := restrictedTarget_cert_entry N m bits.length u
    (restrictedFront_cert_entry bits input cert rest N m B hp hh)
  have ht := originalTargetForest_saved_observation restrictedTargetGrammarPorts N m bits.length u hte hvf
  have hc := originalCertificateGrammar_saved_observation restrictedCertGrammarPorts N m bits.length v hce hwf
  have htw : w.stk restrictedTargetWord = v.stk restrictedTargetWord :=
    originalCertificateGrammar_outside restrictedCertGrammarPorts N m v restrictedTargetWord
      (by intro j; cases j <;> decide)
  have htm : w.stk restrictedTargetMask = v.stk restrictedTargetMask :=
    originalCertificateGrammar_outside restrictedCertGrammarPorts N m v restrictedTargetMask
      (by intro j; cases j <;> decide)
  have hrows : w.stk (restrictedHeader .rows) = List.replicate m true :=
    (originalCertificateGrammar_operand restrictedCertGrammarPorts N m v .rows (by simp)).trans
      ((originalTargetForest_operand restrictedTargetGrammarPorts N m u .rows (by simp)).trans hum)
  have htypes : w.stk (restrictedHeader .types) = List.replicate (N + m * N + 3) true :=
    (originalCertificateGrammar_operand restrictedCertGrammarPorts N m v .types (by simp)).trans
      ((originalTargetForest_operand restrictedTargetGrammarPorts N m u .types (by simp)).trans huA)
  have hbudget : w.stk (restrictedHeader .budget) = List.replicate B true :=
    (originalCertificateGrammar_outside restrictedCertGrammarPorts N m v (restrictedHeader .budget)
      (by intro j; cases j <;> decide)).trans
      ((originalTargetForest_outside restrictedTargetGrammarPorts N m u (restrictedHeader .budget)
        (by intro j; cases j <;> decide)).trans huB)
  have hfresh (j : RestrictedExtraPort) (hj : restrictedGuardBank j = true) : w.stk (.inr j) = [] :=
    (originalCertificateGrammar_outside restrictedCertGrammarPorts N m v (.inr j)
      (restrictedGuard_not_cert j hj)).trans
      ((originalTargetForest_outside restrictedTargetGrammarPorts N m u (.inr j)
        (restrictedGuard_not_target j hj)).trans
        (verifierFront_outside restrictedFrontPorts bits (fun _ => []) () j
          (restrictedGuard_not_front j hj)))
  rw [hout]
  constructor
  · refine ⟨?_, ?_, hc.2.2.2.2.2.1, hc.2.2.2.2.2.2, hrows, htypes, hbudget, hfresh⟩
    · simpa only [htw] using ht.2.2.2.2.2.1
    · simpa only [htw, htm] using ht.2.2.2.2.2.2
  · refine ⟨?_, ?_, hc.2.2.2.1, hc.2.2.2.2.1⟩
    · simpa only [htw, htm] using ht.2.2.2.1
    · simpa only [htw, htm] using ht.2.2.2.2.1

/- Next: instantiate each of the eight concrete entry predicates from
RestrictedGuardInv, use their exact restored-stack contracts to carry
these TWO observations through the success-gated sequence, and establish
the original combined semantic answer. Failed-prefix storage bounds,
global time/mass and haltList packaging are still separate obligations.
No whole-verifier or kernel closure is claimed. -/

end PolytomyReductionModel.WholeVerifierController
