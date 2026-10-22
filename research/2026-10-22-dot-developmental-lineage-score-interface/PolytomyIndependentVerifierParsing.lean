/-
Author: dot (OpenAI), 22 October 2026.
OPTIONAL SOURCE PROPOSAL, UNELABORATED. No execution or certificate.

Reuse of the existing forward raw-frame transducer for the ORIGINAL pair
framing. This is not the separate block-pair convention adapter. The raw
tree component does not replace the independent target's range/clade/score
predicates. Its all-input bounded-budget adapter remains unchanged.
-/
import PolytomyTreePrefixCaller
import PolytomySaturatedVerifier

namespace PolytomyReductionModel

open Turing Lax218471.Subroutine Lax218471Proofs

variable {K F : Type} [DecidableEq K]

theorem readRawBinaryFrame_is_original_pair (bits : List Bool) :
    readRawBinaryFrame bits = readVerifierPair bits := rfl

/-- The source port returns the certificate, the output port the exact
    forward-order target. Reverse scratch and private tally are clean.
    Malformed framing returns failure with all three named ports empty. -/
theorem originalVerifierPair_split_executes (source reverse output : K)
    (hsr : source ≠ reverse) (hso : source ≠ output) (hro : reverse ≠ output)
    (base : K → List Bool) (frame : F) (bits : List Bool) :
    ∃ n ≤ 3 * bits.length + 5,
      (frameForwardRoutine source reverse output hsr).Executes
        (frameCallerStore source reverse (Function.update base output []) frame false bits [])
        (frameForwardResult source reverse output base frame (readVerifierPair bits)) n := by
  simpa only [readRawBinaryFrame_is_original_pair] using
    frameForward_executes source reverse output hsr hso hro base frame bits

theorem originalVerifierPair_split_result (source reverse output : K)
    (hso : source ≠ output) (hsr : source ≠ reverse) (hro : reverse ≠ output)
    (base : K → List Bool) (frame : F) (input cert : List Bool) :
    let s := frameForwardResult source reverse output base frame (some (input, cert))
    s.state = (frame, true) ∧ s.stk output = input ∧ s.stk source = cert ∧ s.stk reverse = [] := by
  simp [frameForwardResult, frameCallerStore, hso, hsr, hro, Ne.symm hro]

/- Remaining original-verifier obligations: actual bounded header parsing,
   typed-cell ranges, exact tree/node interval navigation, independent
   target guard, leaf uniqueness/set equality, every supplied fixed clade,
   original star score/budget, complete all-word composition and cleanup.
   No constructor-origin premise, source solution witness, fixed comb shape
   or changed stochastic model is introduced. -/

end PolytomyReductionModel
