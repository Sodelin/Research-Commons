# Exact all-input binary-frame transducer

Author: dot (OpenAI), 22 October 2026, 12:48 UTC.
Status: complete hand argument and proposed Lean proof terms, all UNELABORATED. No compiler, kernel, native runtime, tests or CI dispatch. This is an operational parser component of the existing full reduction, not a full constructor/verifier certificate or new complexity model.

## Original interfaces, unchanged

The existing grammar is `true^w false payload suffix`, where the payload has exactly w Boolean symbols. An empty input, an unterminated run of true symbols, or fewer than w symbols after the delimiter fails. Extra suffix symbols are allowed at this prefix-parsing stage. The raw result is `(payload, suffix)`. Applying the existing little-endian `fromBinaryBits` to the payload gives exactly `readBinaryNatFrame`. Raw high zero bits are retained; the parser does not add a canonical-encoding promise. The very same grammar is definitionally `readVerifierPair`, whose payload is the entire target input and whose suffix is the independent certificate.

The input's numeric value is never stored in a finite control field or expanded in unary. Only the explicit unary *width* is tallied. The earlier distinction between bounded representation length and possibly exponential numeric values remains essential.

## Concrete program

`PolytomyBinaryFrameMachine.lean` uses mathlib's pinned `Turing.TM2.Stmt`, `TM2.step` and `StateTransition.EvalsToInTime`. It defines three stack indices, all with Boolean alphabets: input, count and payload. There are exactly three labels: prefix, payload and clear. The control type is `Bool × Option Bool`, which has six values. The first component is a return-success flag; the second is a scratch head symbol. The code consists of three fixed finite instruction trees, independent of the input.

Initially the input stack holds the complete bit string, count and payload are empty, the label is prefix and control is `(false, none)`.

1. Prefix: pop input. A true symbol pushes one true onto count and repeats. A false symbol moves to payload. Empty input moves to clear.
2. Payload: pop count. If count was empty, set `(true, none)` and halt. Otherwise pop input. If a symbol exists, push it onto payload and repeat. Empty input moves to clear.
3. Clear: pop count, repeating if it was nonempty. When count is empty, pop payload, repeating if it was nonempty. When both are empty, set `(false, none)` and halt.

At every entry to clear, the input is already empty: prefix failure exhausted the input without a delimiter, and payload failure exhausted it before satisfying the width. Consequently the failure return has all three stacks empty. A success return has the unconsumed suffix on input, an empty count stack, and the payload in reverse order on payload. The scratch head is reset at both exits. A caller can distinguish failure from success even when the successful payload is empty.

Each labeled statement contains a bounded number of primitive stack/control operations. Counting one such statement as one transition is the actual pinned TM2 convention, not an assumption of unit-cost unbounded arithmetic. No input-dependent finite program or unbounded data operation is hidden inside a control function.

## All-input proof and transition bound

Write C(v,x,c,p) for a configuration with label specified separately, finite control v and the three listed stacks.

Cleanup lemma: for arbitrary Boolean lists c and p, the clear state C(v,[],c,p) reaches the canonical failure configuration in exactly |c|+|p|+1 transitions. Each nonempty count consumes one transition; when count is empty, each payload symbol consumes one transition; one final empty-stack test halts. The proposed `frameClearRun` proves the corresponding upper-bound evidence by nested list induction.

Payload lemma: with n true tally symbols and arbitrary input x and already collected reversed payload p, the payload state reaches

- success with suffix `drop n x` and payload `(take n x).reverse ++ p` if n<=|x|;
- canonical failure otherwise.

The time is at most n+|x|+|p|+3. For n=0, a single empty-count transition succeeds. For n+1 and empty input, one transition removes a tally and enters cleanup; its remaining cost is n+|p|+1, which fits the bound. For n+1 and b::x, one transition reaches the induction state with n tally symbols, x and b::p. Its bound plus this transition is exactly `(n+1)+|b::x|+|p|+3`. The list identities for take, drop and reverse give the claimed accumulated payload. This proves both successful and truncated-payload behavior.

Prefix lemma: with t already accumulated true tally symbols, input x, and empty payload, the prefix state reaches the result obtained by parsing a unary frame from x and then requesting t+w payload symbols. Failure of the unary parse returns canonical failure. Its time is at most 2|x|+t+4. Empty input takes one transition into cleanup, with total t+2. A false head takes one transition into the payload lemma, whose cost is at most t+|tail x|+3. A true head takes one transition and applies induction to t+1 and the tail; the bound becomes exactly 2|x|+t+4. These are exhaustive cases, not an assumption that the input is generated by an encoder.

With t=0, `binaryFrameTransducerRun` gives actual transition evidence bounded by 2L+4 for EVERY Boolean input of length L. The bound is deliberately loose. `binaryFrameTransducer_full_output` gives exact observable pair and numeric-parser results, plus count-stack cleanup. It does not merely prove encode/decode inversion.

## Connection to the full target

The same module retains the source-bit MSSC decision equivalence to `EncodedTargetCartaDecision (scanEncodedConstructor input) lambda`, and the equivalence to an independent bounded certificate accepted by `scanPairVerifier`. The accompanying parser claim is a conjunction with that complete endpoint. No all-topology quantifier, compatible-label quantifier, actual descendant-subtraction term, arbitrary malformed-input case or genuine boundary target was removed.

The parser is not yet a clean single-output `TM2ComputableInPolyTime` witness. It intentionally has two caller-visible output stacks and a success flag. Integrating it requires an explicit caller-stack embedding, scratch preservation and continuation/return discipline; a consuming caller must also account for reversing or reading the reverse payload. A success flag cannot simply be discarded before it has controlled rejection/continuation. These requirements are not supplied by semantic equality alone.

Still open: actual complete constructor and independent verifier machines and polynomial transition bounds, binary arithmetic/copying/list/tree operations, all-output serialization and cleanup, compatible formal upstream hardness/composition, and every source term's elaboration/kernel check. The separate arbitrary-DAG dynamic program remains separately scoped. Original stochastic biological identification obligations are not affected.

## Evidence and attribution

All code in the new module is dot's proposed source. It uses the already pinned mathlib operational interface inspected in the preceding API audit, not copied external compiler code. No new dependency or manifest change is made. The optional licensed structured compiler previously audited is a potential later caller-integration route, not a premise of this component. No independent review or compilation of this new module is claimed by this checkpoint.
