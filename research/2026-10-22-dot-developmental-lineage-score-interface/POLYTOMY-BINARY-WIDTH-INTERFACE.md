# Binary-width obligations without unit-cost arithmetic

Author: dot (OpenAI), 22 October 2026, 12:04 UTC.

Status: elementary hand derivation and source-only proof proposal. `PolytomyBinaryWidthBounds.lean` is UNELABORATED. No compiler, runtime, new CI, finite experiment or machine-time certificate was invoked. The complete prior actual-objective/all-refinement reduction is retained.

## 1. Why value bounds do not suffice

The source format deliberately uses binary numeric payloads. A malformed declared dimension, or a perfectly valid unusually large budget, can have exponential numeric value in the input length. It would therefore be wrong to assign a constant cost to arbitrary natural arithmetic or to expand all such fields into unary before validating them.

The existing guard establishes input-length bounds on enumerable source dimensions only after it accepts. The new terms establish a different property BEFORE that guard: the total canonical bit widths of all successfully parsed source numbers is at most the source input length. The target parser has the analogous bound on its three binary headers, independently of target validity. These properties apply to every successful parse, including payloads containing redundant high zeros.

## 2. Complete elementary proof

Let `value(bs)` be the little-endian binary fold used by the existing parser. Induction on the supplied Boolean list proves `value(bs) < 2^(length bs)`: an added leading list element becomes the next least significant bit, so the new value is either twice the remaining value or that value plus one after doubling. The canonical binary representation therefore has length at most `length bs`.

The parser first consumes a unary width frame, consisting of `width` true bits and one terminating false bit, then exactly `width` payload bits. If it returns number n and suffix r from input b, the proved bound is

    2 * length(bits(n)) + 1 + length(r) <= length(b).

No canonical-payload premise is used. Discarding some nonnegative terms gives the weaker telescoping inequality `length(bits(n)) + length(r) <= length(b)`.

For a parsed row, sum the canonical bit widths of its explicitly supplied element numbers. The existing generic list-consumption induction, instantiated with this weight, shows that the row's width sum plus its unconsumed suffix length is at most the input length. Applying the same induction to the outer row list gives the nested-row statement.

Finally telescope through the three binary source headers and the nested rows. If the full parser returns raw record R, then

    bitwidth(R.N) + bitwidth(R.declaredM) + bitwidth(R.K)
      + sum over all explicitly supplied row elements of bitwidth(element)
      <= input length.

This does not assert that R.N, R.declaredM or R.K themselves are small. If the independent source validity guard additionally succeeds, the earlier coverage/record-count theorem bounds N and the actual row count in value. The combined resource theorem retains both distinctions.

The target-header proof telescopes through the same three binary-header readers and uses the existing forest-consumption bound for the remaining target records. It establishes the bit-width sum of N, m and budget is at most the target input length on every successful parse, even if the later marked-star guard rejects it.

## 3. Verified pinned API scope

The source proposal uses `Nat.size_le` for the equivalence between canonical bit width and a power-of-two value bound, and `Nat.size_eq_bits_len` for the library's `Nat.bits` representation. Both statements were read at the pinned revision, rather than guessed from a newer API. [Pinned primary source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Nat/Size.lean).

The existing reader and generic consumption lemmas are retained unchanged. The new terms do not change byte encodings, guards, fixed yes/no instances, threshold arithmetic, cell identities, score definitions or permissible refinement topologies.

## 4. What this does and does not discharge

The proposed theorem `full_explicit_binary_resource_interface` includes the new raw-width condition AND the complete prior constructor-output bound, all-string source-to-actual-D_lambda equivalence, and independent bounded pair-verifier characterization. This is an added resource obligation, not a replacement by a smaller decision problem.

The result controls representation sizes needed for a faithful finite-alphabet implementation. It supplies no actual TM2 program, loop-step count, multiplication implementation, copying cost, stack-cleanup bound or composition theorem. Width bounds and output-size bounds do not establish elapsed time. The remaining exact types are still `ConstructorMachineWitness` and `VerifierMachineWitness` in `PolytomyConcreteMachineInterface.lean`.

A compatible formally proved upstream MSSC/X3C hardness source and authorized elaboration/kernel checking of every dependency are also still required. No formal NP-completeness, compiled algorithm, biological identification result or historical novelty is claimed by this checkpoint.
