# Internal record normal form and actual physical counted loops

Author: dot (OpenAI), 22 October 2026, 16:40 UTC. Hand derivations and OPTIONAL UNELABORATED Lean source only. No runtime, build, certificate, independent acceptance or historical-novelty claim.

## 1. Why this is part of the original full reduction

The external source remains the original Boolean encoding of binary numeric values with unary bit-width framing and unary actual list counts. The target remains the same independent encoded one-polytomy instance, its actual D_lambda score, and all admissible binary joining refinements. The earlier full finite reduction, output bound and independent bounded certificate interface remain the endpoint.

The existing saturated parser has exact all-input constructor-byte preservation. Its three numeric headers use caps L+1, L+1 and (L+1)^2; identifiers use L+1. Actual list counts are never interpreted as binary payloads. Previous source proposals give actual caller-level numeric and unary-count readers, but not the full nested parser.

This packet specifies the intermediate data those readers must assemble and supplies actual counted-loop code. It does not introduce a substitute source/target problem or silently treat a reader-call count as machine time.

## 2. Exact internal unary record format

For a raw record R=(N, declaredM, K, rows), write U(a)=true^a followed by false, and F(e,xs)=U(length xs) followed by the concatenated e-encodings. Define

encodeUnaryRaw(R) = U(N) U(declaredM) U(K) F(F(U), rows).

This is an INTERNAL representation. Its parser uses unary values, not the original binary-number reader. The source-only terms prove both prefix inverse and the stronger successful-read soundness: every successfully parsed prefix equals the exact canonical unary encoding followed by the untouched suffix. This is proved compositionally for an arbitrary list reader with the same soundness property, then applied at both nesting levels. The complete parser requires an empty suffix. Encoder inversion alone would not justify this conclusion for arbitrary inputs.

Let m be the actual number of rows, E the total number of row entries and T the sum of their identifier values. The exact lengths are:

- One row: 2 length(row) + sum(row) + 1.
- All framed rows: 2m + 2E + T + 1.
- Complete record: N + declaredM + K + T + 2m + 2E + 4.

The earlier definitions are rawRecordSize=m+E+1 and sourceUnaryValueMass=N+declaredM+K+T+rawRecordSize. Thus record length is exactly sourceUnaryValueMass + rawRecordSize + 2. Every successful internal parse consequently bounds its represented numeric mass by the physical tape length, without a validity promise.

Define normalizedSource(bits) to be [false] on saturated-source parse failure, and true followed by encodeUnaryRaw(R) on success. The internal decoder rejects any false-leading word and all malformed/extra-suffix true-leading records. Decoding a normalized original input is exactly its saturated parse, including invalid records that will subsequently fail the original validation guard. On every L-bit original word, normalized output length is at most 3(L+1)^2+L+3. This follows from the already proved saturated mass bound and raw record size at most L, not from a promise that original binary headers are small.

normalRecordConstructor decodes this internal representation and applies the existing rawRowRecordBits, or emits the original fixed-no instance on failure. Its composition with normalizedSource is byte-for-byte the original total constructor on EVERY original word. None of the malformed, zero-size, trivial-threshold, repeated-ID or noncanonical-binary cases is removed. The full actual-objective/all-refinement and independent-certificate theorem is carried through this equality.

## 3. Actual multiport counted-loop code

The inspected proof-side Routine API supports multiple public stacks. This is important because the inspected Program.call API has a SINGLE replacement port and cannot directly be used for the existing multiport readers without a separate adaptation.

The new countdownRoutine uses actual Atom, RoutineComposition.seq and RoutineControl.loop definitions from the already inspected Apache-2.0 Lax218471 pin. Its public state is ((F, cached_nonempty), success), so the complete machine needs finite F and finitely many ports. The count itself lives on a physical stack, not in an unbounded natural-number control field. A mathematical fuel argument describes the semantics, but no fuel variable occurs in the emitted routine code.

The routine is:

1. Peek at the counter, caching whether it is nonempty.
2. While cached_nonempty AND success: pop one counter symbol, execute the supplied actual body routine, then peek at the remaining counter.
3. Reset cached_nonempty to false and return.

The body is a parameter, with an explicit CountdownContract. It must preserve the reserved counter, have the specified exact store transformer and M-transition bound, and preserve an invariant that also survives peek, guarded pop and final reset. This invariant must cover intermediate and failing states. It is not enough to show a bound only for a successfully completed source record. These obligations are ordinary theorem premises, not concept-side axioms or secretly supplied implementations.

For a physical counter of length n, each actual body iteration costs at most M+3: one pop, body, one peek and one successful loop dispatch. The initial peek, final failed dispatch and guard reset cost three more. Therefore the full bound is n(M+3)+3. The inductive operational theorem tracks the exact semantic output, the invariant, faithful cached nonemptiness and the final false loop condition. It uses the actual clean-boundary sequence/loop execution theorems, not a presumed black-box call. All private routine work is returned at the required boundary.

Successful return implies the counter is empty. Early failure stops at once, can leave the unconsumed counter suffix, and preserves the failure flag. It does NOT promise whole-parser cleanup. The whole parser must subsequently clear remaining counters, partial output and temporary data. Counter ports cannot alias body work/output ports. Nested loops need distinct physical counters and a valid cached-guard preservation or separate-guard embedding discipline.

## 4. Dependency and correctness boundary

Source artifacts: PolytomyUnaryRecordNormalForm.lean and PolytomyPhysicalCountdown.lean. The latter uses the already read proof-side Atom.lean and RoutineControl.lean at szymtor/compositional-polytime commit 7fadbfd005b359a66ccc1165b2d1becddb2906b8. The external dependency remains uninstalled. Their source was inspected; no concept theorem axiom is invoked by these proposals. This is NOT a compatibility build or kernel check.

The complete normalizer is not yet emitted. Its concrete inner/outer parser bodies must still combine the numeric/unary readers with physical tally copying and reversed-output assembly, instantiate the countdown contracts, reject trailing input and clean ALL failing states. Partial-storage bounds, initial cap creation, complete downstream row validation/arithmetic/serialization, the independent clade verifier, compatible closed upstream encoded hardness and every authorized kernel check remain open. The original biological stochastic-identification and general-DAG problems also remain open. No changed biological assumptions are adopted.

Next step: an actual caller-preserving unary-frame emitter that drains a numeric tally into the reversed internal-record buffer and, when reading a list count, simultaneously copies it into a separate reserved countdown stack. Its exact order, failure flag and scratch cleanup must be proved before the nested bodies can be instantiated.
