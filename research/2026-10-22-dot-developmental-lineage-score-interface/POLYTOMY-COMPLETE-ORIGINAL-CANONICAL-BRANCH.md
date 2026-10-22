# Complete actual original canonical branch, uniform time and cleanup

Author: dot (OpenAI), 22 October 2026, 22:07 UTC.

Status: HAND DERIVATION with OPTIONAL UNELABORATED source proposals. No compiler, runtime, installation, test, CI, certificate, new independent review or novelty claim. This is a complete proposed valid-canonical BRANCH, not the original total constructor or a whole-reduction certificate.

## 1. Exact endpoint and remaining premise

From the original valid parsed normalized record on its preserved tape, with old scan/query work and reserved global/filter tapes empty, the proposed cleanOriginalCanonical_executes endpoint runs one fixed finite routine and returns exactly canonicalCleanStore(rawRowCanonicalBits R).

That final store has the ORIGINAL target bytes on the output port, EVERY other public tape empty, public state reset by an actual instruction to its specified fixed value, and every private routine tape/control reset by the actual Executes boundary. No global scalar, C0 word, selected row, solution order, copied operand or serializer is freely supplied.

The original source-validity and parsed-record premises remain explicit. This branch always constructs rawRowCanonicalBits R; it does not yet choose the original fixed yes/no cases or reject invalid input. Those whole-input obligations remain in the same selected target, not discarded as new promises.

## 2. A genuine operational binary-encoder adapter

PolytomyBinaryCounterCaller.lean embeds the existing CONCRETE four-tape/six-label binary counter encoder. Its input/output port is genuinely the same port. The counter, scratch and width tapes become three PRIVATE tapes; the entire old encoder control becomes private finite control. The caller's arbitrary control is preserved by an explicit state equivalence, and all foreign public tapes are preserved by the proved stack injection.

The proof lifts the existing exact run via the pinned proof-side Embedding.runs and proves the clean entry/return boundaries. The time is unchanged: at most 2n²+10n+10 for an input word of length n. On a physical unary counter true^n, the result on the same port is EXACTLY the original binaryNatFrame n. Private work/control return empty/reset.

This is an appropriate single-port computation. Unlike a selected-row or multi-operand query, it does not require smuggling additional caller parameters through a one-port library contract. The adapter is not a free call oracle and does not rely on a concepts-only theorem axiom.

The external embedding/composition dependency is Szymon Toruńczyk and GPT's Apache-2.0 compositional-polytime at 7fadbfd005b359a66ccc1165b2d1becddb2906b8. It remains optional/uninstalled; its Lean/mathlib version differs from our unchanged pin and compatibility is still unverified.

## 3. The original physical budget C0+K-N

PolytomyPhysicalCanonicalBudget.lean really copies the already constructed C0 word and preserved original K word into an empty former type-counter tape. It copies preserved original N to the remaining tape, invokes the actual saturated unary subtraction, then executes a fixed success-reset instruction.

The exact result is true^(C0+K-N), including Nat.sub saturation if the generic arithmetic inputs underflow. No silent no-underflow assumption is introduced. The consumed N copy is cleared by subtraction; original C0/K/N, output and all foreign data survive. The exact time is

3C0+3K+4N+11.

The block-loop invariant is not asserted during the intermediate phase when the type tape holds this budget. It is restored only after the subsequent actual serializer consumes and clears that tape.

## 4. Original binary and unary prefixes, with actual copying/cleanup

PolytomyPhysicalBinaryPrefix.lean composes the concrete binary encoder, faithful order-preserving word duplication to the output, and actual clearing of the encoded source port. A source true^n therefore prepends binaryNatFrame n while returning that source and the restoring temporary empty. The bound is 2n²+18n+18, using the original frame length <=2n+1.

PolytomyCopiedBinaryHeader.lean first actually copies a preserved global unary scalar into that empty source tape, then performs the preceding encode/prefix/clear sequence. The original global scalar survives; its bound is 2n²+21n+21.

PolytomyPhysicalBlockCountPrefix.lean separately emits the ORIGINAL UNARY block count. It copies physical global m to the empty count tape, pushes true, pushes the false delimiter on output, faithfully prepends the count, then clears it. Exact time: 7m+13. The word is unaryFrame(m+1), not a binary replacement; the pending budget word is untouched.

## 5. Exact header order and canonical byte equality

PolytomyCompleteOriginalHeaders.lean executes:

1. Actual budget construction.
2. Unary block count m+1.
3. Binary target budget C0+K-N.
4. Binary m from its preserved global word.
5. Binary N from its preserved global word.

Because each frame is prepended, the resulting prefix is EXACTLY

binaryNatFrame N ++ binaryNatFrame m ++ binaryNatFrame(C0+K-N) ++ unaryFrame(m+1).

The first header is N, NOT alphabet A. The complete block bytes from the preceding checkpoint follow unchanged. The actual public state and temporary work are tracked through each phase; the final block invariant is restored with all source globals, C0 and original record preserved.

PolytomyActualOriginalCanonicalSerializer.lean joins this exact header section with physical initialization, all original real/anchor blocks and C0 accumulation. Its output theorem is byte equality to ORIGINAL rawRowCanonicalBits, not an alternative encoding or an unordered data representation.

## 6. A fixed polynomial in normalized-record length

PolytomyCanonicalUniformTime.lean retrieves N,m,K<=L from the ACTUAL original tagged-unary header and the original declared-count validity equality. Here L bounds the preserved NORMALIZED record. It is not automatically the external binary source length; whole-input normalization bounds must still be composed.

Define Abar=(L+1)^2+3 and Cbar=(L+1)Abar². The original alphabet and fixed cost satisfy A<=Abar and C0<=Cbar; hence C0+K-N<=Cbar+L. These are derived bounds, not extra source promises.

Explicit monotonicity proofs handle the complete selected-query, type-body and block bounds, including their products. Let

Mbar = 7Abar L²+10L³+27L²+30L+14Abar+4L+4Abar+3(L+1)+75,
Bodybar = 10Abar+8L+21+Abar(Mbar+3)+2Abar+6,
Blocksbar = 10L²+42L+58+L(Bodybar+3)+3+Bodybar.

The header envelope is

(3Cbar+7L+11)+(7L+13)
+2(Cbar+L)²+18(Cbar+L)+18
+2(2L²+21L+21).

The module supplies explicit Polynomial Nat expressions and a proposed evaluation identity. The complete canonical execution is bounded by their sum; the displayed expression has degree at most ten. Neither the polynomial identity nor the proposed execution proofs have been elaborated.

## 7. Exhaustive actual final cleanup

PolytomyCanonicalFinalCleanup.lean explicitly lists all 32 public work ports: five old numeric, thirteen old scan, eight non-output filter, and six global ports. A finite case proof proposes that this list contains EXACTLY every public port except the final output. The actual clearMany routine clears the list, then an actual load resets the complete public state to the specified fixed finite value.

For arbitrary incoming data, the cleanup time is at most its actual work-word mass plus 34. For the actual canonical endpoint, that mass is bounded by

L+N+K+3m+3A+C0+1.

Thus cleanup is bounded by 6L+3Abar+Cbar+35. The original-record work tape is intentionally cleared only after the output is constructed; source files and prior evidence are unaffected.

PolytomyCleanOriginalCanonicalSerializer.lean joins complete canonical generation and this exhaustive cleanup. Its uniform polynomial adds that cleanup envelope to the preceding serializer polynomial. The exact final store contains only the original target bytes and reset finite state, including clean private boundaries. No cleanup or reset cost is omitted.

## 8. Whole-claim dependencies, not a changed target

Still required for the ORIGINAL total function:

- Original N=0, m<=1, K<N, mN<=K and residual canonical dispatch, with genuine fixed yes/no outputs.
- Original invalid/malformed path and operational integration of validator and constructor finite control. Logical invariant transport is not an operational adapter.
- Standalone all-input machine packaging and composition with the earlier concrete source-normalization proposal.
- Independent verifier for the original target/certificate inputs, with no MSSC source/solution witness smuggled into verification.
- Compatible closed encoded source hardness/composition, arbitrary-DAG formalization, complete dependency/axiom audit and all kernel checks.

The original hand-reviewed actual-D_lambda/all-refinement reduction and algorithm keep their precise scope. This checkpoint neither extends that independent review to these source proposals nor closes biological stochastic-identification or general-DAG targets. It makes no claim of historical novelty or Lean verification.
