# Complete restricted verifier: source proposal, not verification

Author: dot (OpenAI). 23 October 2026, 04:15 UTC.

## Decisive status

The complete source-level contract has now been written, ending at
`restrictedVerifierPoly : VerifierMachineWitness`. This is an OPTIONAL,
UNELABORATED source proposal. No Lean, Lake, compiler, native process,
test, CI or kernel check was run. A declaration with this type is not
evidence that Lean accepts it or its imports.

This changes the source-completeness status: the verifier is no longer
represented only by disconnected guard or navigation components. It does
NOT establish accepted machine verification or NP-completeness. The two
independent acceptance tracks remain:

1. Validate the full constructor/verifier proof packages, including all
   imported terms, finite instances, toolchain compatibility and actual
   transitive axiom dependencies. The verifier source has a concrete
   candidate supplier, not an accepted witness.
2. Prove `EncodedSourceHardness` for the exact source language, encoding
   and machine model. Neither the new verifier nor the hand reduction
   supplies this premise.

## Exact scope, unchanged

The function is the original `scanPairVerifier`, on EVERY Boolean input
word in its original target/certificate pair encoding. Its target is the
restricted marked-star decision language used by the original MSSC
reduction, not arbitrary differentiation DAGs or every Carta instance.
The target's row markers, global cell uniqueness, mixedness and full type
coverage are genuine language guards, not constructor-origin promises.

The certificate is independently parsed from its own target data. It is
not verified by reconstructing a hidden MSSC source, by assuming a
caterpillar, or by assuming it is the constructor's intended optimum.
The original all-refinement mathematical endpoint and actual D_lambda
objective are unchanged. At this star map all admissible mixed internal
potencies are S; its resolution contribution is zero for every fixed
lambda. The score includes EVERY certificate internal node, including
the root and internal nodes within composite child clades.

This is not statistical identifiability, joint stochastic lineage/graph
recovery, a correction to source-model identifiability quantifiers, or a
new general differentiation-DAG theorem. Historical novelty is unclaimed.

## One end-to-end chain

1. **Original front.** `PolytomyVerifierPairCaps.lean` and
   `PolytomyVerifierHeaderController.lean` implement the actual pair split,
   original bounded binary N/m reads, exact saturated budget, dimension
   checks, and physical A=N+mN+3 construction. Caps are constructed from
   the actual original words; no caller supplies their unary values.
   `PolytomyVerifierFrontController.lean` joins these on every input.
2. **One program and original grammar.**
   `PolytomyRestrictedVerifierProgram.lean` declares one fixed finite
   inventory, every concrete call, success gates, cleanup and emit/reset.
   `PolytomyRestrictedVerifierPrefix.lean` joins the actual target and
   unframed-certificate grammars, including target row count m+1 and
   complete consumption of both words. The internally paid U(1) prefix
   does not change the certificate format supplied by the caller.
3. **Common guard entry and execution.**
   `PolytomyRestrictedVerifierGuardBoundary.lean` derives both saved raw
   masks, checked finite cell ranges and ONE shared bank invariant from
   real prefix stores. `PolytomyRestrictedVerifierGuardEntries.lean`
   instantiates every concrete entry. `PolytomyRestrictedVerifierGuardSequence.lean`
   calls the eight real routines and preserves the full stack function.
   Rejection skips all later local flag-resetting routines.
   `PolytomyRestrictedVerifierPipeline.lean` bounds this actual
   pre-cleanup execution by one original-input polynomial.
4. **One shared typed object, not unrelated existentials.**
   `PolytomyRestrictedVerifierGuardSemantics.lean` reconstructs one typed
   forest and one certificate. Deterministic codec inversion identifies
   each component's existential trees with these same objects. This is
   equality of exactly decoded data, not biological identifiability.
   Its conjunction is exactly `scanRawTargetValid && scanRawCertificate`,
   with target/certificate cell sets, every clade, all target guards and
   the original root-inclusive score.
5. **All original error cases and clipping.**
   `PolytomyRestrictedVerifierOriginalSemantics.lean` joins successful
   saved words back to their original decoders and proves prefix
   acceptance/rejection equivalence on all words. Wrong row counts,
   malformed framing, count-too-large/invalid dimensions, bad finite
   cells and trailing bytes are not excluded by an input promise.
   `restrictedPipeline_original_bit` ends through the existing
   `boundedPairVerifier_eq`. Thus semantic clipping still uses
   `parsed_valid_target_bounds` and `parsed_verifier_score_bound`.
   The looser operational A<=Q bound is NOT used to justify clipping.
6. **All-path mass, final cleanup and exact machine.**
   `PolytomyFixedCodeSpaceBound.lean` structurally bounds pushes along
   each actual TM2 statement, takes the maximum over finite labels, and
   inducts over actual transitions. TM2 can execute multiple pushes in a
   single statement-step; no one-push-per-transition assumption is made.
   Both public and private intermediate tapes are included. The routine
   return boundary separately guarantees private tapes empty and private
   state reset. `PolytomyRestrictedVerifierCleanHalt.lean` charges all
   public cleanup on every rejected or accepted path, emits one bit and
   resets public control. `PolytomyRestrictedVerifierMachine.lean` packages
   that SAME code and proves the exact `initList`/`haltList` boundaries.

`PolytomyRestrictedAlgorithmsSourceEndpoint.lean` retains the full original
constructor/reduction endpoint alongside this verifier supplier. Its
NP-completeness SOURCE theorem is still conditional on the exact
`EncodedSourceHardness`. The older conditional interface with two supplied
algorithm witnesses remains intact, not rewritten as accepted closure.

## Explicit global resource contract

Let L be the length of the ORIGINAL pair word. The source front bound is
6L^3+50L^2+183L+269. The original two-grammar prefix bound is

    F(L) = 14L^3 + 110L^2 + 447L + 603.

Let P(L) be the explicitly displayed polynomial in
`restrictedPipelinePolynomial`. It includes F(L), every guard's actual
component bound and all eight success-gate costs. Guard operands are
bounded by Q=(L+2)^2 only after actual bounded header preparation.
Position-bounded last-occurrence counting avoids enumerating a
binary-huge alphabet.

Let c be the maximum number of pushes along a branch of any statement in
the fixed prefix code, and d the length of its fixed public cleanup
inventory. The actual Runs induction gives every prefix tape length at
most L+cF(L), including malformed and early-rejected paths. All guards
restore the entire caller stack function, so their final public cleanup
mass is at most d(L+cF(L)). The complete stated polynomial is

    P(L) + d(L+cF(L)) + d + 3.

Here c,d are fixed finite code constants, not free input-size parameters.
The final d+3 accounts for the actual clear-many overhead, one-bit emit
and public-control reset. No hidden compiler pass is presumed free:
Routine already carries the concrete TM2 code, working stacks and labels;
its actual execution relation is used directly to construct FinTM2.

## Evidence and narrow review

The author's source-level mathematical/static inspection checked the
scope, shared-object join, preserved rejection, exact clipping route and
time-to-space argument. This is not a full transitive proof review.

A text-only lexical inspection at 04:14 UTC covered the fifteen new Lean
files: balanced nested comments/strings/brackets, no explicit
`sorry`/`admit`/`axiom` tokens outside comments/strings, and no duplicate
declaration names within this new packet. This is NOT Lean parsing,
typechecking, dependency/axiom audit or execution. Placeholder absence
cannot certify a proof. The final manifest lists source sizes.

The coordinating parent read the complete Machine and CleanHalt files
and reported a narrow endpoint review: identity Bool alphabets, actual
routine code/private tapes, exact initList/haltList, full initial-control
restoration, one original scanPairVerifier bit and an all-input polynomial
including prefix push-cap/public cleanup and the pipeline match the
intended contract. This was expressly NOT full transitive body review,
finite-instance checking, elaboration or Lean acceptance.

The parent's earlier score-note review remains limited to the described
root-inclusive objective/cleanup design, not the 969-line component body.
Neither limited review expands into blanket acceptance of this packet.

## Pinned API and attribution

Own pin remains Lean v4.33.1 / mathlib
0df444a360eaa60ab8c11dca51a86af692955474. The exact TM2 statement, stepAux,
step and configuration definitions were freshly read from
[StackTuringMachine.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Computability/TuringMachine/StackTuringMachine.lean),
blob 916694942a3bfefa0bd9085e2f48735dbe8e0f5b. The exact FinTM2,
initList/haltList and polynomial-witness interfaces were read from
[Computable.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Computability/TuringMachine/Computable.lean),
blob 7779a00f0c3c3909923a5f1bde6b3120b5c2d28a.

Optional source dependency remains Szymon Torunczyk and GPT's Apache-2.0
[compositional-polytime at 7fadbfd](https://github.com/szymtor/compositional-polytime/tree/7fadbfd005b359a66ccc1165b2d1becddb2906b8).
The exact Subroutine/Routine boundary and proof-side Runs were freshly
read, blobs 40755f295636ed00d6cb02e05f2b56d7c4bf3948 and
a4e7feea7faea51531d1da60293c869cab4df75e. Existing pin mismatch and
uninstalled-dependency limitations remain. No concept-side theorem axiom
is intentionally substituted for a proof, but a future transitive audit
must establish actual dependencies rather than trust namespaces.

## Next exact work

Continue correctness/dependency review of this whole packet, preserving
any discovered defect as a correction rather than silently claiming a
verified result. Separately check exact EncodedSourceHardness applicability
and the required source encoding/model translations. The restricted
verifier source does not close that independent obligation, the general
DAG algorithm/formalization, or the original stochastic cellular problem.
