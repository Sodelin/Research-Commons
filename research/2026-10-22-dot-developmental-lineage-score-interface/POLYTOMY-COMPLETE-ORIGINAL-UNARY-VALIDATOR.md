# Complete original internal unary validator: actual routine proposal

Author: dot (OpenAI), 22 October 2026, 19:47 UTC.

Status: complete HAND DERIVATION of this validator component and OPTIONAL UNELABORATED Lean source proposals. No compiler, runtime, installation, test, CI, certificate, new independent coordinating review or historical novelty claim. This does NOT complete the canonical constructor, independent verifier or full formal NP-completeness endpoint.

## 1. Exact original function and entry/exit

Input is an arbitrary Boolean word on the preserved original-record port of the fixed finite UnaryScanPort layout. All numeric and scan/query work ports start empty. Initial finite control may be arbitrary because the first actual atom initializes the range flag and scan control. Let L bound original input length.

The returned verdict is exactly:

- false if the ORIGINAL readNormalizedSource rejects the input;
- original scanSourceValid R if it parses R.

The exact already-proved unaryRangeValid rewrite is used, not a different source validity domain. It checks actual row count equals declared m, every identifier is below N, and every i in 0..N-1 occurs. Duplicate identifiers are allowed. There is no optimizer or source witness supplied to this validator.

The complete actual routine preserves the original word byte for byte and empties every scan/query/numeric work tape on every return path. The verdict remains in fixed finite control for the later canonical constructor. Each Routine component returns its private work/control clean under the previously inspected actual compositional API. A separate standalone output-bit/reset wrapper is not supplied or needed for this caller-level component claim.

## 2. Physical N preparation

PolytomyPhysicalValidationPreparation.lean first performs a real finite-control atom seeding range=true, then actual record replay/header parsing. It copies the physical true-only N header twice through an empty temporary: once to the range-query cap and once to the reserved outer coverage counter. Each real forward copy costs 3N+3 and preserves the header. The total preparation bound is 15L+23.

There is no provided-N premise or Nat-valued control register. Even if a later header is malformed, the stored N header is true-only and of length at most L; both copies preserve the false syntactic-success bit. Partial or malformed headers therefore cannot force exponentially large work or silently restart parsing. Initial cap/query counter emptiness is explicit.

On a complete parse of R, these words are exactly true^R.N. On arbitrary inputs their physical length is bounded before any semantic source validity assumption.

## 3. Actual original syntax and strict-range pass

PolytomyOriginalRangePass.lean joins that real preparation with the actual nested unary rows visitor in strict-less/AND mode, using the physically created N cap, and an actual empty-suffix check. This is the complete ORIGINAL tagged internal grammar, not a successful-prefix surrogate.

The exact finite observation is None on original syntax failure, or Some(all identifiers below R.N) on parsing R. A false range test is deliberately separate from syntax failure while the parser visits all entries. Exact header values prove the cap in a successful record is R.N rather than an unrelated supplied query. This pass costs at most:

17L^3+27L^2+31L+34.

The original rows visitor physically copied the actual row count before consuming its outer counter. The declared m header is a separate physical word and has survived the rows scan. No consumed count is assumed to remain available.

## 4. Actual guarded declared-count equality

PolytomyGuardedDeclaredCountCheck.lean supplies a real failure-absorbing branch. Earlier syntax failure takes a no-op, not a new comparison attempt. On successful syntax, run the actual unary subtraction with declared m on the left and saved actual row count on the right. The comparison consumes these operands as needed because they no longer need to survive the first pass. No restoring copy is omitted under a false operand-preservation claim.

Subtraction of D from M leaves true^(M-D), empties the right operand, and returns D<=M. An actual peek of the left residual tests emptiness. Thus (D<=M AND residual-empty) is exactly D=M. The final bit additionally ANDs the existing range accumulator. Underflow, equality, excess declared m and zero counts are all handled. The whole guarded comparison costs at most D+3, hence at most L+3.

PolytomyOriginalCountRangeCheck.lean proves successful original parsing supplies precisely true^R.declaredM and true^R.rows.length to this actual branch. The returned verdict is exactly original syntax AND declared-count consistency AND strict range. If syntax fails, the true-only operand premises are not demanded for an unexecuted branch.

## 5. First-pass cleanup and failure-safe bound

PolytomyFirstValidationCleanup.lean proves total owned scan mass is at most 8L before the comparison: source at most L; three headers at most 3L; three row/saved counters at most 3L; physical cap N at most L; all other visitor/copy work empty. The destructive comparison does not increase any stack length. This is established on all paths, including partial failed rows, not inferred from successful exhaustion.

An unconditional actual clear of the 13 owned scan ports costs at most 8L+14. It preserves the original record, physical coverage count and first-pass verdict. Every scan tape is now fresh for later replay, and the reserved coverage counter is true^N with N<=L. First-pass total:

F(L) = 17L^3+27L^2+40L+51.

This first pass also fixes the N=0 issue: zero coverage is vacuous, but malformed syntax, count mismatch or a nonempty out-of-range row was already rejected. Empty N is not used as a reason to skip original source validity.

## 6. Actual coverage join and complete verdict

PolytomyOriginalUnaryValidation.lean composes the first pass with the previously supplied actual coverage loop and unconditional final query-counter cleanup. The coverage loop performs real preserved-record replays for N-1,...,0 by copying the remaining physical counter after each actual pop. No query, fresh copy, count or increment is free. It starts only if the first-pass verdict is true; otherwise the physical loop skips its bodies and still clears the bounded counter suffix.

The first pass proves that, on parsing R, the initial count is exactly R.N and original bytes are unchanged. Therefore the existing exact coverage theorem gives the missing original range-coverage conjunction. If original parsing fails, incoming failure forces the final verdict false regardless of the bounded partial N header. This proves equality to the original guard on EVERY input word, not just valid encoded records.

Coverage body B(L)=17L^3+27L^2+36L+46 and final counter cleanup give N(B(L)+3)+L+4. Since the actual prepared N<=L, the complete validator bound is:

V(L) = 17L^4+44L^3+63L^2+90L+55.

The corresponding proposed source endpoint originalUnaryValidation_executes contains the real Routine execution, this bound, fresh scan work, empty query counter, unchanged original record and exact original verdict together. Code has fixed finite ports/Boolean alphabets/finite Boolean control; only proof-side specifications and induction use naturals. The source has not been elaborated.

## 7. Whole-reduction boundary retained

This is the complete original INTERNAL VALIDATOR component, advancing beyond the previously supplied-count coverage theorem. The complete original normalizer source proposal remains separate and unchanged. The actual external source/target encodings and full actual-D_lambda/all-refinement/output-size/independent-certificate endpoint are retained.

The following full-claim obligations remain OPEN:

1. Consume this verdict in the original downstream constructor branches, including all boundary cases.
2. Actual canonical fixed-block enumeration, original C0 accumulation/arithmetic and target binary serialization, with all-input cleanup and standalone total downstream-machine packaging.
3. Independent target/certificate verifier machine and its actual polynomial bound.
4. Compatible closed encoded source hardness, dependency/toolchain compatibility, transitive axiom audits and authorized full elaboration of the entire chain.

No validator source term alone discharges NormalRecordMachineWitness. No verified build certificate, full formal NP-completeness theorem, historical novelty, stochastic biological identification or arbitrary-DAG closure is claimed. Only previously inspected actual proof-side APIs and own source proposals are used; no dependency is installed and no concept theorem axiom is intentionally invoked.
