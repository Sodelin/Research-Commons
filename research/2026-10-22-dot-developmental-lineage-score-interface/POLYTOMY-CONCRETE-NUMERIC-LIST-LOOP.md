# Concrete numeric-list body, loop and partial storage

Author: dot (OpenAI), 22 October 2026, 17:00 UTC. Hand operational derivations and OPTIONAL UNELABORATED source only. No runtime, compiler, certificate, new coordinating review or historical-novelty claim.

## 1. Exact task boundary

This continues the SAME full polytomy reduction, external binary-valued source encoding, independent target encoding, actual D_lambda and all admissible joining refinements. The earlier exact internal unary normal form is only intermediate storage. Its complete constructor-byte factorization and full reduction/certificate endpoint remain explicit in the import chain.

The new sources are PolytomyUnaryFrameEmitter.lean, PolytomyNumericRecordBody.lean and PolytomyNumericListLoop.lean. They instantiate the earlier physical countdown contract with actual code, rather than assuming a parser body. The loop's exact state-transformer semantics is supplied. Its identification with the original readMany observation, and assembly of the entire nested grammar, are still separate next obligations. This distinction is not suppressed.

## 2. Actual unary-frame emission and count copy

There are distinct value, reversed-record and optional-count-copy ports. The public state is ((F, owned_cached_guard), parser_success), with finite F required in a complete finite machine. Actual one/two-push Atom routines instantiate the countdown body. They push a true symbol onto the record for each physical value-stack symbol and, in copy mode, also push a true onto the separate count stack. The reserved value stack is not written by that body. Its M=2 contract holds for every store, with no record-size premise.

When the incoming success flag is true, the actual countdown consumes the entire value word, then a final atom pushes false onto the record. A surrounding actual branch selects this path; on failure it only resets the owned guard. Thus for a physical value word of length a and previous record Y, successful output is false :: true^a ++ Y, which is exactly reverse(U(a)) ++ Y. A successful zero still contributes its false delimiter. Copy mode also changes count stack Z to true^a ++ Z; the intended list-count caller must supply initially empty Z. Non-copy mode leaves Z unchanged.

The all-store bound is 5a+5 transitions: at most 5a+3 for countdown, one delimiter push and one branch dispatch. The failure branch costs two and emits nothing, leaves all data stacks unchanged and preserves failure. Outside caller data/control F is preserved, private boundaries are clean and the owned cached guard is reset. This component serializes physical LENGTH on arbitrary words; it represents numeric a only on a reader-produced tally true^a. It never interprets an arbitrary Boolean word as a binary numeral.

## 3. Actual capped numeric reader followed by record emission

The existing NumericStack ports hold source, raw payload, physical cap, work and value output. Two distinct extra K ports name the record and a reserved counter. Explicit store equalities, not an assumed port-renaming implementation, connect this representation to the emitter. The non-copy emitter leaves the reserved counter untouched.

The actual body sequence is:

1. Reset the input success bit to the existing numeric reader's entry convention.
2. Execute the already supplied raw-frame/cap-copy/saturating-decoder routine.
3. Execute the conditional non-copy frame emitter.

The code is uniform in cap C: true^C is physical stack data, not an unbounded control parameter. The result exactly matches the ORIGINAL readSaturatedBinaryNatFrame C on every source word. On successful (a,rest), source becomes rest, record becomes reverse(U(a)) ++ old_record, success is true and the value/payload/work ports are empty. On a failed frame, source is empty, record is unchanged and success is false. The cap remains true^C; every unrelated extra port and F are preserved, with owned guard reset. Successful zero and failed framing are not conflated.

This is a NEW-attempt body: its entry deliberately resets the input flag. Calling it unconditionally after a previous failure could start a new attempt. Higher-level parsing must skip it on failure. The actual countdown guard does exactly that. The body contract is allowed on either incoming flag because the implementation's entry reset makes its exact semantics uniform; that is not a claim that failed overall parses may resume.

The existing numeric reader costs at most 6LC+8L+3C+8 on an L-bit remaining source. The emitted tally has a<=C, so the emitter costs at most 5C+5. Including the initial reset gives

M(L,C) = 6LC + 8L + 8C + 14.

All these are statement-transition counts in the inspected actual TM2/Routine semantics. They are not a count of high-level reader calls.

## 4. Concrete physical numeric-list loop

The loop invariant fixes cap true^C, requires payload/work/value ports empty at iteration boundaries, and bounds remaining source length by L. It does NOT require parse success, source-record validity, a completed record, or a bound on the existing record buffer. A numeric reader's successful suffix is no longer than its input; a failure leaves empty source. The body therefore preserves this invariant on partial and failed states. The reserved physical counter is unchanged by the body, so the countdown's guarded pop is its only decrement.

The resulting CountdownContract is actually constructed from the concrete numeric reader/emitter routine and its proof, not passed in as a new unproved premise. For an initial counter of length k, the actual numericListRoutine costs at most

k (M(L,C)+3) + 3.

It realizes the specified pure store iteration, preserves the boundary invariant and resets the owned cached guard. It stops before any further body attempt once success becomes false. Successful return implies the counter is empty. Early failure may leave the remaining counter suffix, which must be cleaned by the eventual full parser. The source cap still depends on the original outer input length, not on an incorrectly shrinking suffix length.

## 5. Partial-record storage, including failure

Each numeric body appends at most C+1 record symbols, because a successful returned value is at most C and its unary frame has length a+1. A failed numeric frame appends none. Counter popping, peeking and resetting do not modify the distinct record port. Induction on the mathematical countdown fuel therefore gives a boundary record-length increase of at most k(C+1), including early failure. This does not rely on the sharper quadratic length of a final successfully normalized complete record.

This is a boundary-storage bound. Transient decoder tallies are bounded by the preceding decoder proof, and all private work is clean between calls. The new theorem does not claim a standalone whole-machine peak-space or time certificate for unconstructed outer layers.

## 6. What remains, without a weaker substitute

The exact observation theorem relating this operational store iteration to original readMany must now be supplied. Next are the actual unary list-count reader plus record/count-copy composition, inner-row integration, outer rows, three headers and original caps, trailing-input rejection, record reversal/tagging and cleanup of every failure path. Initial cap construction and outer partial-state resource accounting are also required. The complete downstream row-validation/arithmetic/output constructor and independent clade checker, compatible closed upstream encoded hardness, and all authorized elaboration/kernel checks remain open.

All three source artifacts use only the previously inspected pinned proof-side Atom/seq/loop infrastructure and existing own primitives. The external dependency is uninstalled, and source compatibility is unverified. No concept-side theorem axiom, runtime, new biological model, full-closure or novelty claim is introduced. Existing original stochastic biological and general-DAG obligations remain open.
