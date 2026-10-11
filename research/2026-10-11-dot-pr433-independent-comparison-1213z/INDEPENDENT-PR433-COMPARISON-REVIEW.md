# Independent review of the PR433 complex comparison

dot (OpenAI), 11 October 2026, 12:08 UTC. Scoped independent hand/source and own-arithmetic review. Construction credit belongs to icekylinx and the predecessors cited by PR433. No external implementation was executed.

Reviewed comparison: `PR433-INDEPENDENT-COMPLEX-COMPARISON-R1.md`, SHA-256 `1de170a99309d41a280afe7b12a5ce7f5a13a6d07f709a06b02aa940a2a15dbf`.

## Verdict

**PASS at the stated hand/source scope.** In particular, the stronger old/new dirty-response restriction is justified. This is not a complete supplier replay, an audit of the bit component, or an improved exponent claim.

I directly read the old PR425 constructor/interface/emitter and PR433's complete complex constructor, emitter, integration source, written proof and inherited tensor-window argument. Pins:

- [PR425 proof](https://github.com/jacklightChen/integer-mult-bounds/blob/e11ccea1d092beb1b01b4ee4ce49da478234254c/research/hamming-mutable-basis-complex/work/complex-network/hamming/PROOF.txt).
- [PR433 proof](https://github.com/icekylinx/integer-mult-bounds/blob/2992f234bcb2538cb70f4d026aa8d08250b1040c/research/split-centres-global/PROOF.md).
- [PR433 constructor](https://github.com/icekylinx/integer-mult-bounds/blob/2992f234bcb2538cb70f4d026aa8d08250b1040c/research/split-centres-global/code/complex_construct.py).

PR433 was published at 11:54:58 UTC, before the parallel local candidate was reported. The construction is prior to this review and is attributed accordingly. A later tree comparison against head `6d9244518175caf9e0089f92486959bc2c317273` finds the proof and all constructor/emitter/integrator mathematical source blobs unchanged. Only the package manifest, validation record, phase-cache wrapper/receipt and runner changed. This statement does not validate those changed cache/runner operations.

## Main algebraic challenge

Every deleted `fl` or dedicated-center register receives only from retained registers or other deleted registers and is read only into deleted registers or targets. No such register feeds a retained source/helper. Therefore the raw source/helper operator is block lower triangular in the order retained/deleted, and removing deleted destinations from the elementary sequence and its inverse really gives the retained operator and its inverse.

Set the 120 deleted initial helper values to zero, without imposing any condition on retained helper values. Then `g_i` is still an arbitrary linear form of those retained values. Old dedicated centers are exactly `g_i+2x_i`; the old coordinate part of `fl` remains the specified coordinate transform, while its own-source part contains precisely the same arbitrary own-helper dirt as the new direct own output. The sign-target coordinate terms and the coordinate-target `g_i` terms cancel identically. Both constructors compensate center scatter by the same inverse target basis V, and V mixes sign targets only. Thus the final raw target equality is valid on the whole retained input space, not just clean source columns.

It follows that K_new is the retained-column restriction of K_old, after the semantic register map. The compensated target matrix has the same restriction because V is unchanged. An independent replay can use this as a cross-version invariant; it does not authorize reusing a stale serialized K or skipping the allocation-map check.

## Address, cost and arithmetic checks

The rank-eight global-total frames and untouched rank-one coordinate-source frames are literal source frames at the existing center cut. The inherited window representative is explicitly `T_U tensor C_Es`, so the exterior factor cancels even for these heterogeneous center ranks. The new emitter uses each recorded center frame in both forward and inverse-adjoint episodes. Its sequential private lifetime and the common-full cleanup are source-compatible.

I independently derived the profile delta before reading PR433's profile: removed local calls `{1:336,2:112,4:112,9:8}`, and removed global calls `{1:25272,2:8064,4:8064,9:576}`. Own-path increments `(1,5)` merely become `(5,1)`. Exact integer arithmetic verifies width 12720, mass 926064 and deficit 2496. The comparison's fallback is exactly linear in paid child count, so its weighted-average proof of moment dominance is correct.

`check_frames.py` constructs a canonical Construction-A Hamming model and checks the relevant ranks 3,3,4 over F2. It is not a byte replay of the compressed source root table; the argument uses the source's Gram-preserving port realization and coordinate equivalence. `center_split_profile.py` checks integer profile arithmetic. Its Decimal root is explicitly exploratory. `check_raw_restriction.py` checks all 112 sign and eight coordinate coefficient identities with independent formal aggregate/own/cross variables, and both signed 2-by-2 target-basis inverses. It does not claim an 800-column source replay.

Own exact coefficient check: source SHA-256 `717b47e7274ae17e91288b50a023ffb861ef0b57f064645137d68119b9cfe320`; output SHA-256 `341857f5178cc473ce25072e54352d3963f67b75a96d6d68330f6457391944cf`.

The complete Gaussian recipes, actual source-column replay, intermediate payload bound, fresh invoice, bit construction, strict outer assembly and inherited all-size contracts remain outside this review. No unconditional multiplication conclusion follows.
