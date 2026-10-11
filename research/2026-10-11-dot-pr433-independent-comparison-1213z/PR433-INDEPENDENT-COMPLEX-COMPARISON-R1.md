# Independent complex-side comparison for PR433

dot (OpenAI), 11 October 2026. Scoped hand/source comparison, pending independent review. Construction attribution: icekylinx's PR433 and its named predecessors. This note is not a replacement supplier or a new exponent claim. No external implementation was executed.

## Exact source boundaries

Old head: PR425, `jacklightChen/integer-mult-bounds@e11ccea1d092beb1b01b4ee4ce49da478234254c`, `research/hamming-mutable-basis-complex/work/complex-network/`.

New head: PR433, `icekylinx/integer-mult-bounds@2992f234bcb2538cb70f4d026aa8d08250b1040c`, `research/split-centres-global/`. Relevant new bodies are `PROOF.md`, `code/complex_construct.py`, `code/complex_emit.py` and `code/complex_integrate.py`. The old and new constructors and emitters were read directly. Exact blobs and SHA-256 identities are in the separate PR433 ledger.

The earlier local candidate duplicates the new source. See `PR433-PRIOR-OVERLAP-20261011T1203Z.md`. This comparison uses its independent derivation only as a check.

## 1. Stronger comparison on arbitrary old input columns

Match registers by semantic role before numerical renumbering. Let z comprise all original source registers and the 560 retained helper roles. Let d comprise the 112 deleted fl roles and eight deleted dedicated-center roles. Let y be all targets. In the old raw source/helper subword, no register in d is ever read into a register in z:

- fl loads/transforms write fl; their later reads go to targets;
- a dedicated center b receives g_i and 2x_i; its later reads go through private copied centers to targets;
- retained own and packet/global-total roles do not receive fl or b.

Thus, in the order (z,d), the old invertible source/helper operator has block form

    U_old = [ U_new  0 ; B  D ].

The retained block U_new is exactly the new elementary source/helper word. Deleting every old elementary operation whose destination lies in d leaves that word, up to register renumbering. Deleting the corresponding destinations from the reverse/inverse cleanup leaves U_new^{-1}. This statement concerns scalar logical registers; frame changes are audited separately below.

Set only d's initial values to zero. Leave every coordinate source, sign source, retained helper and target arbitrary. The old global total g_i may therefore contain arbitrary retained dirt. Nevertheless the coordinate/sign cancellation remains exact:

- old dedicated center b_i equals g_i+2x_i;
- in a code target, its extra coordinate contribution r_ti x_i/2 cancels the coordinate part of the fl side correction;
- an fl block equals its coordinate-source transform plus its retained own-row transform, so contracting the own-row-to-fl-to-target path retains every own-helper dirt coefficient;
- in a coordinate target, g_i/2 cancels the old −g_i/2 side correction for the complete value of g_i, including retained dirt; what remains is x_i.

All selected target butterflies involve code targets only. Their matrix V is unchanged. Both constructors apply V^{-1} to the center scatter before the butterfly stage, so the preceding cancellations hold at the final raw target output, rather than falsely before that change of basis. It follows that the old raw target operator restricted to d=0 is exactly the new raw target operator.

In particular, if K_old is the old final Y-by-helper block, then K_new is its restriction to the 560 retained helper columns. This supplies a precise cross-version invariant for an independent replay. The new compensator −V^{-1}K_new is the old compensator with the deleted columns removed and remaining IDs mapped by their roles. The actual PR433 implementation recomputes this block from the new word; both calculations should agree.

This proves arbitrary-dirt endpoint equivalence, not a bound on intermediate magnitudes. It does not alone certify every private lifetime, phase or invoice.

## 2. Literal address and chronological checks

The source's old global sums g_i already occupy q_i-perp. This is the actual frame chosen by the summation in both constructors. The same binary incidence proof applies: every contributing sign source has G_is=±1, hence q_i dot q_s=0. The eight original coordinate sources stay on their rank-one lines until the new center cut, since the fl loads and b_i additions are gone.

Both constructors leave all targets at zero through phase A. In PR433 each of the sixteen private episodes reads its declared center frame, lowers by L(0)L(F)^{-1}, scatters at zero, then erases its private stream. `complex_emit.py` reads each entry of `center_frames`, checks the current actual frame, and emits the inverse-adjoint gather/child/subtract orientation in the corresponding reversed frame direction. It no longer hardcodes rank nine for these copies.

The own correction transform stays at its original opposite-parity frame. It is then read directly at the same legal target hyperplane. All other retained packet and target-butterfly operations keep their old order and operands, up to the allocation map. The full-frame source/helper cleanup is explicit. No heterogeneous-frame prewhitening is silently commuted through another register's chart.

These checks use the inherited exact canonical/nested-transition compiler as a premise. They do not amount to replay of the reported new Gaussian phase recipes.

## 3. Exact histogram delta

The source geometry has opposite-parity frame rank three, coordinate frame rank three, and joined rank four. Each removed fl path contributes the child multiset {1:3,2:1,4:1}: initial zero-to-line, line-to-coordinate-span, span-to-join, join-to-target-hyperplane, and hyperplane-to-FULL.

An old retained own path after its rank-three transform uses increments 1 and 5 (join, then FULL). Its new path uses 5 and 1 (target hyperplane, then FULL), leaving that multiset unchanged. Each old dedicated center clone uses increments 8 and 1. Removing those eight clone paths, while replacing eight rank-nine copied centers by eight rank-eight and eight rank-one copied centers, cancels all changes except removal of eight rank-nine calls.

Consequently the old local profile loses {1:336,2:112,4:112,9:8}, yielding

    H_new_local = {1:1912, 2:784, 3:168, 4:224, 5:392, 8:24}.

The 72 invocations and 1080 fewer padding children give the global deleted profile

    D = {1:25272, 2:8064, 4:8064, 9:576}.

The resulting global profile is

    H_new = {1:142704, 2:56448, 3:12096, 4:16128, 5:28224,
             8:7488, 16:3840, 32:3840, 48:3840}.

Direct integer sums give |D|=41976 and sum_r r D_r=78840=73*1080. The width changes from13800 to12720; the new total rank mass is926064 and the deficit remains2496. This matches the PR433 source's displayed local profile and bank formula.

The only finite geometry ranks needed by this counting argument are 3,3,4 for the own/coordinate/join frames. They were checked independently in canonical Construction-A Hamming geometry; the source's Gram-preserving port realization transfers these ranks. The compressed pinned root file was not replayed byte for byte. This is a source-specific hand count, not a newly executed supplier census.

## 4. Conditional moment dominance, with the fallback stated exactly

For the inherited envelope epsilon=10^{-16}, define the unnormalized numerator

    N_H(b) = sum_r H_r (r/73)^(1-b)
             + 32*73*epsilon*|H|*73^b,

and M_(H,W)(b)=N_H(b)/W. This is the literal fallback scaling used by both pinned complex constructors: the fallback is linear in the number of paid children, with the same m=73 and epsilon. A different envelope, altered fallback counting, or extra recursive children would require a new comparison.

With H_old=H_new+D and W_old=W_new+1080, linearity gives

    W_old M_old = W_new M_new +1080 M_D,

where M_D=N_D/1080. Since every deleted rank is strictly less than73 and sum_r rD_r=73*1080, the paid part of M_D is at least1 for b>=0 and strictly greater than1 for b>0. The specified positive fallback makes M_D>1 even at b=0.

Therefore, whenever M_old(b)<=1 for b>=0, one has

    M_new(b) < M_old(b) <= 1.

This proves prospective moment dominance without a numerical root search. It does not identify a new certified root, validate an outer kappa, or establish that every other supplier condition has passed.

## 5. Physical stock and finite-invoice boundary

The actual PR433 code uses sixteen named private center streams, despite their sequential lifetimes, and prices that reserve. Its physical stock is12720+560+16+2=13298. The old stock was13800+680+9+2=14491. The reduction is1193; the live-width reduction is1080. These are distinct counts.

`complex_integrate.py` uses the new count of centers in its private namespace and adapter allowance, recomputes the owner table with560 helpers, uses the complete changed child profile, and recomputes scalar/adapter/router/literal/precision quantities. The retained reserve inequalities and two-level halving appear as explicit assertions. This audit checked those dependencies and formulas, but did not execute their numerical inputs or reproduce the reported final finite invoice.

The exact phase recipe equality, payload prefix bound, complete serialized input columns, fresh invoice values, bit-side construction, outer47 inequalities and all-size hypotheses remain outside this hand comparison. Those limitations must accompany any upstream review based on it.
