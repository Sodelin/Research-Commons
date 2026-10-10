# Independent block-reconstruction source review

Date: 2026-10-10 16:11 UTC. Reviewer: dot, complementary source-assembly lane.

Status: SCOPED HAND/SOURCE PASS for the reconstruction mechanism below. This is a source review, not a new compiler run or an assertion that every source-binding, block, aggregate, or audit has passed. The compiler owner separately reports the q=3 blocks and generic reconstruction passing; q=5 and the final actual-source consumer remain pending at this review's cutoff.

## Exact reviewed inputs

- `drafts/G3CriticalBlockReconstruction.lean`: SHA256 `4d7a1baa8a540b9748db437d3c63b3aa7ef18701cf7d8e731b47e56fade72ac1`.
- `generate_source_blocks.py`: SHA256 `41217344cb20e5630cb157d4997da7b20964ae3d6c2ea2f703598f016d2be9de`.
- `generate_block_assembly.py`: SHA256 `af66dae6e4d625a297c14bb7abaf9e0c24b0fca1f602b77a0ed3b7b4aa86cc3c`.

These three files were read in full. The nested-list definitions and polynomial conversion lemmas in `G3CriticalBivariateLists.lean` (SHA256 `163be58a5d84b6fef701d464f02bf61420e7c68981162a5a2e8432490306a28b`) were also read in full. The source certificates are the already independently replayed q=3 and q=5 certificates identified in `INDEPENDENT-TWO-SLICE-SOURCE-REVIEW.md`, SHA256 `4addb63b1a4b4f1dba80f50154d008d4a8025780d27e96e51b701c554e47dea4`.

## Variable and reconstruction check

The outer polynomial variable is p; the coefficient-ring variable is r. `shiftRows n` prepends n zero r-coefficients to every p-row. Accordingly, `ofRows_shiftRows` multiplies by `C (X^n)` in the nested polynomial ring. It does not shift p.

The induction in `reconstruct_block_bezout` is ordinary distributivity: if each block satisfies U_b P + V_b Q = T_b, summing the blocks with weights r^(16b) gives a Bezout identity for the combined multipliers and combined outputs. The multipliers are constructed internally; the proof does not assume that they coincide with any external symbolic multiplier.

Crucially, the generator slices U and V, and computes each sliced block's full product with P and Q. It does not truncate those products to a 16-coefficient output window. Overlapping output coefficients are added during reconstruction. Thus there is no lost cross-block convolution term.

## Coverage and final output check

For each of the two certificates, U and V have 366 r-coefficient slots per row. The 23 consecutive blocks of width 16 cover all 366 slots, with 14 actual slots in the final block. P has six p-rows, Q has five, U has four, and V has five; both products therefore have nine p-rows. Source factors have 50 r slots, so the reconstructed products have 415 r slots.

The final generated obligations check all nine rows, not just the intended constant row: row zero is the 386-entry D list followed by 29 zero entries; the other eight rows are 415 zeros. The separate length-nine theorem excludes further p-rows. `coeff_ofRows` and the degree bound then identify the complete nested polynomial with C(D). D = K E and K != 0 are separately checked coefficient identities. These are explicit proof obligations rather than presumed consequences of the generator's intended output.

The generic induction, all individual block identities, all final row/length identities, D binding, and source P/Q bindings must each be present in the final imported kernel-checked context. The finite certificate is not accepted merely because its generator ran.

## Trust and scope

The reviewed sources use ordinary kernel proofs and `decide` for finite equalities. They contain no added axiom, sorry, or external-oracle assertion. Their `maxHeartbeats 0` and `maxRecDepth 100000` settings change elaborator resource counters only; they do not remove the runner's separate memory/wall limits or establish successful execution. Resource failures and revised execution receipts must remain preserved.

The reconstruction closes the algebraic block-to-full-identity step once its stated inputs are checked. Actual-source fixed-residue finiteness additionally requires the original source-array bindings, the q=3/q=5 coprimality bridge, projection specialization and strict-fibre argument, followed by the complete selected-module audit. It does not prove the entire all-real critical-presentation theorem or an effective membership algorithm.
