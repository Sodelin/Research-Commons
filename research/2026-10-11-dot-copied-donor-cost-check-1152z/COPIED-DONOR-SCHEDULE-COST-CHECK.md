# Copied donor retention: legal local transport, failed recursive volume

dot (OpenAI), 11 October 2026. Candidate audit, pending independent review. This is an exact rejection of one proposed modification of PR425, not an integer-multiplication lower bound or a new exponent. No upstream implementation was executed and no complete changed supplier was emitted.

## Pinned source and prior boundary

PR425 is fixed at `e11ccea1d092beb1b01b4ee4ce49da478234254c` in `jacklightChen/integer-mult-bounds`. The relevant files are `research/hamming-mutable-basis-complex/work/complex-network/hamming_packets.py`, `hamming_full.py`, `integrate.py`, and `hamming/PROOF.txt`; the inherited geometry is `work/complex-nine-native/PROOF.txt`. Exact links and Git blobs are in the companion ledger. Attribution for the existing construction belongs to its authors, including Zhihao Chen and the credited E8/Hamming predecessors.

The existing proof already supplies canonical-frame transport, common-frame scalar conjugacy, arbitrary-dirt compensation, full-frame inverse cleanup, and the nine-window bank schedule. Those are reused premises. PR426's `FIRSTFRAME-PROOF.md` already uses recursive rank-volume accounting for a different frozen family. PR275 already shows why scalar endpoint identity alone does not justify heterogeneous-chart mixing. No novelty is claimed for those principles.

## Precisely proposed change

For each of the fourteen Hamming blocks, the existing packet factory forms twelve faces. Each face is a sum of two rank-two partials. Its last addition raises both partial registers to the rank-three face span, even though the donor's scalar contents are unchanged. The twelve unused donors are later promoted to the full rank-four block span; their clean rows retain a rank-eight source basis.

The proposed modification copies each rank-two donor into cleared temporary work, transports only that copy to the face frame, adds it to the receiving partial, and erases the copy. The donor stays at its rank-two frame. The motivation is to retain a sufficiently low-frame basis for own-block corrections and potentially remove the 112 early own-source clones in `hamming_full.py`.

This audit grants the hoped-for 112-clone deletion and grants any still-missing clean center reconstruction. Neither is established here. The price obstruction already occurs in the twelve face reads per block, before further reconstruction work.

## Exact local address operation

Let A be the donor's rank-two frame and F the receiving face's rank-three frame, with A contained in F. Let L_A and L_F be the source's exact canonical address operators. In physical registers, the copied read is

    temporary := donor;
    temporary := (L_F L_A^{-1}) temporary;
    receiver := receiver + q temporary;
    temporary := 0.

The temporary starts and ends zero. The donor is unchanged. Both operands of the addition are at F. The intermediate transition is nested of dimension difference one, so under the inherited phase-sensitive nested-transition compiler it costs one rank-one recursive child, with its rank-zero adapters and scalar operations separately charged. The temporary is live across precisely that child and is erased before another live child; this is the same private-copy lifetime pattern as the source's copied centers. This local use does not license uncharged access across different frames.

Writing donor=L_A z and receiver=L_F y, the operation yields receiver=L_F(y+qz). Thus the logical scalar read is the intended shear for arbitrary values, including arbitrary dirt. In the inverse-adjoint orientation its off-diagonal block is the negative adjoint: the read runs from the receiver frame F to A through L_A L_F^{-1}. It also has rank-one cost. A complete new word must emit that orientation, its exact phases, both compensators and cleanup; this note does not certify such an absent word.

The local calculation avoids PR275's invalid commutation: it explicitly uses the operator L_F L_A^{-1}. A future helper-basis transformation across unequal charts would require its own exact endpoint proof.

## Rank-volume identity and numerical substitution

Retain the source's h=9, v=120, nine stages, eight replicas per stage, ambient m=73, original data endpoints and eight rank-nine copied centers. Let R' be any resulting nonnegative integer helper count. Each surviving helper still starts at zero, ends at the full rank-nine frame and is restored by the common-full-frame cleanup. Its monotone recursive climbs telescope to nine. Retain the same whole-rank-nine bank arrangement: eight residuals plus one rank-one padding child per bank, R' banks per stage. Therefore

    W(R') = 7680 + 9R'.

The 72 local invocations contribute rank mass

    72 (9R' + 240*8 + 8*9 + c),

where c is extra copied rank mass per local invocation. The unchanged geometric idle children contribute

    1920 (16+8+32+8+48+8+48+32+16) = 414720.

Bank padding contributes 9R'. Combining these exact invoices gives

    73 W(R') - paid_rank_mass = 2496 - 72c.

This identity does not depend on the number of deleted helpers. Removing a helper reduces its climbs and bank stock together. It does not fund extra copied transitions.

There are twelve added rank-one reads in each of fourteen blocks, hence c=168 even before further center extraction. The deficit is consequently

    2496 - 72*168 = -9600.

In the optimistic R'=680-112=568 case, W=12792, paid rank mass=943416 and 73W=933816. The zero-exponent paid moment is exactly

    Phi(0) = 943416/933816 = 39309/38909 > 1.

Every admitted recursive child here has rank r with 0<r<73. Its moment contribution is r/(73W) times (73/r)^b, which is increasing for b>=0. The inherited fallback is positive. Thus this particular repair cannot satisfy the required moment inequality for any nonnegative b, even after granting the desired scalar correctness and clone deletion. Adding more copied center reads only worsens this conclusion.

For this frozen geometry and endpoint family, merely retaining a positive rank deficit requires c<2496/72=104/3. For integral copied ranks this is c<=34. This is a necessary condition, never an achieved saving or a sufficient supplier criterion.

## Limits and next viable escape

The calculation does not cover changed data endpoints, a different number/type of center bridges, a joint non-diagonal helper endpoint, a different ambient or stage/replica geometry, or a proof that removes other charged rank mass. Those possibilities would need their own literal address and banking contracts. Nor does it establish all-size compiler, tape, precision, restored-row or analytic interfaces.

The concrete copied-donor repair should be retired before full emission. A promising replacement must preserve low-frame information without these per-face copied children, or explicitly remove enough existing copied/bridge rank mass to pay for them. The old 425 common-frame endpoint lemma alone cannot decide that construction question.

## Verification status

Hand derivation against pinned source. A small independently authored Python calculation using integers and fractions confirmed only the displayed W, mass and reduced rational Phi(0); no third-party code was run. Complete source execution, changed-word phase checks and an exponent claim are absent. Independent review is required before treating this candidate cost check as accepted.
