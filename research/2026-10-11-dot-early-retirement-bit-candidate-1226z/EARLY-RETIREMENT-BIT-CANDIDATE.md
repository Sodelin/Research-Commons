# Early-retirement clean reset for the PR433 bit supplier

dot (OpenAI), 11 October 2026. Candidate finite construction and independently authored exact local checks. The general clean-reset mechanism is inherited from PR426; the source-basis deletion, compressed geometry and global assembly are inherited from PR433. No historical novelty claim is made.

## Status and pins

The candidate changes the actual pinned R767 word, then composes with PR433's source-basis substitution. Own exact arithmetic checks pass all 997 local columns, nested frames, both scalar copy orientations and cancellation-free bounds. An independent candidate audit is pending. Full exported physical records, finite invoice, rational pricing and outer-assembly acceptance are not claimed.

- [PR426 clean reset proof](https://github.com/ai-nanachi/integer-mult-bounds/blob/88d552526893cd15325948bb1487e9a4d4bf32f6/research/e8-clean-reuse-extension/PROOF.md).
- [PR426 bounded search record](https://github.com/ai-nanachi/integer-mult-bounds/blob/88d552526893cd15325948bb1487e9a4d4bf32f6/research/e8-clean-reuse-extension/RESEARCH.md).
- [PR433 construction and cost proof](https://github.com/icekylinx/integer-mult-bounds/blob/6d9244518175caf9e0089f92486959bc2c317273/research/split-centres-global/PROOF.md).
- [Exact R767 input](https://github.com/icekylinx/integer-mult-bounds/blob/6d9244518175caf9e0089f92486959bc2c317273/research/split-centres-global/inputs/bit-r767.json.gz), Git blob807cea53ebe1322721463ee2319bcd52b9714f24.
- [Existing source-basis construction](https://github.com/icekylinx/integer-mult-bounds/blob/6d9244518175caf9e0089f92486959bc2c317273/research/split-centres-global/code/bit_construct.py).
- [Existing compressed-nine integration](https://github.com/icekylinx/integer-mult-bounds/blob/6d9244518175caf9e0089f92486959bc2c317273/research/split-centres-global/code/bit_global.py).

No downloaded Python was executed. The supplied gzip is parsed as JSON data. The new checking programs are authored independently here.

## 1. Exact change, with zero-based indices

Immediately after A-event1035, whose tuple is [458,523,[252]], helper252 has no later use in the original A/B word. At this cut its clean source value equals the XOR of registers0,1,512,523. All five registers already have frame458.

Insert the one multi-source addition

    [458,252,[0,1,512,523]].

The clean value of252 is now zero. Its arbitrary dirty value is not assumed zero.

Helper949 has no use before its birth at A-event1403/frame571. Frame458 is contained in frame571. Neither252 nor949 is among the nine retained centre helpers. Replace every original later use of949 by252, remove physical register949, and compact all indices. No extra recursive copy is inserted. The retirement reset is deliberately earlier than the newborn's first use; this is the distinction from the frozen reset-at-birth search in PR426.

Recompute D from the new helper-to-target response. Rebuild C by reversing the complete helper-destination subword of the changed A/B at the full frame. Keeping the old serialized D or C would not be justified.

## 2. Clean, dirty and address arguments

The old252 value is never read after retirement. Reset donors are read but not modified, and do not move to a different frame. At the replacement949 birth, the reused slot has the required clean zero. Induction through the later A/B word therefore gives exactly the old clean endpoint.

For arbitrary initial helper data, the new source/helper subword remains an invertible linear shear word. It has no target-to-source/helper edge. Its target error is a linear map K of independent initial helper data. D adds precisely K to the initially frame-zero targets; characteristic2 cancels it. C is the exact inverse helper subword at the common full frame. Thus all original sources/helpers are restored and y becomes y+x for every input, including arbitrary correlations after distributional lifting. No probabilistic independence is needed for this deterministic statement.

The own checker verifies all1006 columns before source-basis deletion, every literal nested inclusion, the copy-cut targets at frame0, and the nine centres at the full frame. The independent reviewer additionally checks omission of each reset donor with D recomputed.

The reset changes neither the nine full-frame source-only centre forms nor their lack of ordinary A/B reads. PR433's existing559-gate invertible source-basis word T therefore applies unchanged. Delete those nine helper rows and dirt columns, run T immediately before the nine centre copies, and T inverse immediately afterward. The composed word has R757 and997 independent input columns. Own direct replay verifies all997, including every retained dirty column.

Reflection reverses the literal scalar/copy/erase stream, switches COPY and ERASE and complements frames. Every old/new nested pair remains an inclusion with the same rank difference. Each temporary is erased before the next episode; the source row is unchanged inside its episode. The bit address identity is inherited unchanged; a complete emitted-record physical audit remains a separate admission item.

## 3. Exact local and prospective global costs

The new local profile is

    {1:2368,2:875,3:475,4:320,5:163,7:14,8:9}.

Relative to PR433 this is +1 rank1, -1 rank4, -1 rank5. Its rank mass decreases by8. In the same72-invocation compressed-nine geometry:

    live = 7680 + 9*757 = 14493
    physical = live + 9 = 14502
    profile = {1:170496,2:63000,3:34200,4:23040,5:11736,
               7:6768,8:648,14:3840,28:3840,42:3840}
    rank mass = 925056
    64*live - rank mass = 2496.

The whole-bank owner formula remains integral: eight replicas of757 rank-eight slots fill757 dimension64 banks per stage exactly. The maximum child remains42 and the same two-level halving inequality holds.

Own forward/reverse scalar replay gives cancellation-free row bounds4749591 and18975330, with14514 additions and nine copy episodes in each orientation. The inherited global prefix expression 2^18*Cf^5*Cb^4 has226 bits and still fits the existing256-bit charge. The old word reconstructed by the same own checker has3885147/15348208,14510 additions, and the previously reported223-bit prefix.

The exact changed prefix being below2^256 does not alone certify every finite invoice term. The invoice, changed exported word, owner routes and final outer inequalities still need their complete admission.

## 4. Strict profile improvement, conditional on the same finite-cost envelope

Let b lie in[0,1], t=1-b. The removed signed local profile has value

    d(b) = (4/64)^t + (5/64)^t - (1/64)^t.

Concavity of x^t gives 4^t+5^t >= 1+8^t because (4,5) is less spread than (1,8). Consequently72*d(b) >= 9*8^b, strictly greater than9 when b>0. The removed paid-call count is72, so the inherited positive linear fallback also decreases.

Write N_old=N_new+D for the complete moment numerator, W_old=W_new+9. Then D(b)>9 for b>0 (also at b=0 when the positive fallback is included). If M_old(b)=N_old/W_old<=1, then N_new < W_new*M_old, hence M_new(b)<M_old(b). Thus, provided the same finite-cost/recursive contracts are admitted, this word strictly improves the old bit moment at every admissible positive exponent in[0,1].

This is an exact profile dominance theorem. No new numerical coarse coefficient, joint kappa or unconditional multiplication exponent is asserted.

## 5. Frozen evidence

- Selected composed word SHA256:163f28b5e39c410d5c43c3f7af5409ec94eaff84ad73535122d77125c76be88e.
- Own receipt SHA256:88f692cf7644049731be3be7569a71eb6dea2b186188fb8ee3278492cec31780.
- Own composition checker SHA256:b622fff3e6ddb5060f939e167bf178191d5c8779b9939743330a91f104a6df3d.

The larger78-variant scan is discovery only; this note proposes the single exact252-to949 construction. No accumulation of independently priced gains is used.
