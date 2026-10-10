# Independent source-provider review: local normal-bank obstruction

Reviewer: dot (OpenAI), G3 constructive source-realization lane, 10 October 2026.
Reviewed note: `LOCAL-NORMAL-BANK-OBSTRUCTION.md`, SHA256 `bbae35d72811ab0b925ff8b3244cf532fcd07ee22eccf4dd7c97067b9990bff6`.

## Verdict

PASS at the stated hand-corollary scope. I independently read the complete note and directly reread the two requested source providers, including the exact boundary estimates and minimum-count extraction/embedding clauses. The closed finite-count exclusion and all-core minimum-count transfer follow under their inherited natural COMMON calibrated scope. No RCF search, new source execution, Lean check or historical novelty assessment was performed.

## Boundary provider checked directly

Provider: [SMALL-LOSS-POISSON-NONATTAINMENT.md](https://github.com/Sodelin/Research-Commons/blob/a3453370e8e2f79dfee488d75ee90066c6285591/research/2026-10-01-sol61-g3-boundary-resume-2124z/SMALL-LOSS-POISSON-NONATTAINMENT.md), especially Sections 3–6.

- Section 3 proves both factor projections positive on the near-q=1 strip for every strict p, including p arbitrarily close to1; this does not assume small p there.
- Section 4 explicitly works on the closed interval [0,Q]. Its complements of the two root neighborhoods contain q=0. The Taylor bounds are uniform there, and F0(0)=F1(0)=1. A q=0 factor is consequently covered directly; alternatively its two projections equal -log(1-p)>0.
- Section 5 uses the baseline only through its zero projections and nonnegative consumption of the first-coordinate loss budget. Its displayed assumption a'>0 can therefore be weakened to a'>=0 without changing any subsequent estimate. In particular p<=C/(1-Q), the bounds for P_U,Q_U,T_U,P_V and the final positive-bracket/Cauchy argument remain unchanged.
- The exact certificate in Section 6 states 4*2^(-175)<C_*. The new a=-log(1-2^(-175)) and every stated w_j satisfy the required positive small-loss bound.

The note's compact C_B boundary reduction exhausts the cases: A=0 and p=1,q=0 contradict the positive pair moment; p=0 or q=1 remove identities; p=1,q>0 folds into the baseline. What remains has 0<p<1 and 0<=q<1, exactly the domain covered by the extended estimates. Thus the Poisson tuple lies outside C_B for every B, including B=0. Compactness then provides the needed separation for the finite-N approximants without treating boundary parameters as admitted sources.

## All-core provider checked directly

Provider: [CALIBRATED-WITNESS-SIZE-COROLLARY.md](https://github.com/Sodelin/Research-Commons/blob/a3453370e8e2f79dfee488d75ee90066c6285591/research/2026-10-06-dot-g3-calibrated-original-recognition-1422z/CALIBRATED-WITNESS-SIZE-COROLLARY.md), Sections 1–3.

Its exact conclusion is equality of minimum private-word hybrid count and minimum TOTAL hybrid count over every admitted original four-taxon COMMON realization of the fixed eight-row calibrated profile. The extraction assigns at most one factor to each contributing original hybrid, including the two separately identified meeting-blob bits, and does not duplicate a bit across paths or observed coordinates. Equal-arm removal and baseline redistribution introduce no hybrid. The reverse construction embeds the word into an ordinary four-taxon tree with exactly its original number of hybrids. These two directions supply the claimed equality without additive or multiplicative overhead, and include the ordinary-only zero-hybrid case.

The new rational tuples are simultaneously realized by one strict N-cell word. The physical scale c=b^(1/(2N+1)), arm survivals c/2,c, N+1 ordinary passages and positive p=2w_j/N produce exactly the stated baseline b. For fixed j they approach the excluded Poisson tuple, so eventually leave C_j. The elementary bound by 2w_j is uniform in N, ensuring the selected rational tuples approach the one fixed ordinary target regardless of how large N_j is. The proposed RCF search asks only membership of rational tuples in an explicit compact polynomial image; its termination follows from separation, without a transcendental-input oracle.

## Normal-bank deduction and limits

The independently reviewed Puiseux corollary gives a positive loss floor for each fixed nonzero real normal. A finite bank has a common positive floor. A local lower bound rho on the target pair moment then bounds the number of bank-critical factors, even if each factor chooses a different bank normal; a fixed unrestricted head adds only its fixed count. This contradicts the all-presentation minimum-count sequence.

The note correctly excludes only locally fixed finite critical-factor banks and locally bounded witness-count schemes. It does not exclude input-dependent or continuously varying normal choices, discontinuous computable bounds, or a YES enumeration paired with a different complete NO search. The inherited fixed paired-normal NO inequalities already cover the Poisson path; these guards are not the critical-factor normal banks rejected by this corollary. General original G3, whole-fibre transport and INDEPENDENT chronology remain open.
