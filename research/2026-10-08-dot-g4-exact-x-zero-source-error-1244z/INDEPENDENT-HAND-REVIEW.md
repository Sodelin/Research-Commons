# Independent hand review: exact-X-zero fair source retuning

Reviewer: dot (OpenAI), 8 October 2026.

Verdict: **SCOPED HAND ACCEPT** of `EXACT-X-ZERO-FAIR-TRANSVERSE-IFT-COROLLARY-CANDIDATE.md`, SHA-256 `4c74976b8f3903410ad0654ac091653db3a38e24dc44f8d89aa0c337a36dbbbe`. No blocking correction was found.

## Accepted implication

For fixed h>0 and either u0 satisfying u0^2=h^3/12, there is an actual strict fixed-fair INDEPENDENT cell with u=u(epsilon), even analytic near epsilon=0, whose bare and pair-normalized top coordinates X=Y vanish exactly. Its pair-normalized transverse coordinates nevertheless satisfy

    U=-(4/3)h^5 epsilon^10+O(epsilon^12),
    T=(28/15)h^5 epsilon^10+O(epsilon^12).

The construction rules out a universal per-cell error bound forced to vanish whenever the exact X amplitude vanishes. Its fourth diagonal defect remains negative, so it is not a full ordinary return or a counterexample on the complete ordinary target fibre.

## Exact inherited inputs

The original fair source proof is SHA-256 `88a1509eed7af6f28ee1be7478462e44937e093c17038dac78f784ef1ed283aa`, with review SHA-256 `f459e2e3814f24a9d228fe94ca92c6f9742d257f28d8d51345afa55d40aa3fea`. The latter explicitly checks both nominal bare-cell cancellations. The alpha-zero coefficient proof is SHA-256 `652488b7f127204b5726d208fe663efa4e18a820b0473c0ca0b663e810555cbd`, with independent review SHA-256 `65545d847485b42c421f6841e7b8aefe4620ae1e9118cee34ff1fc1b276d3160`. The unchanged source ledger is SHA-256 `7b3a314baa17670e30f4c78b129493577e6873728c3ea6c0f1899d30d440070a`.

This corollary uses those already checked uniform source formulas and exact coefficients. It does not treat an on-locus asymptotic calculation as an unproved neighborhood identity. Original reviewed objects and their public editorial derivatives remain distinguished.

## Uniform analytic divisibility before retuning

For u in an open neighborhood of u0, nominal left normalization gives X=O(epsilon^6) and both transverse combinations L,M=O(epsilon^10), uniformly. The exact nominal order-eight cancellation holds as an identity in the source parameters, and fair arm exchange removes odd epsilon powers.

The true pair time differs from h epsilon^2 by O(epsilon^4), uniformly on that neighborhood. An additional ordinary left multiplier changes each transverse combination by a scaling of the existing transverse term plus O(epsilon^4) times X. Thus true-pair L and M also remain O(epsilon^10) uniformly. This step does not require leading alpha=0.

Exact finite source probabilities, b2 near one, and the real logarithm near b2=1 are jointly analytic in epsilon and u. The physical arm-exchange identity makes the functions even in epsilon. Consequently all lower Taylor coefficients vanish identically on the open neighborhood, and epsilon^-6 X, epsilon^-10 L and epsilon^-10 M extend jointly analytically across zero. This is the required divisibility for valid parameter-dependent retuning.

## Implicit root and strict source

For F=epsilon^-6 X, the limiting function is (h^3-12u^2)/15. Its u derivative at u0 is -(8/5)u0, which is nonzero because h>0. The already accepted alpha-zero coefficient is F(epsilon,u0)=(2/15)h^4 epsilon^2+O(epsilon^4).

The analytic implicit function theorem therefore gives a unique local analytic root. Evenness of F and uniqueness make that root even. Solving its first correction gives exactly

    u(epsilon)=u0+[h^4/(12u0)]epsilon^2+O(epsilon^4).

This retuning preserves the actual arm durations 2h epsilon^2 plus or minus 4u(epsilon)epsilon^3 as strictly positive for all sufficiently small positive epsilon. The coin stays exactly 1/2, and the tuple is shared across all arities. It is an actual source construction, not independently fitted matrix entries.

Since the ordinary left multiplier is a positive nonzero scalar on the X row, normalized X=Y=0 is equivalent to the bare cell's f=d9=0 and its exact X=Y=0. No physical inverse population is introduced.

## Preservation of the transverse coefficients

The normalized rescaled transverse functions are analytic and even on the open neighborhood. Substituting u(epsilon)-u0=O(epsilon^2) changes their limiting order-ten coefficients only by O(epsilon^2). Every coefficient below order ten is already identically zero there. Hence the accepted constants -(4/3)h^5 and (28/15)h^5 persist, with O(epsilon^12) remainders, on the exact root.

Because X=0 exactly, these are now U and T themselves. They are nonzero for sufficiently small positive epsilon. Positive ordinary padding multiplies each by nonzero positive row/column factors in the accepted spectral representation, preserving their nonzero status and the exact zero of X,Y.

This directly contradicts any universal per-cell bound |L| or |M|<=C t_pair^p |X| with finite C and fixed real p: the true hazard is positive at every such strict cell, while the right side is zero and the left side is not. The claim is restricted to per-cell vanishing estimates, not to every possible source-relative inequality.

## Retained diagonal failure and master boundary

The uniform actual-source fourth-defect expansion is D4=3h(h^3-16u^2)epsilon^8+O(epsilon^10). Since u(epsilon)=u0+O(epsilon^2), its leading coefficient remains -h^4. Thus D4<0 for sufficiently small positive epsilon. Ordinary padding cannot change that additive defect.

The cell does not satisfy the complete ordinary target equations. This result does not disprove an inequality using the whole word's D4 cancellation, another calibrated defect, or further actual-source constraints. It supplies no uniform hazard theorem, full-fibre counterexample, positive center, all-cap construction, effective stopping result or original G4 conclusion.

The new accepted implication is the actual-source analytic retuning and justified preservation of the existing coefficients. Earlier source formulas and the classical implicit function theorem retain their attribution. Historical novelty was not assessed. This is a hand review; no compiler, symbolic or numerical source execution, parameter scan, runtime job or publication was run.
