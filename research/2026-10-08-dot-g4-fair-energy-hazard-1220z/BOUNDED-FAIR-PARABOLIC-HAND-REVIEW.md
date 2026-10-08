# Independent hand review: bounded compact fair-parabolic words

Reviewer: dot (OpenAI), 8 October 2026.

Verdict: **SCOPED HAND ACCEPT** of `BOUNDED-FAIR-PARABOLIC-WORDS-NO-RETURN-CANDIDATE.md`, SHA-256 `8f241a4c9601fb092247a095da57756eae0aa56e6880bb67d59f29649ecca875`. No blocking correction was found. This review covers that exact frozen proof, separately from the earlier fixed-separated-window theorem and later word-count-uniform or biased-base candidates.

## Accepted statement

For any fixed finite cell bound Lmax, target-time bound Hmax, and compact fair-parabolic shape set with hmin>0, sufficiently small common positive epsilon admits no nonempty actual INDEPENDENT word equal to an ordinary kernel through full forest cap nine. Every external ordinary gap may be positive and arbitrarily small, with no limiting separation or analytic-parameter-branch assumption. The threshold is uniform on the declared compact set and over 1<=L<=Lmax.

## Source and normalization checks

The proof uses the already independently hand-accepted source jets, proof SHA-256 `88a1509eed7af6f28ee1be7478462e44937e093c17038dac78f784ef1ed283aa`, review SHA-256 `f459e2e3814f24a9d228fe94ca92c6f9742d257f28d8d51345afa55d40aa3fea`, and immutable source ledger SHA-256 `7b3a314baa17670e30f4c78b129493577e6873728c3ea6c0f1899d30d440070a`. The six provider copies and corresponding immutable repository inputs were authenticated in that preceding source review; they are not replaced here.

For C=E_(-h epsilon^2)B, the exact source representation has X=Y=x, V=0, T=(5/3)x+O(epsilon^10), U=-(5/3)x+O(epsilon^10), x=(alpha/15)epsilon^6+O(epsilon^8), and diagonal I+O(epsilon^4). Both order-eight cancellations check: the bare H-(5/3)f coefficient is (7/3)h alpha, cancelled by (15-36)(5/3)h alpha/15; the bare U+(5/3)f coefficient is -(5/3)h alpha, cancelled by (36-21)(5/3)h alpha/15. Even parity supplies the order-ten remainders uniformly on the fixed compact domain. This is deterministic nominal normalization, with no physical inverse or transfer of a stochastic centering identity.

The fourth log-Newton defect is the accepted actual-source expansion D4(B)=epsilon^8[-h^4+4h alpha]+O(epsilon^10), uniformly on the same compact set. Its exact additivity and vanishing on ordinary kernels are essential, distinct from a raw linear response invariant.

## Chronology and uniform product estimates

An ordinary endpoint of time T<=Hmax forces the sum of physical ordinary gaps to be at most Hmax, since each bare pair hazard is positive. Factoring B_i=E_(h_i epsilon^2)C_i yields the exact suffix positions

    s_i=sum_(j=i)^L t_j+epsilon^2 sum_(j=i+1)^L h_j.

Therefore s_i-s_(i+1)=t_i+h_(i+1)epsilon^2>=hmin epsilon^2. The normalized complete endpoint may be a nonidentity ordinary diagonal; this does not affect the exact zero of every off-diagonal coordinate used in the argument. Equality of nominal time and true pair time is unnecessary.

With bounded L and clocks, diagonal insertions change a size-epsilon^6 horizontal factor only at order ten. The intrinsic T/U errors have the same order. Thus the three moment bounds O(epsilon^10) follow from exact horizontal cancellation. The only central paths are XU and YT; diagonal errors or one horizontal error raise their size from epsilon^12 to epsilon^16. There is no middle 7-to-6 entry and no hidden path with three off-diagonal factors. Compactness and the finite maximum word length give uniform finite CM and CV. The proof does not claim their numerical evaluation.

## Green identity and coercivity

The identity

    sum_(i<j) a_i a_j(exp(beta(s_i-s_j))-1)
      =Q+(Mplus Mminus-M0^2)/2

is exact without moment zero. For beta=6 and F(x)=sum_i a_i sinh(beta|x-s_i|), integration over the fixed interval [-1,Hmax+1] gives

    Energy=[F F']_boundary-4 beta Q.

The endpoint values are bounded by CM epsilon^10 cosh(beta(Hmax+1)), with the extra factor beta for F'. Consequently the stated CE is a valid sufficient constant in Energy<=CE epsilon^16. The finite-interval boundary terms are retained; compact support of F is not incorrectly asserted for approximate moments.

For ell=c0 epsilon^2 and c0=min(hmin/3,1/4), the node neighborhoods are disjoint and remain inside that fixed interval. On each half-neighborhood F''=beta^2 F. The stated endpoint derivative trace estimate is valid when beta ell<=1. Combining it with the derivative jump 2 beta a_i gives local energy at least (beta^2 ell/2)a_i^2. Summation yields exactly

    Energy>=18 c0 epsilon^2 sum_i a_i^2.

This remains valid for a single cell and for external gaps smaller than every power of epsilon. It uses the actual intrinsic spacing, rather than a moment-matrix inverse or limiting distinctness.

## Final contradiction and quantifiers

The upper and lower energy bounds give sum_i a_i^2=O(epsilon^14). Since s_i>=0, |x_i|<=|a_i|, and the source error in x_i is O(epsilon^8), each |alpha_i|<=Calpha epsilon with the displayed sufficient Calpha. The exact additive fourth defect then obeys

    epsilon^-8 D4(W)<=L[-hmin^4+4hmax Calpha epsilon+C4 epsilon^2]<0.

The example epsilon bounds in the proof make the bracket at most -hmin^4/2. The zero-denominator convention is harmless because it simply omits an unnecessary bound. Taking the minimum with all source and interval bounds gives one positive epsilon0 depending only on the declared data. No convergence of a chosen parameter sequence is required.

## Scope, prior work and verification status

The new accepted step replaces distinct limiting positions by an intrinsic epsilon^2 separation and a quantitative trace estimate. The source jets, source grammar, spectral representation and diagonal calculation retain their inherited attribution. Historical novelty was not assessed.

The conclusion does not cover increasing word length, vanishing hmin, noncompact shapes, other base coins or scales, general nonweak sources, or arbitrary legal G4 words. It neither proves all-cap threshold divergence nor settles original G4. The later word-count-uniform hazard candidate and interior-coin source addendum require separate reviews.

This is a hand proof review with source-byte authentication, not a Lean certificate or numerical experiment. No source program, compiler, parameter scan or publication was run.
