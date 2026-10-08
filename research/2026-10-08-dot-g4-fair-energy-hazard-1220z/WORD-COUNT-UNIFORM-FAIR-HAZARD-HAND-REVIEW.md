# Independent hand review: a count-uniform fair-parabolic hazard floor

Reviewer: dot (OpenAI), 8 October 2026.

Verdict: **SCOPED HAND ACCEPT** of `WORD-COUNT-UNIFORM-FAIR-BIGON-HAZARD-BOUND-CANDIDATE.md`, SHA-256 `2a7120eba6253b628fc9341d89dc89ef57f076fda0bfa73718432313084d0bd1`. No blocking correction was found. This acceptance is separate from the bounded-length and separated-window results.

## Accepted result

Fix a compact fair-parabolic shape set K with hmin>0, a common small positive epsilon for every cell, and an upper bound Hmax for the ordinary target time. There are positive constants epsilon0 and B0 depending only on those fixed data and the fixed source representation such that any nonempty actual finite word equal to an ordinary kernel through complete forest cap nine must spend more than B0 total bare-cell pair hazard when epsilon<epsilon0. The number of cells has no assumed upper bound. All positive external ordinary gaps may collapse arbitrarily.

The conclusion is a necessary positive hazard floor within this source class. It does not exclude returns with larger positive bigon hazard, show divergence with the forest cap, or establish a universal all-source no-return theorem.

## Authenticated source premises

The source jets are the previously hand-accepted proof SHA-256 `88a1509eed7af6f28ee1be7478462e44937e093c17038dac78f784ef1ed283aa`, independent review SHA-256 `f459e2e3814f24a9d228fe94ca92c6f9742d257f28d8d51345afa55d40aa3fea`, and source ledger SHA-256 `7b3a314baa17670e30f4c78b129493577e6873728c3ea6c0f1899d30d440070a`. Their immutable actual forest/EPPF, spectral and diagonal providers were authenticated in the preceding source review. The present proof retains those providers and their attribution; no freely chosen triangular matrix is declared an actual cell.

## True pair normalization

Let c_i=-log b2(B_i). Uniform compact-domain expansion gives c_i=h_i epsilon^2+O(epsilon^4) and therefore (hmin/2)epsilon^2<=c_i<=2hmax epsilon^2 for sufficiently small epsilon. Passing from nominal E_(-h_i epsilon^2)B_i to C_i=E_(-c_i)B_i changes a size-epsilon^6 horizontal coordinate only at order ten. The accepted nominal cancellation consequently leaves the uniform T-(5/3)X and U+(5/3)X errors O(epsilon^10). The identities X=Y and V=0 remain exact.

The diagonal improvement to I+O(epsilon^6) is valid. Pair normalization removes the arity-quadratic log term exactly. Finite Newton inversion through arity nine expresses every remaining log diagonal as a finite combination of D_k=O(epsilon^(2k)), k>=3. Exponentiation preserves O(epsilon^6). This argument needs only finitely many arities and compact analytic remainder bounds.

True pair normalization is used solely for deterministic matrix estimates. The proof does not carry martingale means, convex centering, source-image rank, or physical negative ordinary intervals through this source-dependent operation.

## Exact chronology and count dependence

At an ordinary endpoint, multiplicative pair survival gives exactly T=sum t_j+sum c_i. Thus the suffix-normalized product is identity, and every projected off-diagonal endpoint vanishes. Its nodes satisfy

    s_i-s_(i+1)=t_i+c_(i+1)>=(hmin/2)epsilon^2,
    0<s_L<...<s_1<T<=Hmax.

For S=L epsilon^2, the inequality B>=hmin S/2 is exact under the chosen uniform lower bound. The proof first derives estimates conditional on S<=1 and later obtains that condition from B<=B0. There is no circular use of a bound on L.

For S<=1, products of normalized diagonal entries have absolute value at most exp(Cd L epsilon^6)<=exp(Cd). Their differences from one are at most Cd L epsilon^6 exp(Cd). This applies to every diagonal subsequence occurring along a matrix path, including when the selected diagonal index changes at an off-diagonal insertion.

A horizontal intrinsic remainder contributes O(L epsilon^10); all diagonal weighting errors contribute O(L^2 epsilon^12)<=O(L epsilon^10). The only central paths are XU and YT. Their intrinsic errors contribute O(L^2 epsilon^16), and their accumulated diagonal weighting contributes O(L^3 epsilon^18)<=O(L^2 epsilon^16). The zero middle 7-to-6 entry rules out any path with three off-diagonal insertions. All spectral exponentials are bounded by the fixed target-time window. These facts establish CM and CV independent of L, as stated.

## Green energy and trace bounds

With a_i=exp(15s_i)x_i and beta=6, the exact identity relating the ordered exponential sum, Q, and the three moments is unchanged when their residual moments are nonzero. The endpoint equations therefore yield |Q|<=(CV/kappa)L^2 epsilon^16+CM^2 L^2 epsilon^20.

For F(x)=sum_i a_i sinh(beta|x-s_i|), the finite-interval identity is

    integral_(I)(F'^2+beta^2 F^2)=[F F']_boundary-4 beta Q,
    I=[-1,Hmax+1].

The two exponential moments control the boundary values and derivatives. The displayed CE consequently gives Energy<=CE L^2 epsilon^16 uniformly in L. No false compact-support assumption or inverse moment-matrix bound is used.

For c0=min(hmin/6,1/4) and ell=c0 epsilon^2, the symmetric node neighborhoods are disjoint even at the smallest permitted intrinsic spacing. The same endpoint derivative trace estimate and jump 2 beta a_i give

    Energy>=18 c0 epsilon^2 sum_i a_i^2.

This estimate does not lose an additional factor of the word count. It yields sum_i a_i^2<=[CE/(18c0)] L^2 epsilon^14.

## Mean-square amplitude and the positive threshold

From |x_i-(alpha_i/15)epsilon^6|<=Cx epsilon^8 and s_i>=0,

    (1/L)sum_i alpha_i^2
      <=(25 CE/c0)L epsilon^2+450 Cx^2 epsilon^4
      <=CA(S+epsilon^4).

The factor 25 is correctly 2*15^2/18. The stated CA=max(1,25CE/c0,450Cx^2) is sufficient. Averaging, rather than bounding each amplitude independently by a count-dependent maximum, is what permits the uniform conclusion.

Exact additivity of D4 and ordinary equality, followed by Cauchy-Schwarz, give

    hmin^4<=4hmax sqrt(CA(S+epsilon^4))+C4 epsilon^2.

For s0=min(1,hmin^8/(256 hmax^2 CA)) and B0=(hmin/2)s0, the assumption B<=B0 implies S<=s0. Its contribution to the right side is at most hmin^4/4. The displayed additional epsilon bound makes the remaining terms at most hmin^4/4. This contradicts the necessary inequality. All constants and the sufficiently small epsilon threshold are independent of the finite cell count.

No explicit numerical value of the compact-domain analytic remainder constants or of B0 is claimed to have been evaluated. Their finite uniform existence and the resulting positive threshold are proved.

## Scope reconciliation and limitations

The full ordinary cap-nine premise supplies X9=Y9=T=U=V=0 and D4=0 simultaneously. Lower-cap-eight equality plus b9 alone is weaker and does not supply the top off-diagonal equations. Selected T/U cancellation alone does not remove the actual intrinsic defects or enforce the fourth diagonal guard. In particular the corrected shrinking-gap grades in the separate Codex two-insertion package are not imported as substitutes for the present compact fair-source estimates.

The new accepted step is the count-explicit product accounting after true pair calibration, together with the mean-square trace/diagonal comparison. It strengthens the bounded-length exclusion to a positive bare-cell hazard floor for arbitrary finite word count in the stated class. The Green identity, source coefficients, source grammar and diagonal identities retain their inherited attribution. Historical novelty was not assessed.

The common epsilon, compact shape bound, hmin>0, bounded target time and fair base are essential current restrictions. The actual coin may still be 1/2+epsilon w with bounded w. Arbitrary per-cell scales, vanishing h, noncompact shapes, fixed biased bases, boundary coins, nonweak sources and general original words are outside the theorem. The interior-base source addendum has weaker order-nine errors and cannot be substituted unchanged into this count-uniform proof.

An ordinary-return family with L of order epsilon^-2 can spend a positive bounded bare-cell hazard and is not excluded by this theorem when that hazard exceeds B0. Original G4, positive full-forest centering and all-cap threshold alternatives remain open.

This is a hand proof review with source-byte authentication. No compiler, source program, symbolic or numerical expansion, parameter scan, or publication was run.
