# Independent hand review: interior-base source coupling

Reviewer: dot (OpenAI), 8 October 2026.

Verdict: **SCOPED HAND ACCEPT, SOURCE ONLY** of `INTERIOR-COIN-SOURCE-JETS-ADDENDUM-CANDIDATE.md`, SHA-256 `81de27ab78b4bf8b8889d2b8a7005194264b831396a50ac0d71076899ac660b6`. No blocking correction was found. The accepted fair-base proof and its separate rank theorem remain unchanged.

## Source identity and scope

The addendum extends the actual INDEPENDENT bare-cell jet derivation to any base a in a fixed compact subset of (0,1), with b=1-a and common parabolic scale epsilon. The actual cell parameters are x=epsilon^2 h/a-epsilon^3 u/a^2+epsilon^4 v/a^3, y=epsilon^2 h/b+epsilon^3 u/b^2+epsilon^4 v/b^3, g=a+epsilon w. Compact h,u,v,w with h bounded below by a positive constant make every sufficiently small positive-epsilon source strict, uniformly. Base coins may vary between cells inside that fixed compact interval.

The bare-cell statement has no r parameter and does not require h+r<4. If the result is inserted into the previously accepted padded F chart, that chart's positive-pad condition h+r<4 must still be retained. The inverse E_(-h epsilon^2) is solely a deterministic proof normalization.

The original source proof is SHA-256 `88a1509eed7af6f28ee1be7478462e44937e093c17038dac78f784ef1ed283aa`; its hand review is SHA-256 `f459e2e3814f24a9d228fe94ca92c6f9742d257f28d8d51345afa55d40aa3fea`. The unchanged source ledger is SHA-256 `7b3a314baa17670e30f4c78b129493577e6873728c3ea6c0f1899d30d440070a`. Its six immutable providers were authenticated in that source review. No new unpinned representation is introduced.

## General-base substitution

Writing zeta=wh-u, direct multiplication gives gx-(1-g)y=epsilon^3 zeta/(ab)+O(epsilon^4). The epsilon^3 terms of g^2 x and (1-g)^2 y are 2wh-u and u-2wh and cancel. Thus mu=h epsilon^2+O(epsilon^4), sigma2=zeta^2 epsilon^6/(ab)+O(epsilon^7), and mu3=O(epsilon^9). These bounds are uniform under the stated compact-interior restriction.

The balanced partition correction used by the fair proof is independent of the base routing probability: after the two-arm assignment average, the terms divided by g and 1-g combine using g+(1-g)=1 and g(1-g)(1/g+1/(1-g))=1. This permits reuse of the displayed balanced coefficients at general a; no arm-exchange parity is assumed.

The degree-two part of A_n is -3 sigma2 and its balanced degree-three part is mu^3. Hence A_n=alpha epsilon^6+O(epsilon^7), with alpha=h^3-3 zeta^2/(ab). The exact selected-label difference supplies

    A9-A6=63 mu sigma2-21 mu^4+O(epsilon^9)
          =-21h alpha epsilon^8+O(epsilon^9).

The omitted third central moment is order nine; changes in the balanced degree-four correction also start at order nine, and degree-five terms start at order ten. The same accounting gives e=h alpha epsilon^8/3+O(epsilon^9). Therefore H-(5/3)f=(7/3)h alpha epsilon^8+O(epsilon^9) and U+(5/3)f=-(5/3)h alpha epsilon^8+O(epsilon^9), with the exact bare U=-H+2e.

## Nominal cancellation and diagonal order

For C=E_(-h epsilon^2)B, the exact row multipliers are exp(36h epsilon^2) for X=Y, exp(15h epsilon^2) for T, and exp(21h epsilon^2) for U. Their order-eight differences cancel the two bare coefficients exactly. Consequently X=Y=(alpha/15)epsilon^6+O(epsilon^7), T-(5/3)X=O(epsilon^9), U+(5/3)X=O(epsilon^9), and V=0.

The deterministic diagonal coefficient is also consistent: the epsilon^4 term in mu is (v-2wu+w^2h)/(ab), while the leading second cumulant supplies h^2/2 after logarithmic normalization. Thus diagonal_j(C)=1+lambda_j c epsilon^4+O(epsilon^5), for the stated c. Source-dependent pair normalization and stochastic averaging are not substituted.

Without fair-base parity, neither an order-ten remainder nor vanishing of an order-nine transverse coefficient is established. The proof correctly claims no nonzero order-nine coefficient, sign, or rank. Its source-only conclusion is compatible with the earlier fair-base order-ten rank result.

## Log-Newton coefficients

The inherited connected-incidence argument applies for each fixed k>=3. The leading centered-route coefficients are epsilon^3 zeta/sqrt(ab) and epsilon^2 h. A term reaching both epsilon order 2k and top label degree k uses only saturated connected paths or cycles; every active centered variable then occurs twice. Higher centered moments, the changing coin, and v cannot change that leading top-degree coefficient. The arity-quadratic ordinary term is annihilated for k>=3.

This yields the stated

    J_k=(-1)^k (k-1)!/2 h^(k-3)[h^3-k zeta^2/(ab)],

with O(epsilon^(2k+1)) remainder for fixed k. In particular J3=-alpha and J4=-h^4+4h alpha. At alpha=0 and h>0, the latter is strictly negative. The claim is not uniform over unbounded k.

## Boundary of this acceptance

The order bookkeeping proposed for a separately audited bounded-length energy argument is consistent: horizontal errors of order nine, central errors of order fifteen, and boundary terms of order eighteen would combine with intrinsic epsilon^2 spacing to give alpha_i=O(epsilon^(1/2)). This review accepts those source estimates, not a generalized no-return theorem by inference. In particular the fair word-count-uniform estimate cannot be imported unchanged after weakening its error orders.

The complete ordinary cap-nine endpoint used by the separate Green proof includes X9=Y9=0 and the vanishing fourth diagonal defect. Lower-cap-eight equality plus the new b9 diagonal alone is a weaker premise and does not supply those top off-diagonal equations. Selected T/U cancellation alone supplies neither the full endpoint nor the diagonal guard. No corrected shrinking-gap grade claim is inferred from those weaker data.

Unbounded length, boundary coins, vanishing h, noncompact shapes, different cell scales, nonweak cells, positive source centering, uniform all-source budgets and original G4 remain outside this result. Prior source grammar, EPPF, spectral, parabolic and cycle/path arguments retain their attribution. Historical novelty was not assessed. This is a hand/source review; no compiler, numerical or symbolic source execution, parameter scan, or publication was run.
