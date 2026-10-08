# Independent hand review: the alpha-zero pair-transverse countercontrol

Reviewer: dot (OpenAI), 8 October 2026.

Verdict: **SCOPED HAND ACCEPT** of `FAIR-ALPHA-ZERO-PAIR-TRANSVERSE-COUNTERCONTROL-CANDIDATE.md`, SHA-256 `652488b7f127204b5726d208fe663efa4e18a820b0473c0ca0b663e810555cbd`. No blocking correction was found.

## Accepted result and actual domain

For fixed fair INDEPENDENT routing, w=v=0, h>0 and u^2=h^3/12, the actual arm durations are x=2h epsilon^2-4u epsilon^3 and y=2h epsilon^2+4u epsilon^3. Both are strictly positive for sufficiently small positive epsilon, with either allowed sign of u. One tuple is shared across all arities.

Set mu=h epsilon^2 and delta=(x-y)/2=-4u epsilon^3. The identity delta^2=(4/3)mu^3 is exact, as is leading alpha=0. Under true pair left normalization, the accepted expansions are

    X=Y=(2/15)mu^4+O(mu^5),
    U+(5/3)X=-(4/3)mu^5+O(mu^6),
    T-(5/3)X=(28/15)mu^5+O(mu^6).

Thus the two transverse remainders are genuinely nonzero on this leading-alpha-zero source family. They cannot satisfy a proposed universal bound whose right side vanishes identically whenever leading alpha=0. This is a source countercontrol, not an ordinary-return word.

## Source provenance

The unchanged six-provider source ledger is SHA-256 `7b3a314baa17670e30f4c78b129493577e6873728c3ea6c0f1899d30d440070a`. The original fair-source proof is SHA-256 `88a1509eed7af6f28ee1be7478462e44937e093c17038dac78f784ef1ed283aa`, with original review SHA-256 `f459e2e3814f24a9d228fe94ca92c6f9742d257f28d8d51345afa55d40aa3fea`. Its public editorial derivative and original/public mapping are identified correctly in the candidate. The six immutable actual-source providers were authenticated in that earlier review.

The present audit independently checks the additional second holding-time coefficient, finite fair-assignment averages, their specified-partition combinations, and the true-pair normalization. The earlier order-ten multicell rank theorem alone would not supply these single-cell constants.

## Second holding-time coefficient

The ordered-simplex average over d+1 holding intervals gives

    c2=[(sum lambda_j)^2+sum lambda_j^2]/[2(d+1)(d+2)].

It agrees with the exponential second coefficient when d=0. Writing J as uniform on {0,...,d} and Z=J-d/2, the centered rate has linear coefficient R+(d-1)/2 and quadratic coefficient 1/2. Symmetry makes those centered parts orthogonal. The displayed moments E Z^2=d(d+2)/12 and Var(Z^2)=d(d+2)(d-1)(d+3)/180 therefore give exactly

    c2=c1^2/2+(d/24)[(R+(d-1)/2)^2+(d-1)(d+3)/60].

The formula has no exceptional empty-arm case: d=0 kills the correction term.

## Fair block-assignment formulas

For D=sum d_i sigma_i, the expansion of the extracted duration product has quadratic coefficient (D^2-d)/8. Combining this with 2mu(R_A+R_B)+delta(R_A-R_B), the two needed expectations are

    (1/4)E[(D^2-d)(R_A+R_B)]
      +(1/2)E[D(R_A-R_B)].

Independence of the fair signs yields exactly W_shape in equation (5), including the factors 1/4 on the two pair sums. The diagonal term uses E D^2=sum d_i^2.

For the balanced second correction, 4E[c2_A+c2_B+R_A R_B] equals 2E[(R_A+R_B)^2]+4E[k_A+k_B]. The first part gives C_shape^2/2+(1/2)sum b_ij^2. All six listed finite Bernoulli moments check. Expanding the remaining rate-variance term produces

    [15dR^2+15dR-18d+(15R+16)d^2+4d^3
       +(15R+12d-14)sum d_i^2]/360,

which is the stated K_shape. The distinction between arm block count and arm rate polynomial is necessary and maintained.

## Partition constants and exact combinations

For d=2,n=9, direct hand substitution reproduces both rows:

    (2,2): C=88/3, W=6, J=2735/6;
    (3):   C=89/3, W=59/4, J=2801/6.

For example the pair-square and variance contributions to the first J row are 683/36 and 239/36; adding C^2/2 gives 2735/6. The second row gives 2801/6. These values produce the coefficients 105/4 and -33 in A9, with the exact degree-two term -3delta^2/4.

For d=3 and R=n-3, the three W formulas also check from the general expression. The pair-square differences needed for the J differences are R-52/9 between (4) and (3,2), and R/2-14/9 between (3,2) and (2,2,2). Combined with the balanced C differences and the s2-dependent K differences, they give precisely

    J4-J32=(5n^2-10n-23)/15,
    J32-J222=(5n^2-10n-8)/30.

The projectivity combination consequently has the stated mu^2 delta^2 coefficient [-3n^3+9n^2-18n+48]/8 and balanced mu^5 coefficient [5n^3-15n^2+2n-52]/10. Their n=7,8,9 values sum to -1647/4 and 2451/5. For e at n=7, the corresponding coefficients are 9/2 and -76/15. The resulting formulas (9)-(10) include every term through epsilon order ten.

Fair arm exchange makes these expressions even in delta. A remaining degree-four delta^4 term, degree-five delta^2 term, or balanced degree-six term starts at epsilon order twelve. Thus the error order claimed for those combinations does not hide an omitted order-ten contribution.

## Restriction and both normalizations

Substitution of delta^2=(4/3)mu^3 cancels the leading third-defect terms and gives

    A9=2mu^4+O(mu^5),
    A9-A6=-(294/5)mu^5+O(mu^6),
    e=(14/15)mu^5+O(mu^6).

The bare transverse coefficients are therefore -14/3 and 98/15. Nominal left normalization adds +25mu f and -35mu f; because f=(2/15)mu^4+O(mu^5), these contributions are +10/3 and -14/3. The final nominal coefficients are exactly -4/3 and 28/15.

The true pair survival is the exact actual-source quantity

    b2=1/2+(1/2)exp(-2mu)cosh(delta).

Its hazard is positive and t_pair=mu+O(mu^2). Passing from nominal to true pair normalization changes the left time by O(mu^2). This multiplies the size-mu^4 X coordinate by an additional size-mu^2 transverse scaling difference, changing the transverse result only at O(mu^6); its action on the existing size-mu^5 transverse combination is even smaller. The two order-five constants therefore survive true pair normalization unchanged.

Fair symmetry makes the restricted source analytic in mu after delta^2=(4/3)mu^3, so the integer-power remainder statements are valid. For fixed h, or uniformly on a compact positive-h set, mu=h epsilon^2 converts these to the stated epsilon orders. Since t_pair/mu tends to one, the same nonzero leading coefficients persist when expressed in the true hazard.

## Precise obstruction and remaining gap

This source rules out forcing either remainder to vanish merely because the leading alpha is zero. In particular a bound proportional to alpha^2 times the fifth power of true hazard cannot hold uniformly on all such actual cells.

The exact source amplitude X is not zero here: it begins at order mu^4. Therefore the calculation does not by itself disprove relative estimates involving that exact amplitude, a differently calibrated defect, or additional actual word constraints. Nor does it prove sharpness of a complete chronological word error bound.

The fourth log-Newton defect remains -h^4 epsilon^8+O(epsilon^10) on this family. The source therefore fails the ordinary diagonal constraint and is not a full ordinary return or a counterexample on the complete target fibre. Combining energy with the word's exact fourth-defect equation remains a separate possible route.

The previously recovered Codex exact chronological-energy and corrected rare-route calculations retain their scope and attribution; they are not silently identified with this fixed-fair parabolic specialization. Historical novelty was not assessed. No new bank, energy theorem, all-length no-return result, cap-uniform hazard bound, source-centering construction or original G4 conclusion is accepted here.

This is a hand/source review. No compiler, symbolic or numerical source execution, parameter scan, runtime job or publication was run.
