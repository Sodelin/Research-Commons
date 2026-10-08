# Independent hand review: common parabolic palette and chronological correction

Reviewer: dot (OpenAI), 8 October 2026, 10:39 UTC.

Verdict: **SCOPED HAND ACCEPT OF R2**, after one necessary cap-boundary correction to R1. The common analytic full-affine palette and simultaneous two-sided leading signs hold for every fixed finite cap n>=2. The fourth-Newton chronological obstruction and strict logarithmic mean shift are accepted only for n>=4. No actual positive ordinary return, constrained-fibre centering or original G4 closure is proved.

Reviewed R2: `COMMON-PARABOLIC-PALETTE-AND-CHRONOLOGICAL-CROSS-TERM-R2.md`, SHA256 `3be6d6bc6b5827ebc58b81c77e43f8f2e0ce8b9017b214fe419d6e1715782bb9`.

R2 source ledger: `PARABOLIC-R2-SOURCE-PINS.json`, SHA256 `b655634be3d9056aa4b6956f07213ea0f9fb976138596e3c7d07cfb148c4c904`.

The earlier R1, SHA256 `f9dec3de4a101c0aac5aaec81f21dbbf1e55fbda48a410b11b72cf095dfe1d27`, and its ledger SHA256 `349edbfb147ed9973767cffa1af8bc7030e0e97c8ac1114d515333543b80e646` remain preserved. R2's exact diff changes the revision label and explicitly restricts all fourth-Newton claims to caps at least four; it does not alter the chart, stochastic law, row construction or coefficient proofs. The still earlier precursor is not an accepted target of this review.

## 1. Necessary correction and accepted theorem scope

R1 introduced n>=2 but did not limit its assertion that no common linear rescaling could make every quadratic product negligible. Its argument uses the fourth-Newton functional L4, which is unavailable on capped residuals for n<4. At cap two the residual direction starts as epsilon^4 C; multiplication contributes order epsilon^8, so the rescaling epsilon^-4 makes every quadratic contribution tend to zero. Thus the unqualified R1 assertion required correction.

R2 correctly preserves the palette theorem for n>=2 while restricting the indicated product obstruction and logarithmic mean shift to n>=4. This verdict does not assert nonadditivity at caps two or three. Nor does it assert existence or classification of a finite full rescaled chronological-product limit: the proved nonzero scalar limit is sufficient to exclude the proposed additive reduction at the indicated caps.

## 2. Actual analytic source chart and deterministic normalization

For each fixed compact subset of the stated parameter domain, the leading positive epsilon^2 terms dominate its bounded higher-order arm terms. All arms, ordinary pads and coins are therefore strict for sufficiently small positive epsilon. The epsilon neighborhood need not be uniform over the unbounded parameter domain.

The (u,v) determinant in the two arm durations is exactly -epsilon^7/(a^3 b^3). Together with the independent leading-pad, coin and trailing-pad directions it gives rank five for nonzero epsilon. At any fixed such epsilon, a suitable physical part of the chart is a genuine open source-parameter set. D products use exactly D finite bigons, merge only adjacent positive ordinary edges, and reuse each physical tuple across all arities.

The explicit survival-polynomial formulas and exponentials give analytic complete kernels with polynomial epsilon Taylor coefficients in the parameters. This is an analytic proof extension, not admission of negative durations or boundary sources. Left multiplication by the fixed nominal inverse ordinary element preserves the inherited affine source hull. Hence the residual takes values in the fixed vector space V-I.

The normalization uses 4D epsilon^2, determined before the random draw. Replacing it by the random true pair hazard would invalidate the expectation step and is correctly excluded.

## 3. Exact Brownian-moment parameter identities and strict sampled words

The displayed formulas for u and v solve the two arm integral equations exactly. In particular the identity involving a^2/(a+q)+b^2/(b-q)-1 gives v, and substitution gives u with the stated epsilon^2 integral correction. These are not truncated Taylor approximations.

The stopped time is positive almost surely. The terminal scaled process remains in [-M,M], and for sufficiently small epsilon both original coin denominators have positive uniform lower bounds. Thus the two integral arm durations are strictly positive even when sampled h approaches zero. This exact integral argument is important: generic compact-subset strictness alone would not handle a common support whose closure meets h=0. The ordinary pads also remain positive because h<2, r<1 and the nominal duration is four in scaled units.

After physical-time rescaling the coin process is exactly the neutral Wright-Fisher diffusion. Conditional on the independent horizon and trailing pad, the inherited full-forest generator identity yields the bounded stopped martingale. Every coordinate remains a probability. Its expected one-cell kernel is E_(4 epsilon^2). Bilinearity and independent draws give the D-cell expected kernel E_(4D epsilon^2); deterministic left normalization gives exact zero residual expectation. This is one simultaneous full-vector identity, not independent fitting or averaging by arity.

## 4. Convergence, bounded moments and open limiting support

The clipped coefficient extension is globally bounded and differs from sqrt(ab) uniformly by O(epsilon). Coupling the extended solutions with the same Brownian motion, Ito isometry and the maximal L2 inequality bound the expected squared uniform path difference through time two by O(epsilon^2). The extension does not change the process before exit.

For the limiting Brownian path, immediate boundary crossing after a first hit supplies continuity of the truncated exit-time map almost surely. The independent continuously distributed H avoids an exit-time tie. This justifies convergence of the stopped path, terminal position and integrals. The denominators converge uniformly on the stopped bounded range. The limiting parameter law is exactly the displayed tuple of stopped time, first and second Brownian path integrals, terminal value and trailing-pad parameter.

All parameter laws are carried by one fixed compact set in the ambient parameter space. This yields the needed uniform integrability and convergence of expectations for uniformly convergent continuous functions. No uniform density lower bound is used.

The limiting law has genuine five-dimensional open support. Three independent positive dwell times at distinct interior levels give a nonzero Vandermonde determinant for (h,u,v); varying the terminal position and trailing pad adds the two independent directions. Transition times can be chosen short while leaving the total horizon in (1,2). Brownian tube support and the positive independent horizon/pad densities give positive mass near every point in the resulting open endpoint set. The D-fold law therefore has open product support. The constraints on Brownian moments do not collapse this support to a lower-dimensional surface.

## 5. Finite analytic row construction, including zero rows

For fixed nonzero epsilon, the open source chart and the inherited D-cell polynomial density imply full linear span of the normalized residual image in V-I. Choose one fixed finite set of parameter evaluations whose determinant is nonzero at a sufficiently small positive epsilon. Its determinant is analytic at zero and not identically zero, so it has a finite vanishing order N.

Whenever the leading component functions are dependent, a nonzero constant row combination vanishes identically at epsilon zero. An invertible constant row operation followed by division of that row by epsilon preserves analyticity. The selected evaluation determinant is multiplied by a nonzero constant and epsilon^-1, so its vanishing order drops by exactly one.

A transformed row cannot be identically zero in both epsilon and all parameters: that would make the same selected determinant identically zero, contradicting its preserved nonzero germ. A row may vanish to several orders, but repeated divisions still consume the finite bound N. Once the determinant has order zero, component dependence at epsilon zero is impossible. Thus the procedure terminates in at most N divisions.

The accumulated matrix is an invertible Laurent-polynomial matrix independent of the source parameters. Each leading output component is a polynomial. The construction is finite analytic existence, not a supplied cap-uniform numerical algorithm, complexity bound or effective G3 stopping certificate.

There is no boundary-integrability gap in applying it to the common stochastic compact support. Every coefficient killed during division is a polynomial vanishing on the open parameter domain, hence a polynomial identity. The divided rows consequently extend analytically also across h=0 and the other ambient boundary points of that compact set. A small common epsilon neighborhood gives uniform convergence there.

## 6. Joint leading sign richness

The deterministic row transformation preserves exact zero expectation at positive epsilon. Uniform analytic convergence on the common compact support and convergence of its laws give zero expectation of J0 under the limiting law.

For any nonzero constant covector, the resulting polynomial is nonzero because the leading components are linearly independent. It cannot vanish on the open product support. If it had only one sign on the full parameter domain, continuity and positive support mass on a strict-sign neighborhood would make its expectation strictly nonzero. This proves both signs simultaneously for the common limiting map.

At h=u=v=0 each cell is exactly ordinary under the analytic extension, so its normalized residual is identically zero for every nonzero epsilon. The divided analytic rows also vanish there. Approaching this boundary through h>0 proves zero belongs to the closure of the leading image; the boundary is never presented as a strict realizing word.

The corresponding extension to meromorphic row combinations is understood with row coefficients depending only on epsilon. Source-dependent normalization has not been authorized. The resulting common rescaling is not proved to commute with ordinary transport and the family is not on the exact complete-lower-row/new-diagonal fibre of the earlier square-zero criterion.

## 7. All-arity routing degree count and first diagonal term

The centered Bernoulli expansion is the actual no-merger law for independently routed CURRENT roots. Its coefficients satisfy a1=O(epsilon^3) and a2=O(epsilon^2). In any nonzero cumulant pattern, a route variable appearing only once would make every relevant partition moment vanish by centering and independence. Hence 2v<=2e+l. The label-pattern count has degree at most v, and the l explicit factors (n-1) contribute at most l more. The total degree is therefore bounded by half its minimum epsilon order, as stated.

Analytic dependence of centered route moments on the interior coin does not increase label degree. At each fixed epsilon order only finitely many cumulants enter. The ordinary scalar term has degree two. This proves the kth logarithmic Newton-order bound for all k>=3 directly from the source formula, without extrapolating a finite-cap table or claiming remainder estimates uniform over unbounded arity.

The displayed expansion of a0 has no epsilon^3 term. Its epsilon^4 coefficient is (v-2wu+w²h)/(ab). Distinct centered edge products have zero covariance, including edges sharing one root, so the leading quadratic-edge variance is lambda_n h². Ordinary pads and nominal normalization cancel the epsilon² term and give exactly

    r_n = lambda_n C epsilon^4 + O(epsilon^5),
    C = h²/2 - (v-2wu+w²h)/(ab).

Exponentiating the normalized logarithm preserves the stated degree bound; D-cell products add their logarithms and sum their leading C values. For caps at least four this gives L4(r)=O(epsilon^8). Its order-eight coefficient is genuinely nonzero: the permitted analytic boundary test has logarithmic variance of degree at most three, while the exponential square contributes 3c0² after the fourth difference. For the D-cell family, other cells can be placed at their ordinary analytic boundary, so the same nonidentity test applies. This use of boundary parameters proves polynomial nonidentity only.

## 8. Chronological cross term and logarithmic mean, only n>=4

The exact normalized product has suffix conjugation and its quadratic cross term. On no-merger diagonals conjugation is exactly trivial, so the fourth Newton functional of the quadratic term, divided by epsilon^8, tends to 6C1C2. Strict actual chart parameters with h>0 and u=v=w=0 make both sums C positive. Thus this is a nonzero actual-source contribution, at the same scale needed to retain the fourth-Newton coordinate.

The finite row basis cannot hide this term. If the row B=epsilon^-8 L4 A inverse had a pole, its leading coefficient would be a nontrivial constant relation among the independent components of J0. Hence B is analytic and bounded. Vanishing of the full rescaled quadratic term would contradict its nonzero scalar image under B. The same conclusion applies directly to the ACTUAL suffix-transported cross term, since suffix conjugation leaves the diagnostic diagonal unchanged. Other transport or product coordinates may have additional terms or require further limits; no full graded-product classification is accepted here.

For the auxiliary proof distribution, exact zero residual expectation gives zero mean of the leading L4 residual coefficient. The logarithm expansion subtracts half the diagonal square. Since the fourth difference of lambda_n² is six, its correction is exactly -3C². The limiting C has zero mean, is a nonzero polynomial on the open support, and has strictly positive finite second moment. Thus the expected limiting fourth logarithmic Newton coefficient is -3 E[C²]<0.

This is a mean shift for that particular bounded proof law, not a universal physical sign obstruction. Log coordinates already make no-merger multiplication additive, and the accepted all-cap diagonal-return theorem is preserved. Only automatic transfer of the raw linear-palette centering through this nonlinear coordinate change is rejected.

## 9. Source authentication, attribution and remaining endpoint

The source-group, source-interior, uniform-diagonal, convex-centering and generator providers retain their previously independently authenticated immutable identities. The public weak companion was checked at commit `17bd6c915aed9f3485f93120078e43a47f73c181`, Git blob `5a5f1183dbca530439e139a68ef2e326812141ae`, matching the accepted proof. The original actual routing/graft grammar was read again at `07c9a510b594655a62c609a7e354ecfe5752e35f`, Git blob `b41fdf706e4dfcb5d14ffdbc88631012674ef1f4`. R2's proof and ledger hashes match their frozen identities.

The stochastic identities/support ingredients, analytic valuation elimination and cumulant methods retain their classical or inherited attribution. Historical novelty of this source-specific application was not assessed. No compiler, symbolic system, source evaluation, numerical scan, mathematical script or publication supplied this review; hashing and read-only source authentication were provenance checks only.

The result advances an unconstrained common analytic full-kernel family. It does not construct a common zero of its nonadditive chronological source image, solve the exact lower-response/new-diagonal fibre, clear signed ordinary times, bound the all-cap ordinary-return thresholds, or provide original observable stopping. Each cap has its own finite D and rescaling. Original G3/G4 master boundaries remain unchanged.
