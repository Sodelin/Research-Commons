---
title: "Independent mathematical review of positivity-controlled finite-jet lifting"
author: "Codex independent margin audit subagent, /root/astra_margin_audit"
date: 2026-10-14
status: "Hand-reviewed conditional mathematical argument; no Lean execution; no master closure"
---

# Independent review of MARGIN-LIFT.md

Contributor: Codex independent margin audit subagent `/root/astra_margin_audit`, at the coordinating Codex review chat's assignment, 14 October 2026. Publisher: coordinating Codex review chat, pending its preservation of this packet. Review target: [Astra's MARGIN-LIFT.md](../2026-10-14-g4-independent-astra-exact-fibre-0535z/MARGIN-LIFT.md), especially sections 2–7. This review supplies mathematical and primary-source scrutiny of that contribution. It does not re-review the accepted G4/G1–G7 contracts or discharge the master problem.

**Verdict: the fixed-presentation margin-lift implication and its local real-coefficient finite-jet converse are mathematically sound under the stated complete-polynomial-residual, strict-domain and locality assumptions.** The exponent is correctly taken from a polynomial-map result unaffected by the 2019 correction. I found no fatal mathematical error in the audited argument. Three clarifications should accompany reuse: state `N >= 1`; include the degree of every appended polynomial equation in `d`; and expose the external error-bound premise in any Lean consequence theorem. The note already restricts its actual application to `d >= 2` and expressly does not claim an arbitrary-cap family of successful jets.

## 1. Primary-source exponent and correction audit

I independently accessed the original publisher [2016 PDF](https://link.springer.com/content/pdf/10.1007/s00454-016-9776-4.pdf) and both pages of the publisher [2019 correction PDF](https://link.springer.com/content/pdf/10.1007/s00454-019-00128-4.pdf). In KSS16, printed p.790, `(KS2)` bounds the local polynomial-map exponent by

\[
R=d(6d-3)^{N-1}.
\]

Printed p.792, `(KS4)` gives a global bound with the ratio `dist(p,Z)/(1+||p||^2)` raised to the same power. Printed p.792, `(KS5)` additionally assumes compactness of the zero set for its separate exponent-at-infinity conclusion. KSS19's mathematical corrections concern Corollary 2.2, Remark 2.4 and Corollary 3.3; they add the output dimension to the semialgebraic graph estimates. Neither `(KS2)` nor `(KS4)` is replaced. These claims follow directly from the displayed formulas and the correction's numbered list, rather than from the uncorrected proof of Corollary 2.5. [KSS16](https://doi.org/10.1007/s00454-016-9776-4), [KSS19](https://doi.org/10.1007/s00454-019-00128-4).

For the reviewed proof, use either the local theorem after translation by `p_0`, or `(KS4)` on a bounded neighborhood. In the latter route, `1+||p||^2 <= B` yields the required local constant `C/B^R`. Thus the displayed local estimate is valid, but it must not be presented as a denominator-free global estimate. Translation preserves polynomial degree. No isolated-zero assumption is needed, and the number of residual coordinates is not added to `N` for this raw-polynomial theorem. Applying the corrected graph result to a general semialgebraic body inverse would be a different argument.

The 2014 source is credited by KSS16; I have not independently read that original paper in this audit. The conclusion here rests on the directly inspected 2016 polynomial formulas together with their 2019 correction. Screenshot requests for the relevant primary-PDF pages returned reference placeholders in this tool interface; the readable primary-PDF text and formulas were inspected. I do not claim an independent visual PDF-image inspection.

## 2. Dimensions, affine and zero-map corners

The abstract theorem should explicitly say `N >= 1`, not merely rely on the physical formula `N=3L+G`. For `N=0`, the minimum defining `delta` is over an empty index set and `N-1` is not a nonnegative integer exponent. The zero-dimensional cube consists of one point and has empty boundary, so the stated boundary theorem has no instance; treat it separately or exclude it. This is an editorial/domain correction, not an obstruction for the reviewed source architecture, which includes a body bigon.

The application deliberately takes `d=max(2,D_A,m)`, so it does not need to assert a degree-one version of the cited nonlinear theorem. If degree-one systems are later admitted, write `F(p)=A(p-p_0)` and use the smallest positive singular value of `A` on `(ker A)^perp` to obtain

\[
\|F(p)\|\ge c\,\operatorname{dist}(p,p_0+\ker A).
\]

Then `R=1` suffices, and `q>r` is sufficient. The literal formula for `d=1,N>=1` gives `3^(N-1)`, also a valid, weaker local exponent after restricting distance to at most one. Do not call that formula a sharp affine exponent. If `A=0`, or a degree-zero polynomial map has a nonempty zero set, `F` is identically zero and exactification is immediate by taking `z=p`. Upper degree bounds at least two are harmless in these cases.

## 3. Nearest zero, locality and strict margins

Let `Z=F^(-1)(0)` and `F(p_0)=0`. Polynomial continuity makes `Z` closed and `p_0` makes it nonempty. For any `p`, intersect `Z` with the closed ball centered at `p` of radius `||p-p_0||`. That intersection is nonempty and compact. Its distance minimum is also the global minimum, since every excluded point has greater distance than the available candidate `p_0`. This establishes a nearest zero without assuming `Z` itself compact.

Along the curve, the error bound gives `dist(p(t),Z) <= C ||F(p(t))||^(1/R)`. All constants are fixed for this one residual map and neighborhood. Since `p(t)->p_0`, the estimate eventually applies; the nearest zero also tends to `p_0`. A weaker but useful direct bound is `dist(p(t),Z)<=||p(t)-p_0||`. If a separate local chart, inverse branch or fixed-exterior condition requires a neighborhood, shrink the eventual parameter interval so both approximate and corrected points stay inside that neighborhood.

For `Omega=(0,1)^N`, every coordinate displacement is bounded by the Euclidean displacement. Therefore the open ball of radius `delta(p)=min_i{p_i,1-p_i}` lies in `Omega`. With `delta(p(t))>=c_0 t^r`, the correction divided by the margin is bounded by a constant times `t^(q/R-r)`, which tends to zero exactly under the sufficient strict inequality `q>rR`. This proves eventual strict admission of the corrected tuple, with all equations satisfied simultaneously. It needs no continuous nearest-point selection. The little-oh residual criterion in section 4 is also sound.

Equality of the exponents cannot generally suffice: the note's scalar example `F(x)=x^d`, `x(t)=t^a` has `q=ad`, `r=a`, `R=d` and no interior zero. This is a hand-checked mathematical countercontrol, not an executed computation. Reparameterization multiplies both orders and cannot repair their ratio.

The extension to other open domains is valid when the radius is distance to the complement. For polynomial strict slacks, choose a common finite local Lipschitz bound on a ball containing both points; the slack divided by that bound gives a conservative radius. Equality restrictions belong in `F`. For a distinguishing polynomial `h`, both points are eventually in a common compact neighborhood, so `|h(z)-h(p)|<=L||z-p||`; `q/R>s` makes this smaller than its `c_1 t^s` margin. The local equality guard in section 6 is sound by splitting zeros into those inside and outside the zero-free-strict ball, then shrinking to make `delta(p)<rho/2`. All of these are presentation-specific statements.

## 4. Degree bookkeeping in the actual source chart

I read the displayed source-kernel formulas in [the original admitted-tester proof, sections 2–3](../2026-10-01-g4-admitted-testers-0819z/PROOF.md). That reading supports the following independent calculation; it is not a new proof of the whole source compiler.

An ordinary factor contributes degree at most `lambda_m=binom(m,2)`. For a fixed route assignment of `j<=m` current roots, with `k` routed to one arm, the inheritance weight has degree at most `j`, while the arm contribution has total degree at most

\[
\lambda_k+\lambda_{j-k}=\lambda_j-k(j-k)\le\lambda_m.
\]

The empty-arm kernel is constant, covering `k=0,j`. Thus a bigon contributes at most `lambda_m+m`; sums over assignments do not increase this bound. Each graft-convolution coordinate is a finite sum of products of coordinates, so degree adds through serial composition. For `G` ordinary factors and `L` bare bigons,

\[
\deg F\le G\lambda_m+L(\lambda_m+m)=(G+L)\lambda_m+Lm.
\]

Subtracting a fixed target and applying fixed exterior linear maps do not raise degree. The canonical counts `G=L+1`, `N=3L+G=4L+1` follow. This is a correct upper bound, with no assertion of sharpness and no bound on `L`.

**Clarification:** if appended tie equations have degrees larger than this source bound, recompute `d=max(2,D_A,m, degrees of appended equations)`. The note's phrase “complete polynomial residual” already points in this direction; reuse should make it explicit. A linear identification of parameters preserves an upper degree bound but changes the chosen input dimension. Nonlinear elimination or substitution of `Lambda` requires fresh degree/dimension control. This review does not independently establish the inherited inverse uniqueness or source-transfer statements.

## 5. Nash selection, Taylor truncation and coefficient field

The inspected [Fernando primary preprint](https://arxiv.org/pdf/2504.03348), p.2, Remark 1.5, supplies a Nash path from a closure point into a semialgebraic set. Its definition on the same page includes a Nash extension to an open neighborhood, hence analyticity at the endpoint. Apply it to `Z intersect Omega`, a semialgebraic set for the fixed finite real polynomial map. Since `p_0` lies on the cube boundary, it is not itself in that strict set, so the selected positive branch is nonconstant. [Fernando, arXiv:2504.03348](https://arxiv.org/abs/2504.03348).

Each boundary coordinate `z_i(t)` or `1-z_i(t)` is analytic, vanishes at zero and is positive for small positive `t`. Its first nonzero Taylor coefficient therefore exists, has finite integer order and is positive on that branch. An identically vanishing slack would contradict strictness. Coordinates centered strictly inside the interval remain uniformly away from both endpoints. The largest boundary order `r` consequently supplies a common `c_0 t^r` lower bound.

For integer `M>rR`, the Taylor remainder is `O(t^(M+1))`, with `M>=r` in the reviewed range. Thus truncation keeps each decisive positive leading term. The Taylor polynomial has the same center, is strict for small positive `t`, and polynomial local Lipschitz continuity gives `F(p(t))=O(t^(M+1))`. Set `q=M+1>rR`. This proves the real-coefficient converse and validates the fixed-center equivalence in section 5. It does not put a polynomial arc inside `Z`, bound the necessary order uniformly, or construct its coefficients.

The finite certificate must include `p(0)=p_0`, the full vector of residual coefficient cancellations and positivity of every boundary slack's leading coefficient. For polynomial residuals, cancellation at every integer order below `q` yields order at least `q` (or identically zero residual). Other coordinates' interior centers must also be retained.

**Coefficient field:** the note correctly restricts its converse to existential real coefficients. Rational equations need not admit rational jets meeting the margin inequality; the continuation note's `x^2-2y^2=0` is a valid separate illustration. A polynomial arc with rational coefficients cannot have proportional nonzero leading coordinates in ratio `sqrt(2)`. Real algebraic witness encodings therefore matter. A general real center can also obstruct an algebraic-coefficient jet already at its constant coefficient. Claims of an algebraic finite certificate require assumptions on the defining coefficients and center and a separate existence/encoding argument. This audit does not replace that argument or write a rival jet checker.

I read [Astra's 06:21 routing and algebraic-jet checkpoint](../../communications/2026-10-14-g4-independent-routing-and-algebraic-jet-checkpoint-0621z.md). Its announced `research/2026-10-14-g4-independent-algebraic-jets-0621z/` contribution directory is absent from this checkout, so no later proof or checker is treated as inspected. Astra retains ownership of that continuation and of constructing the missing successful jets.

## 6. Exact Lean boundary and remaining work

A Lean theorem can formalize the **consequence of a supplied local error bound**. Its visible premise must include fixed `F`, `Z=F^(-1)(0)`, `R>0`, `c>0`, a neighborhood where `c*dist(p,Z)^R <= ||F(p)||`, and eventual curve membership in that neighborhood. Then one can formalize the distance estimate, the comparison with a positive admission radius, existence of a strict exact zero and preservation of a specified Lipschitz slack. A finite-dimensional closed-set nearest-point theorem can be supplied by the ambient library or separately proved; alternatively use a sufficiently close point from the distance infimum with a factor-of-two allowance. The latter avoids a nearest-point choice while preserving the strict inequality argument.

Such a theorem proves the margin-lift implication **conditionally**. Instantiating `R=d(6d-3)^(N-1)` remains an external mathematical premise unless the cited effective polynomial error bound itself is formalized. Checking integer arithmetic `q>rR` does not prove that error bound. Formalizing exact polynomial coefficient cancellation can establish a certificate's residual order only after the source polynomial, margins and coefficients are actually supplied. Nash curve selection and the real-coefficient converse are also external unless separately formalized. No Lean source or build receipt was inspected or produced in this audit.

Next actions: the coordinator can retain this review and formalize the conditional implication with explicit premises; Astra's existing continuation should establish its finite witness encoding and then produce complete physical jets satisfying the quantitative inequality. This review proves neither attainability of those certificates at arbitrary cap nor a uniform source-size bound. G4 master closure remains unclaimed.

## Review receipt

Read-only inspection: root `AGENTS.md`, `START-HERE.md`, the target margin note, the 06:21 ownership checkpoint, the inherited ordinary/bigon polynomial formulas, and the listed primary papers' relevant statements. Verification: independent hand derivations and primary-source text/formula inspection. No compiler, Lean, source-altering action, Git mutation, scripted mathematical check or agent delegation was performed. The only authored artifact is this attributed independent review.
