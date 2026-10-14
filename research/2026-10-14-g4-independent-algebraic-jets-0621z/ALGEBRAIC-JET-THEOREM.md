---
title: "Algebraic finite-jet certificates for a fixed physical fibre"
author: "Independent Astra G4 research contributor"
date: 2026-10-14
status: "Hand-derived classical composition; independent review pending"
tags: [G4, finite-independent, real-algebraic, exact-certificate, local-fibre]
---

# Algebraic finite-jet certificates for a fixed physical fibre

## 0. Decision brief

For a FIXED finite polynomial physical chart with algebraic data and a FIXED algebraic boundary presentation, strict exact solutions with a specified polynomial distinction accumulate at that presentation if and only if an appropriate FINITE polynomial parameter jet exists with REAL ALGEBRAIC coefficients. Every coefficient can be represented using one shared isolated real root. Rational-only coefficients are not a complete substitute.

The certificate threshold is

    q > R max(r,s),     R = d(6d-3)^(N-1).

Here q is the vanishing order certified for the COMPLETE residual, r is the worst strict-domain margin order, and s is the order of the specified nonzero distinguishing polynomial. This strengthens the previous margin-lift certificate format by giving an exact finite algebraic representation and preserving distinction. It does not supply G4 source jets at every cap.

Evidence: a hand argument composing classical polynomial error bounds, Nash curve selection and elementary transfer for real closed fields; an executed exact-arithmetic reference checker; abstract polynomial controls. No independent proof acceptance, historical novelty, Lean compilation or native-solver integration is claimed. The concrete rational G4 target is retained. Arbitrary transcendental target data are not covered by the algebraic representation converse.

## 1. Abstract

A finite real-coefficient jet is a mathematical existence certificate but need not be a finite machine-readable exact witness. We show that, for fixed algebraic input data, any successful jet can be replaced by one with algebraic coefficients while keeping the target, boundary presentation, coefficient vanishing conditions, positivity orders and nonzero distinction. A single real embedding then suffices to represent and check all rows. An explicit rational polynomial example demonstrates why merely searching rational jets is incomplete. This is a local certificate theorem, not an unknown-size recognition algorithm or an all-prefix G4 rival construction.

## 2. Source and original obligation

The governing G4 source has one admitted finite graph and one shared physical parameter tuple across EVERY experiment. Keep the original labels, joint controls, current opaque-root INDEPENDENT routing, finite positive exposures and interior inheritance. Legal observations remain rooted labelled topology laws. Full capped forest/graft equality is a sufficient transfer device from the inherited source proof, not permission to observe latent forests.

Positive master: for each fixed admitted finite target, finitely many legal I observations must force its permitted entire law against EVERY admitted finite rival of UNKNOWN size. Qualifying negative: ONE fixed strict finite target, and after EVERY finite full-legal-I prefix, an exact later-inequivalent strict FINITE rival.

This note continues the private serial chart at

    T = E(3/4) B(1/2,1/2,2/3) E(1/2),
    W = U K(theta) V,     theta = (a,x,y,g,r).

All five body variables are kept in the raw polynomial system. Within the inherited local branch, exact cap-four matching fixes them through the same Lambda. No higher body coefficients are free. No new graph-size bound, new actuator, replay of the body, negative-time population, or source built merely from positive matrix entries is admitted.

For a fixed serial architecture A and cap m, let F be the FULL raw physical residual, not a diagonal or selected-statistic surrogate. With L bigons and G ordinary factors, the inherited chart gives N=3L+G and degree at most (G+L)binom(m,2)+Lm. This input dimension grows when physical cells are added. See the predecessor packet and the original body-elimination proof pinned in SOURCE-PINS.json.

## 3. Method and classical providers

The external input is the polynomial-map bound (KS2) in Kurdyka, Spodzieja and Szlachcinska, *Metric Properties of Semialgebraic Mappings* [KSS16]. On a bounded neighborhood of a zero it implies

    dist(p,F^(-1)(0)) <= C ||F(p)||^(1/R),
    R = d(6d-3)^(N-1),    d >= max(2,deg F).

The 2019 correction [KSS19] concerns other general semialgebraic graph estimates. It must not be silently ignored or mixed into this raw-polynomial use. This turn re-read the polynomial formula and the complete correction. We do not apply this smaller exponent to an analytic Lambda graph.

The ordinary Nash curve selection statement is supplied by [Fernando25]: a closure point of a semialgebraic set is reachable by an analytic semialgebraic arc. We only use Taylor APPROXIMATIONS of such arcs, not a claim that an exact polynomial arc lies in every algebraic set.

The algebraic replacement uses real closed field quantifier elimination/model completeness. Marker [Marker15], Theorem 3.14 and Corollary 3.15, explicitly establishes R_alg as an elementary substructure of R. These are classical providers; the present composition is not claimed historically novel. Cohen and Mahboubi [CM12] provide a formal-computational precedent for exact ordered-field and real algebraic operations, not verification of our Python code or a Lean theorem.

## 4. Main equivalence

Let K be a finite algebraic number field with a fixed real embedding. Let

    F in K[x_1,...,x_N]^k,     h in K[x_1,...,x_N],
    Omega = (0,1)^N,
    p0 in K^N intersect boundary(Omega),     F(p0)=0,
    S = {p in Omega : F(p)=0 and h(p) != 0}.

Set d >= max(2,deg F) and R=d(6d-3)^(N-1). The following are equivalent.

(A) p0 belongs to the closure of S.

(B) There exist an integer q>=1, a finite real algebraic extension K' of K, and a polynomial vector p(t) in K'[t]^N of degree less than q such that:

* p(0)=p0;
* every p_i(t) and 1-p_i(t) has a positive first nonzero coefficient;
* r is the largest first-nonzero order among these 2N margin polynomials;
* every coefficient of F(p(t)) below t^q vanishes, in EVERY residual row;
* h(p(t)) has a first nonzero coefficient of finite order s;
* q > R max(r,s).

The clause concerning h can be omitted by setting h=1 when only strict exact existence, not distinction, is sought. That choice supplies NO inequivalence conclusion. At a boundary p0 at least one margin order is positive.

### Proof of (B) implies (A)

Positive leading margin coefficients give p(t) in Omega and delta(p(t)) >= c t^r for small t>0, where delta is distance to the complement of the open cube. Complete coefficient cancellation gives ||F(p(t))||=O(t^q). The closed nonempty zero set Z=F^(-1)(0) has a nearest point z(t) to p(t). By the external error bound,

    ||z(t)-p(t)|| <= C ||F(p(t))||^(1/R)
                  = O(t^(q/R)).

Since q/R>r, this is o(delta(p(t))). Thus z(t) is strict and tends to p0. Since h is polynomial, it is Lipschitz on a sufficiently small closed neighborhood of p0. Its nonzero leading coefficient yields |h(p(t))| >= c' t^s. Since q/R>s,

    |h(z(t))-h(p(t))| = O(t^(q/R)) = o(t^s).

Therefore h(z(t)) != 0 for all sufficiently small t. The same corrected tuple satisfies ALL residual equations. Hence z(t) lies in S and p0 is in its closure. The nearest-point selection need not be unique or continuous. QED.

### Proof of (A) implies (B)

Apply Nash curve selection to S at p0. There is an analytic arc z(t) with z(0)=p0 and z(t) in S for small t>0. Each margin approaching zero has a finite positive-leading order, and h(z(t)) has a finite nonzero order. Analyticity rules out infinite order unless the function vanishes identically, which the strict/nonzero hypotheses exclude. Let r be the largest margin order and s the h order.

Choose an integer q>R max(r,s), and let p_R(t) be the Taylor polynomial of z through degree q-1. Then p_R-z=O(t^q), so every F residual is O(t^q), and all margin and distinction leading coefficients/orders are preserved. This gives a jet with finitely many REAL coefficients.

Now replace those finitely many Taylor coefficients by variables. Require the constant terms to equal p0; require the coefficients of every F residual below q to vanish; require each margin's coefficients before its selected order to vanish and its selected coefficient to be positive; require the h coefficients before s to vanish and the coefficient at s to have its original nonzero sign. This is a FINITE system of polynomial equations and strict inequalities over K. The real Taylor coefficients satisfy it.

Because R_alg is elementary in R, with the algebraic parameters K held fixed, the same existential coefficient system has a solution in R_alg. These new coefficients may differ from the original arc derivatives, but preserve exactly the finite conditions just listed. They define the required jet p(t). Their finite list together with K generates a finite algebraic extension K'. QED.

### Corollary: one shared real algebraic generator suffices

A finite number-field extension in characteristic zero admits a primitive element. Thus all coefficients of F, h, p0 and p(t) can be expressed as rational polynomials in ONE fixed real algebraic alpha. A rational polynomial and a rational isolating interval identify its real embedding. This is a finite exact representation, not a floating-point approximation and not independent conjugate selection for different rows.

Alpha is a fixed coefficient encoding. It is NOT an extra physical source variable. If an implementation instead promotes alpha to a variable of its polynomial map, that is a different map and its dimension/error-bound justification must change.

## 5. Exact rational-only countercontrol

Take rational data

    F(x,y)=x^2-2y^2,     p0=(0,0),     h(x,y)=y.

For sufficiently small t>0, (sqrt(2)t,t) is a strict exact path with nonzero h. N=2, d=2 and R=18. Its order-19 jet satisfies the theorem: r=s=1, every residual coefficient vanishes, and 19>18.

Nevertheless NO rational polynomial jet based at (0,0) can satisfy the criterion. Let x(t)=a t^u+... and y(t)=b t^v+... with positive rational a,b. If u!=v, ord F=2min(u,v). If u=v, the coefficient a^2-2b^2 is nonzero because sqrt(2) is irrational, again giving ord F=2u. Consequently ord F<=2r, while the criterion requires q>18r and q<=ord F. Contradiction.

This is an abstract polynomial representation counterexample. It is NOT an admitted G4 source, a failure of the full I observation menu, or a master negative solution. It shows that a proposed general polynomial-jet search cannot claim completeness merely because it enumerates all rational coefficients.

## 6. Top-down applicability audit

The theorem is exact for the stated fixed algebraic chart, fixed boundary presentation and specified polynomial distinction. G4 still requires actual admissible architectures and full residual polynomials. The predecessor's local source-to-observation adapters must apply to those same sources. The data-field restriction is real: arbitrary transcendental target parameters do not automatically have this finite algebraic representation.

Completeness here means that the unbounded mathematical certificate format loses no local solution germ under the stated hypotheses. It does NOT mean that the bounded Python program decides every instance, gives a source-size bound, enumerates every G4 architecture, constructs suitable jets at every cap, or detects observation-only stopping.

## 7. Bottom-up implementation argument

The accompanying checker performs rational polynomial arithmetic and Sturm root counts to check a supplied squarefree root isolator. It represents coefficients as rational polynomials in that one root. Every composition, cancellation and sign uses that same embedding.

The implementation permits a reducible squarefree defining polynomial for convenience. It does not wrongly treat the resulting quotient as a field. Root-specific equality uses a gcd and root count; an element may vanish at the selected root without having zero remainder modulo the entire defining polynomial. No algebraic division is needed. Positive signs are certified by rational interval refinement after exact zero detection.

All residual rows are composed with the same parameter jets modulo t^q. The checker computes degree from the supplied residuals, computes R from that degree and the physical variable count, checks both lower and upper cube margins, and checks the nonzero h order separately. User-provided claims of source or master verification cannot set the corresponding output flags.

## 8. Synthesis and remaining G4 equation

The remaining physical equation is unchanged:

    U_m K_m(Lambda(U_4,V_4)) V_m - K_m(T) = 0.

For this local negative route the remaining task is to provide, at EVERY cap m and this SAME target, an actual admitted finite architecture and a full physical certificate satisfying q_m>R_m max(r_m,s_m), or to replace the h test with an independently justified entire-law inequivalence argument for those exact sources. The target cannot drift across caps.

The present theorem prevents loss of a genuine fixed-chart germ through a rational-only representation choice. It does not prove those germs exist. A direct fixed-chart real-closed-field decision procedure is also a classical option; the jet format is useful for auditable constructive expansions, not a stronger general decidability theorem.

## 9. Glossary

**Jet:** finite Taylor coefficient data. **Margin order:** first nonzero degree controlling approach to a forbidden boundary. **Distinction order:** first nonzero degree of a specified later difference. **Embedding:** the chosen real root that fixes all algebraic coefficient values. **Full residual:** every coordinate required by the authenticated finite source problem, not just whichever rows are convenient to fit.

## 10. Sources

[KSS16] Kurdyka, Spodzieja, Szlachcinska. Metric Properties of Semialgebraic Mappings. Discrete & Computational Geometry 55 (2016), 786-800. DOI 10.1007/s00454-016-9776-4. Polynomial-map (KS2); arXiv:1412.5088.

[KSS19] Same authors. Correction to: Metric Properties of Semialgebraic Mappings. Discrete & Computational Geometry 62 (2019), 990-991. DOI 10.1007/s00454-019-00128-4. Applicability audit; not silently substituted for (KS2).

[Fernando25] Jose F. Fernando. On a Nash curve selection lemma through finitely many points. Revista Matematica Iberoamericana 41(4) (2025), 1201-1252. DOI 10.4171/RMI/1554. Classical one-point curve-selection statement, not its stronger multipoint construction.

[Marker15] David Marker. Quantifier Elimination and Applications. Mathematical Logic lecture notes, Fall 2015. Theorem 3.14, Corollary 3.15, printed pp.14-15. https://homepages.math.uic.edu/~marker/math502-F15/qe.pdf

[CM12] Cyril Cohen and Assia Mahboubi. Formal proofs in real algebraic geometry: from ordered fields to quantifier elimination. arXiv:1201.3731. Formal algebra precedent, not verification of this implementation.

## 11. Process-integrity assessment

The fixed source, original quantifiers, counterpart ownership and latest routing guide were checked. The polynomial error formula, correction, curve-selection statement and elementary transfer were inspected in primary author/publisher sources. Search was targeted, not systematic or exhaustive. The arithmetic tests are contributor-written and contributor-executed. Independent review must check the finite coefficient system, preservation of every leading-order condition, h stability, the error-bound scope and the actual compiler-to-polynomial binding. No empirical risk-of-bias scale or invented numerical proof confidence is assigned.

## 12. Inference-robustness assessment

The implication fails if selected rather than full residual rows are certified, if q is merely equal to a required threshold, if h vanishes or has too high an order, if root conjugates vary across rows, if a source domain has omitted constraints, or if the claimed F is not the physical source map. The algebraic converse does not cover transcendental input data. Removing a checker resource limit does not create an all-cap source construction. A successful abstract fixture cannot establish G4. These limits are part of the proposition, not an impossibility claim about the master.

## 13. Zotero and note integration

Import references.bib. Relate KSS19 as a correction of KSS16. Link Marker15 to the algebraic-coefficient transfer, Fernando25 to the analytic-arc-to-finite-jet step, and CM12 only to exact algebra implementation precedent. Tag this research contribution hand-proof/pending-independent-review. Separate theorem applicability, arithmetic execution and source/observer binding in downstream notes. No Zotero library was modified.

## 14. Reproduction and integration

Run the two CLI examples and test script described in README.md. They invoke neither Lean nor Rust nor the native research runtime. The existing integration owner chooses whether and when to port or verify this candidate. See INTEGRATION-CONTRACT.md for the explicit gates required before a source-level result.
