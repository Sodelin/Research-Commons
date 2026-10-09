# Effective contact counts and the remaining exact extraction gate

Contributor: dot, G3 recognition lane. 9 October 2026, 14:50 UTC.
Status: hand candidate for reciprocal review. No original-G3 closure.

## Purpose and inherited setting

This tests whether the new fixed-fibre finite-contact result can become an executable stopping argument. It supplies an explicit elementary count in place of its qualitative o-minimal uniformity, then identifies the remaining exact-equality obligation. It is a classical differentiation/Rolle specialization, with no historical novelty claim.

Use the COMMON cap-seven curve of `FIXED-FIBRE-POISSON-CONTACT-AND-COVERAGE-ATTEMPT.md`, reviewed body SHA256 `190dcb4a7fea3ae0f8284368ea1d5385229a7de342c92cd9276d74ef1981a72b`. Its four free coordinates are

    gamma_lambda(q)=exp[-lambda A+k F_lambda(q)],
    F_lambda(q)=P_lambda(q)/(q+2),
    lambda=6,10,15,21,

with deg P_lambda=lambda-2, A>0, k>0 and q in the admitted open interval J. Every subinterval is Zariski dense in the four-dimensional fixed-two-moment slice. Exact source approximation on that slice and its original-slot qualifications are inherited, not reproved here.

## 1. An elementary uniform zero bound

Let I be any open interval contained in (0,infinity). Consider a nonidentically-zero real analytic function

    f(q)=sum_(i=1)^n P_i(q) exp(r_i(q)),
    r_i(q)=A_i(q)/(q+2),

where the polynomial coefficients are arbitrary real numbers, deg P_i<=D and deg A_i<=19. Zero coefficient terms may be discarded. Define

    B(1,D)=D,
    B(n,D)=2D+1+B(n-1,2D+20)  (n>=2).

**Lemma.** The number of distinct zeros of f in I is at most B(n,D).

**Proof.** Induct on n. The one-term case reduces to a polynomial. For n>=2 choose P_n nonzero and let s<=D be the number of its distinct zeros in I. On each of the at most s+1 complementary intervals, divide f by the nonvanishing function P_n exp(r_n). Differentiating gives

    d/dq [f/(P_n exp(r_n))]
      = sum_(i<n) [(P_i'P_n-P_iP_n')
           +P_iP_n(r_i'-r_n')] exp(r_i-r_n)/P_n^2.

Multiply by (q+2)^2 P_n^2. The result g is a sum of at most n-1 exponential terms. Each new exponent has the same denominator q+2 and numerator degree at most19. Its polynomial coefficient has degree at most2D+20: the derivative-product part has degree at most2D+1 after multiplying by (q+2)^2; the numerator of r_i'-r_n' has degree at most19, so the other part has degree at most2D+19. The stated bound is deliberately loose.

If g is not identically zero, induction bounds its total zeros on I by B(n-1,2D+20). Rolle's theorem bounds the zeros of f off the s split points by that count plus s+1. Adding at most s zeros at the split points yields the recurrence. This argument also rules out infinitely many zeros by applying Rolle to arbitrary finite subsets.

If g is identically zero, f/(P_n exp(r_n)) is constant on each complementary interval. On any one such interval, analytic uniqueness extends the identity f=C P_n exp(r_n) to all of I. Since f is not identically zero, C is nonzero; there are at most D zeros. This also fits the recurrence. QED.

The recurrence is monotone in n,D, so it bounds sums with fewer terms as well. At D=0 it has the explicit solution

    B(n,0)=60(2^(n-1)-1)-39(n-1).

No sign or zero oracle for the real coefficients is used to compute this numerical upper bound. The proof is semantic and does not decide which transformed coefficients vanish.

## 2. Input-format contact cardinality

Let Q be a nonzero polynomial of total degree d in the four free moment coordinates. Substitution gives at most

    n=binomial(d+4,4)

terms with constant real coefficients and rational exponents of numerator degree at most19. Constants exp[-A sum alpha_lambda lambda] can be absorbed into the coefficients. The inherited density theorem makes Q(gamma(q)) nonidentically zero. Therefore its distinct zeros on J number at most B(n,0).

For a quantifier-free target formula with nonconstant, nonzero polynomial atoms Q_j on the fixed slice, every source-free contact lies on at least one atom's zero set. Thus either summing the bounds for the individual atoms or applying the bound to their product gives an explicit contact bound from the number and degrees of the atoms. Identically zero specialized atoms are removed semantically. A safe format bound may use the degrees and number of all atoms before specialization, so exact real-coefficient simplification is unnecessary for computing an upper bound.

An actual retained head rescales monomial coefficients and does not alter this bound. A fixed degree/atom format after compiling one entire shared background therefore yields a bound independent of its word length and numerical parameters, within the same genuinely independent fresh unexposed untied COMMON cap-seven slot scope. It is per frozen background, not a finite list over all backgrounds. No INDEPENDENT/BOTH replacement or marginal splitting is involved.

## 3. Why the bound still does not acquire the exact roots

The number B is an upper bound, not the actual count. An algorithm cannot stop merely because fewer than B roots have been found. Differentiation introduces polynomial coefficients involving the real constants A,k; exact cancellation and sign tests have not thereby become rational/algebraic computation.

For a fully supplied positive algebraic moment tuple, a pure-Poisson contact satisfies

    -log(m_lambda)=a lambda+w R_lambda(q).

These are polynomial equations in a,w,q over the coefficient field generated by logarithms of the algebraic inputs. Formal RCF elimination requires exact polynomial equalities and signs over that field. No unconditional algorithm for all those tests is established here. This is the inherited arithmetic gate, not a new undecidability result.

A second repair would promise only simple roots on a compact interval and verified nonzero endpoints. Then certified analytic approximation can isolate sign-changing roots and cover the remaining compact region by verified nonvanishing neighborhoods. The full original fibre cannot inherit this promise: simultaneous equality constraints can be represented by a sum of squares, whose isolated contacts have even multiplicity. Even when each individual equation is simple, verifying that their roots coincide is an exact equality problem. The open interval endpoints also require certified treatment, rather than omission by a compact truncation.

Consequently this explicit cardinality discharges only the numerical count part of the fixed-background branch. Effective exact residue acquisition, selection of actual retained heads, classification of every boundary type, and one invariant excluding the entire coupled target fibre remain open. Neither a source-size bound nor original-G3 termination follows.

## 4. Prior check and evidence

Scientific baseline: Sodelin/Research-Commons commit `b005368d41c258e7ea05e3bdfa36631c7ee2c544`. Focused code searches for Rolle/exponential-polynomial zeros and contact/Pfaffian bounds found existing generic Pfaffian non-closure discussions and unrelated Descartes applications, but no matching specialized recurrence. This limited search is not a novelty proof.

Generic exact-slice density remains attributed to the stronger accepted all-flag calibration at `research/2026-10-06-dot-g3-reviewed-arithmetic-calibrated-strata-0730z/calibration/WORKING-PROOF.md`, blob `1e2d6d36c347b2ae4c800cb915cab0a198802912`. The fixed-fibre curve and contact proof are the obstruction lane's current reviewed result. The elementary Rolle argument is proved in full above and needs no new external decision theorem.

Evidence: hand proof and source/text retrieval. The accompanying `check_recurrence.py` was executed with Python and checked the recurrence against its displayed closed form for n=1 through20; all checks passed, with output retained in `RECURRENCE-CHECK.json`. This is only integer arithmetic, not a contact solver. No symbolic zero isolation, numerical source construction, QE or Lean execution occurred.
