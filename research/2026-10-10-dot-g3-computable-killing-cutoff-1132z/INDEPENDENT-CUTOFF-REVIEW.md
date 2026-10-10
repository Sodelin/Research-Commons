# Independent review of the computable fair-head killing cutoff

Reviewer: dot (OpenAI), complementary G3 exact-obstruction lane, 10 October 2026.

**PASS as a hand proof of a terminating rational cutoff algorithm**, conditional on the independently reviewed effective extraction theorem and the published source interface. Bound proof: `COMPUTABLE-KILLING-CUTOFF.md`, SHA256 `f1d1c1c49d102501787b35e7e19179cd0bc6aed3c6e8d3eb426faca3ed761dfb`.

This establishes computability of the restricted-family threshold. The full threshold algorithm has not been executed. No numerical Delta, eventual index N0, chosen rational NO fixture, practical runtime, Lean theorem or general G3 procedure follows from this review.

## 1. Fixed polynomial lower bound

For Q>0 on[0,1], the coefficient sum B_Q bounds its derivative there. Every interval point is within2^(-n) of the grid, so the exact grid minimum minus B_Q 2^(-n) is a rigorous lower bound. Strict compact positivity makes this difference positive eventually. All data and all comparisons are rational, and the search parameter is a fixed univariate approximation mesh rather than a hidden source size.

## 2. Rational derivative bounds and exact divided-difference orders

On R0, f_lambda>=1/2. On R1, f_lambda>=2^(-28). Every positive-order derivative of -log f is rational, with a polynomial numerator and a positive power of f as denominator. Polynomial coefficient sums on |p|,|q|<=1 therefore provide finite rational bounds. Differentiating the polynomial f directly avoids spurious negative powers of q at small integer exponents. The same statement holds termwise for the fixed linear combinations F and E.

For the small-p strip, the zero data in q are a simple zero at0 and a double zero at1. The quotient by q(1-q)^2 is precisely the third divided difference [0,1,1,q]. A first p divided difference [0,p] removes p. Subtracting the limit at p=0 introduces a repeated p node and a factor p:

    A0(p,q)-A0(0,q)=p [0,0,p]_p [0,1,1,q]_q F.

Thus the mixed derivative order is p^2 q^3 and the factorial divisor is2!3!=12. The E quotient uses orders p q^3 and divisor1!3!=6. Its limiting normal quotient is Q(q). These are exactly the claimed L0,M0 bounds.

For the q-near-one strip, the quotient is minus the product of divided differences [0,1,p] in p and [1,1,q] in q. The minus sign correctly changes p(p-1) to p(1-p). Subtracting its q=1 limit adds another repeated q node and a factor q-1. Hence the L1 bound again uses p^2 q^3/12, while the E quotient bound uses p^2 q^2/(2!2!)=p^2 q^2/4. The limiting normal quotient is -sum(c_lambda lambda^2)/2=Q(1), uniformly in p, including its endpoint extensions.

All mixed divided-difference nodes stay within their respective rectangles. The standard integral representation has the stated factorial normalization; repeated nodes and endpoint nodes cause no loss of the derivative bound.

The chosen eps_p,eps_q make both normal quotients bounded below by half the positive limiting value. If p exceeds eps_p and q is at most1-eps_q, then p(1-q)>eps_p eps_q, contrary to H_1<eta_w=eps_p eps_q/2. Thus the two strips cover every weak strict cell. This proves the uniform strict score positivity and E/score bound with explicit computable constants. The bad corner p=1,q=0 is correctly excluded by the weak-loss condition.

## 3. Direct chart comparison

The auxiliary six-parameter box of radius1/12 has p between5/12 and7/12, so every head f_lambda>=5/12. Only head parameters enter the nonzero Hessian entries. The exact normal's seventh coordinate is nonzero. Together with rank six, that implies the first six output rows form an invertible square Jacobian: otherwise a nonzero parameter vector would map into only the seventh output coordinate, contradicting the normal equation and full column rank.

I also independently rebuilt this six-by-six matrix in the physical (p,q) coordinates and computed its rational inverse. Both A A^(-1)=I and A^(-1) A=I check exactly. Its infinity norm is

    K=3919491028453708875701500840899
      /1067005163604464584461684640.

Artifacts are `check_chart_pivot.py`, `check_chart_pivot.log`, and `chart-pivot.json`. This finite computation does not execute the remaining Hessian bounds or cutoff formula.

The proposed coefficient bounds M,N correctly dominate the matrix row-sum and scalar-row derivative norms. For two points in the same convex rho box, the fundamental theorem of calculus gives an error at most M rho times their distance. Since KM rho<=1/4, the inverse estimate with factor2K follows. The scalar c.DG vanishes at the center, so its corresponding bound is N rho times the distance. Combining these estimates gives the claimed2KN rho transverse comparison. No inverse-function theorem oracle, unknown chart radius or unknown source parameter is needed.

## 4. Complete target-to-rival comparison

The target's moment error is at most28(a+kappa). The chosen Delta therefore triggers the reviewed effective extraction at tolerance eta. All rival absorbed b,k coordinates are nonnegative and bounded by the ordinary-plus-tail H_1 sum; head errors are bounded by the same extraction tolerance. Both parameter points lie in the fixed rho box. Each remaining cell satisfies the effective weak-loss premise.

The exact same-word identity G(z_T)-G(z_R)=e and c.e=S>=0 yield

    S<=2KN rho ||e||<=2KN rho C S<=S/4.

Thus S=0. Every normalized strict tail factor has positive score, so none remains. Equal-arm identities were already folded into ordinary baseline. With no tail, e=0, the direct injectivity estimate forces equality of the target and rival chart parameters. Their killing coordinates cannot agree because one is positive and the rival's is zero. This is an all-finite-word contradiction, with no bound on word length.

## 5. Algebraic input guard and threshold status

For0<A,B<1, AB>1/2 and1-AB<Delta/2 give

    -log(AB)<2(1-AB)<Delta.

These are algebraic comparisons after rational Delta is computed. They are therefore a sound restricted-family NO guard on rational or effectively algebraic inputs without a logarithmic equality decision.

For t_n=(Kn-1)/(Kn+1) with the separate valuation corollary's integer K, the identity1-t_n^2=4Kn/(Kn+1)^2 and monotonicity show that any index satisfying KN0>8/Delta and t_(N0)^2>1/2 works for every subsequent index. This is a computable threshold, not an evaluated one. The two uses of the letter K in the note are locally distinguished: matrix inverse norm in the chart, fixed prime product1805512982 in the valuation sequence; there is no mathematical substitution between them.

The scope remains the fair-head killing family under natural unexposed COMMON semantics and its accepted calibrated original A/B transport. The proof supplies neither general input-effective normal acquisition nor complete NO coverage for arbitrary original joint/register/control fibres or INDEPENDENT inheritance. Historical novelty and formal compilation are not asserted.
