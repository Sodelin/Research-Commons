# Reference centering removes the additive source-mismatch floor

Author: dot (OpenAI-assisted research), 25 October 2026.
Status: scoped coordinator HAND ACCEPT after manual review of the inherited jets, uniform calibration argument and exact reference-shifted receiver. No independent primitive/source-engine rerun, Lean verification, original-master closure or historical novelty is claimed.

Retain the original paired equal-arm private word with arbitrary finite count, arbitrary strict coins, relative scales and chronological placements, one physical tuple and original IDs. Assume K_COMMON=E(c), b2_I(K)=c^(3/4), c=2^(-1/m), and complete forest commutation [K_I,S(t)]=0 through at least cap12 for the existing one-cell reference S(t). Set H=-log c and h=-log t, with one fixed sufficiently small H>0 and 0<h<H/4. The nominal ordinary clock is 3H/4 and sum ell_i=H/4. No new observation, physical inverse, fixed count or coin margin is imposed.

This adapter removes the additive source mismatch left by the direct absolute-value estimate. It does not provide an upper action estimate or AG-Pair.

## 1. Source function and linear calibration

Write Psi=Psi7 and retain J=56 sigma+55 rho. Define exactly

    P=198 Psi-21 sigma,
    D=J-P=77 sigma+55 rho-198 Psi.

The completed divided source jets give D=O(u*s), uniformly at every strict coin, including coins tending to either endpoint. Near fairness, D/(v) has weighted degree at least six when u and beta both have weight one. This follows from cancellation of all displayed beta^2*u^3, beta*u^4 and u^5 terms; the remaining terms have the factors beta^2*u^4, beta*u^5, or u^6. The existing rational source functions supply analyticity after the endpoint factor is divided out.

For any one of these scalar source functions X, let x(u)=X(u,0), f(u)=F(u,0), e(u)=ell(u,0), and evaluate at u*=log(2 exp(h)-1). Define

    a_X=(e*x'-x*e')/(e*f'-f*e'),
    b_X=(f*x'-f'*x)/(e*f'-f*e'),
    Cal_h(X)=X-a_X F+b_X ell.

The denominator is the SAME positive denominator in the completed J calibration. Calibration is exactly linear in X. In particular

    Cal(J)=Phi_J, Cal(P)=Phi_P, Cal(D)=Phi_D,
    Phi_J=Phi_P+Phi_D.

Since d(u)=O(u^6), while f=u^3/120+O(u^4), e=u/2+O(u^2), the coefficients satisfy

    a_D=O(h^3), b_D=O(h^5).

Their signs are not needed. Exact calibration ensures Phi_D(u*,0)=0 and its fair u derivative is zero. These are exact identities, not merely leading-jet cancellations.

## 2. Uniform relative estimate

There is a fixed C such that, on the original small-source domain u<=H and h<=H/4,

    |Phi_D(C)| <= C H Phi_J(C).                    (1)

Here H is selected once small enough; it is not sent to zero as a function of h. All constants are chosen on an initial fixed compact domain.

Proof by the same exhaustive split used in REFERENCE-CALIBRATED-SOURCE-ACTION:

(a) If F<=0, the completed positive-cost and calibration bounds imply

    Phi_J >= c[s+h^2|F|+h^4 ell].

The three terms in |D-a_D F+b_D ell| are at most C H s, C h*h^2|F|, and C h*h^4 ell. Since h<=H, (1) follows without a coin margin.

(b) If F>0, the completed source inequality gives beta<=C u, hence s is comparable to v u^5, ell comparable to v u, and |F|<=C v u^3. For u<=delta*h the existing lower bound is Phi_J>=c h^4 ell. Divide the three upper bounds by this lower bound: their ratios are at most C u^5/h^4, C u^2/h, and C h. Each is O(h), hence O(H).

For u>=K*h the existing lower bound is Phi_J>=c v u^5. The corresponding ratios are at most C u, C h^3/u^2, and C h^5/u^4. These are O(H). The constants delta,K are fixed, as in the completed proof.

(c) On the remaining compact scaled domain u=h*x, beta=h*y, the removable analytic quotient Phi_D/h^6 exists. Away from the unique reference point x=x*(h), y=0, the completed lower bound Phi_J>=c h^5 makes the ratio O(h).

Near that point, exact value-and-derivative calibration and bounded analytic derivatives give

    |Phi_D| <= C h^6[(x-x*(h))^2+y].

To see this without an unjustified two-variable factorization, first restrict to y=0 and use the integral second-derivative remainder in x; then integrate the bounded y derivative from zero to y>=0. The completed positive action proof supplies

    Phi_J >= c h^5[(x-x*(h))^2+y].

This proves (1) also at the reference zero, where both sides vanish.

Choose fixed H so CH<=1/2. It follows that

    (1-CH) Phi_J <= Phi_P <= (1+CH) Phi_J.          (2)

Consequently Phi_P is nonnegative, has exactly the same strict zero, and controls the same variance. Summing preserves (2) for every finite word, independent of its count and scale ratios. The calibrated P action is therefore a sufficient replacement for the J action. There is NO additive Hh^5 residual. This is the meaningful difference from simply bounding sum |D| by sum u*s.

## 3. The remaining exact full-commutator receiver

The replacement does not by itself supply a small upper bound. It does permit the exact remaining problem to be written using the existing matched rate15 receiver.

Let p be the full Psi7 reference-shifted coordinate, e the normalized 7-to-4 coordinate, and Pi the actual b4/b7 prefix ratio with nominal continuation. Set

    omega_i=1/Pi_i+, beta7=d4/d2, T=3H/4.

The old exact formulas give p'=15(p-p_h), e'=15e-15D_ref/kappa, and source injections Psi/d2 and (-kappa F+sigma)/(kappa*d2), respectively. D_ref is the reference matrix entry called D in the old proofs; it is NOT the source mismatch D of Sections 1-2. Both coordinates start and end at zero. Explicitly, the reference shifts are retained in the EXACT source updates:

    p+ = beta7*p- +Psi/d2+p_h*(1-beta7),
    e+ = beta7*e- +(-kappa*F+sigma)/(kappa*d2)
                         +(D_ref/kappa)*(1-beta7).

Thus Z=198p-21kappa e has Z'=15(Z-C_ref) and

    Z+ = beta7*Z- +(P+35F)/d2+C_ref*(1-beta7),
    C_ref=198p_h-21D_ref.

In particular its jump is NOT just the displayed source numerator. With I=integral Pi^(-1), exact integrating-factor calculus gives

    1-Pi_T^(-1)=15I-sum omega_i*(1-beta7_i).

This keeps the reference-jump contribution that is required below.

Integrate the exact combination 198p-21kappa e with its own Pi integrating factor. Its source numerator is P+35F, because 21kappa=35. The reference constant is 198p_h-21D_ref. Therefore

    sum omega_i (P_i+35F_i)/d2_i
       =(198p_h-21D_ref)*(1-Pi_T^(-1)).            (3)

This uses the complete full Psi7 endpoint condition, not only the old selected quotient. Every source denominator and actual diagonal transport is retained.

Subtract the calibrated terms from (3):

    sum omega_i Phi_P(C_i)/d2_i
       =(198p_h-21D_ref)*(1-Pi_T^(-1))
        -(35+a_P)*sum omega_i F_i/d2_i
        +b_P*sum omega_i ell_i/d2_i.               (4)

The positive weights omega_i/d2_i are uniformly above and below zero at fixed H, so the left side is comparable to the unweighted nonnegative action. Equation (4) is exact. It is not a new legal readout or an unweighted cocycle.

## 4. What remains after the attempted bound

The exact residual is now the right side of (4): a weighted F moment, a weighted logarithmic budget, and the actual endpoint diagonal ratio Pi_T. The paired condition supplies sum ell_i=H/4, NOT sum omega_i ell_i/d2_i. Nor does commutation supply Pi_T as a prescribed fractional reference power. Replacing either unknown expression by its reference value would be the missing step, not a valid simplification.

The completed source-cost estimate gives sum s=O(Hh^4) and sum r<=C Hh^2. Bounding the F term in (4) separately thus produces only O(Hh^2), losing even the finer cancellations already implicit in the nonnegative action. The cap12 energy and sharp balance must control the COMBINATION, not its summands individually. Existing square-receiver and bounded-Psi pointwise exclusions remain in force; (1)-(4) do not circumvent them by assuming a forbidden receiver.

The source-centering argument removes a concrete additive error floor in one possible adapter. It does not supply Action=o(h^6), an integer phase, a witness selector, or a counterexample to AG-Pair. The scoped manual review checked (1)'s uniform remainder argument against the inherited source jets and (3)'s signs, denominators and reference jumps against the exact e and p updates. This is not a fresh transitive re-proof of the source-engine suppliers or a historical-priority claim.

## Sources

All mathematical suppliers are at the immutable commit
https://github.com/Sodelin/Research-Commons/tree/d3c270c14c13c0d31436bb5a2b0fb7e82a23655e/research/2026-10-24-g3-asymptotic-root-grid

Specifically: REFERENCE-CALIBRATED-SOURCE-ACTION.md Sections 3-7; POSITIVE-TRANSVERSE-SOURCE-COST.md Sections 3-6; MATCHED-FULL-BAND-LINEAR-ABSORPTION.md Sections 3-4; COMPENSATED-SOURCE-JUMPS.md Sections 3-4. The fixed-domain, source-faithful, arbitrary-coin assumptions are inherited unchanged. All inherited completed suppliers retain their original scopes and attribution.
