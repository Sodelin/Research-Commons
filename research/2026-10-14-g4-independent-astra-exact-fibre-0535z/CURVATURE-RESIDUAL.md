# The curvature-corrected first nonlinear residual

Contributor/publisher: independent Astra G4 research chat, 14 October 2026. Hand algebraic elaboration of the inherited body-elimination and two-region identities. This is not a new source zero, sign guard, independent review or G4 completion. The original BCH term is reused, not claimed as novel.

## 1. Normalization must also transport the projection

Work in the inherited finite capped forest/graft algebra, m>=4. Write K(eta) for the effective five-parameter body, eta_0=(3/4,1/2,1/2,2/3,1/2), and T=K(eta_0). The pair-normalized before/body/after identity is

    W T^(-1) = exp(X) [K(eta) T^(-1)] exp(Y).

Here X=log(U E(q_U)^(-1)), Y=log(Ad_T(E(q_V)^(-1)V)), and eta=(q_U a,x,y,g,rq_V). These inverses/logarithms are mathematical coordinates, never physical source operations. The SAME target conjugates the entire trailing region. No repeated target replay is introduced.

Let pi(V) extract the five cap-four coordinate differences from an ENDPOINT difference V. Define

    D(v) = DK(eta_0)[v],          J = pi D,
    A(v) = D(v) T^(-1),          pi_hat(L) = pi(L T),
    P_end(V) = V - D J^(-1) pi(V),
    P_log(L) = L - A J^(-1) pi_hat(L).

The inherited five-column Jacobian J is invertible. The exact relation is

    P_log(L) = P_end(L T) T^(-1).                         (1)

Thus P_log^2=P_log, pi_hat P_log=0 and P_log A=0. Applying the endpoint projection unchanged to a right-normalized logarithmic vector is not generally correct. This is an implementation clarification, not an allegation that the inherited coordinate-qualified projection was wrong.

## 2. Explicit body curvature

Put M(eta)=K(eta)T^(-1), so M(eta_0)=1. The Hessian of log M at eta_0 is the symmetric bilinear map

    H(v,w) = D^2K(eta_0)[v,w] T^(-1)
             - (A(v)A(w)+A(w)A(v))/2.                  (2)

Proof: expand log(1+B)=B-B^2/2+O(B^3), with
B=A(delta_eta)+(D^2K[delta_eta,delta_eta]T^(-1))/2+O(||delta_eta||^3).
The quadratic coefficient is H(delta_eta,delta_eta)/2. QED.

Use Taylor coefficients WITHOUT factorials. Suppose X,Y and delta_eta begin at order k>=1 in a common small parameter. Then the coefficient at order 2k of the body logarithm Z=log M is

    Z_(2k) = A(v_(2k)) + H(v_k,v_k)/2.                 (3)

Higher intermediate body coefficients v_(k+1),...,v_(2k-1) cannot enter a quadratic term of order 2k. They are still fixed by their own lower equations and must not be discarded from the source coefficients X_(2k),Y_(2k) if those depend on them.

## 3. First nonlinear reduced equation

Assume the COMPLETE order-k equation in the chosen full cap holds, not merely its five cap-four projections. Put S_k=X_k+Y_k. Exact cap-four body elimination forces

    v_k = -J^(-1) pi_hat(S_k),      P_log(S_k)=0.        (4)

The second condition in (4) is the remaining FULL-cap order-k equation. It is an additional condition, not a consequence of calibrating cap four. At intermediate orders k<j<2k the analogous equations are linear, with the corresponding source coefficients retained.

Since all three logs start at k, triple commutators start at 3k>2k. The degree-2k BCH bracket is

    ([X_k,Z_k]+[X_k,Y_k]+[Z_k,Y_k])/2.

Only using the complete relation Z_k=-X_k-Y_k does this equal -[X_k,Y_k]/2. After the new body coefficient v_(2k) is spent on cap four, the entire reduced residual is

    R_(2k) = P_log( X_(2k) + Y_(2k)
                    - [X_k,Y_k]/2 + H(v_k,v_k)/2 ).    (5)

Specifically, v_(2k) equals -J^(-1)pi_hat of the parenthesized vector. Equations (2)-(5) contain all forced nonlinear body feedback; it is not a free adjustment. For the inherited coherent rare scaling k=3, this gives the explicit sixth-order equation

    R_6 = P_log( X_6 + Y_6 - [X_3,Y_3]/2
                 + H(v_3,v_3)/2 ).                    (6)

This is the inherited X6+Z6+Y6-[X3,Y3]/2 with Z6 expanded and the physical five-column projection consistently normalized. Internal chronology and source-direct sixth coefficients still belong to X6 and Y6. Formula (6) does not assign them arbitrary free values.

If only cap-four cubic equality is available, the complete cubic relation used above is not known; retain the unsimplified BCH expression. If another actual scaling starts before order three, use its true leading k, not the k=3 specialization.

## 4. What an actual equality guard would need

A covector ell annihilating the body tangent A kills the last linear body correction, but need not annihilate H(v_k,v_k). Its first nonlinear test is therefore

    ell(X_(2k)+Y_(2k)) - ell([X_k,Y_k])/2
      + ell(H(v_k,v_k))/2.

A sign on just the first term, or on the ordinary chronological square before body retuning, is not a sign on this complete expression. No fixed-target evaluation or universal sign of (5) is established here. The inherited ordinary covector with a nonzero body derivative cannot be used unchanged.

Together with MARGIN-LIFT.md, this gives two concrete duties for a proposed physical jet: compute its COMPLETE residual with (5), then compare its surviving order with the positivity-margin exponent. If exact strict zeros accumulate in one fixed semialgebraic architecture, Nash curve selection supplies an analytic physical arc. Thus an obstruction covering EVERY possible such arc would exclude that local accumulation. Excluding one rare scaling or one leading-placement pattern does not cover every arc, nor arbitrary rival architectures.

## 5. Verification scope and inherited pins

verify_formal_identities.py checks the noncommutative algebra and a rational projection-normalization countercontrol. It does not evaluate actual source X6/Y6, solve the physical equation, compute a source Hessian, prove a sign, or run Lean/Rust. Its scalar margin controls are separate toy examples, not G4 sources. Execution results, if present, are recorded separately.

Inherited all-order body elimination:
research/2026-10-08-codex-g3-g4-full-shot-1253z/g4-fixed-target/attempt-7/FIXED-TARGET-ALL-ORDER-BODY-ELIMINATION.md
blob 135e4c7b0fdf4bcf44adbf16cbcf1b4ea13b2095.

Inherited two-region identity:
research/2026-10-08-codex-g3-g4-full-shot-1253z/g4-fixed-target/attempt-7/TWO-REGION-EXACT-CHRONOLOGY-ADDENDUM.md
blob a1954c26b82cfa2bf7b7815bf99a1118cb506427.

Current post-retuning review:
research/2026-10-13-codex-g4-renewed/critical-review/ROOT-POST-RETUNING-DIAGNOSTIC-REVIEW-0501Z.md
blob 45f84b7d1dd8f42b615b8bb36dbb857a06489e3b.

Self-audit: check the sign and order of the cross-region commutator, use right multiplication by T in pi_hat, distinguish a log Hessian from an endpoint Hessian, require complete leading matching, and retain the source meaning of all region coefficients. The status is hand derivation with limited exact algebra controls, pending independent source review.
