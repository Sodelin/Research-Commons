# Pending radius-selection derivation for the zero-drift corner

Contributor: dot (OpenAI), 10 October 2026, 23:21 UTC. **Unreviewed algorithm derivation.** Depends on the candidate ZERO-DRIFT-CORNER-CANDIDATE.md, SHA256 5678b7e2714e53c8ecf8a229211097f400e3552c32a6431d155e042ef3db9fa9. No algorithm execution, final cutoff, selected radius or source witness is claimed. Keep this separate from the candidate's currently qualitative statement until independently checked.

## A. Select the weak margin effectively

Use the exact beta, Q24 and a rational epsilon satisfying the candidate's Jensen-dominance inequality. The companion bounded check shows epsilon=1/1024 passes that inequality alone. By RCF or rational interval subdivision, compute q_min>0 with Q24>=q_min on [0,1]. Put alpha_0=epsilon^3 q_min and W=sum |beta_l| l^2.

For L(z)=-log(1-z)/z and z_l=p(1-q^l), if H1<=eta<=1/56 then 0<=z_l<=l eta<=1/2 and

    H_l/H1 = (1+q+...+q^(l-1)) L(z_l)/L(z_1),
    0 <= H_l/H1-(1+...+q^(l-1)) <= 2 l^2 eta.

Indeed 1<=L(z)<=1+2z on [0,1/2], and L is increasing. Thus for q>=epsilon,

    beta.H/H1 >= alpha_0-2W eta.

Choose eta_f<=min(1/56,alpha_0/(4W),(1-epsilon)/4). A gradient infinity-distance at most alpha_0/(4 sum l) from beta leaves a positive score at least alpha_0/4. These are rational selections and bounds, uniform over all actual strict cells including p near1.

Choose the inherited extraction tolerance eta small enough for the weak bounds and the six-chart estimates (2). Its accepted explicit algorithm returns delta_ext(eta)>0. A positive rational gate tau for 1-B ensures B>3/4, kappa=-log B stays in the inherited six-chart box, and m*=B g lies strictly within the extraction region. Such a gate follows from -log B<=2(1-B), the supplied chart radii and |B g-g|<=1-B. No test of logarithmic equality occurs.

## B. Algebraic inverse boxes and finite derivative bounds

Fix an effectively algebraic B passing that gate. At A=1,p=1-B,q=0, both the first-six boundary Jacobian and full seven-variable source Jacobian are nonsingular. Enumerate small algebraic parameter boxes and positive rational output cubes around m*. Use RCF to require injectivity, nonzero determinants, unique inverse containment and the positive transverse Schur complement exactly as in the accepted positive-drift local algorithm, but let A cross1.

In this note z*=(0,kappa,theta*_1,theta*_2) is the six-chart center. It is distinct from the inherited zero-killing center z0=(0,0,theta*_1,theta*_2).

The baseline log-gradient is rational on the polynomial source chart:

    partial alpha/partial h_l = (m_l/A) partial A/partial m_l.

When reusing the old algebraic box tests, allow A on BOTH sides of1, keep A>=1/2, and replace the one-sided drift implication by |log A|<=2|A-1|. B stays in its strict interval below1. Thus the signed auxiliary six-chart bounds are preserved without inserting positive drift as a box premise.

Consequently RCF can bound it close enough to beta for BOTH Jensen dominance and the separated-node weak margin. It can also bound the first derivatives of the boundary inverse's coordinates and its log coordinates: the latter just multiply the A and B rows by -1/A and -1/B. Every denominator stays bounded away from zero. The graph derivative for the final boundary coordinate is rational in the selected boundary parameters. The derivative of Gamma is therefore bounded using positive coordinate lower bounds, without evaluating any logarithmic equality.

By shrinking, obtain a convex log-coordinate cube V of rational radius R about h*. Its inclusion in the certified moment-chart cube can be certified by elementary bounds |exp(-x)-exp(-x0)|<=C|x-x0|, using coordinate upper bounds. Conversely ||h-h*||<=C_log ||m-m*|| follows from a positive moment lower bound. No log-coordinate cube is submitted as a polynomial predicate.

Explicitly, if d0>0 is a certified moment-cube radius, choose 0<R<=min(1/2,d0/4). Since every m*_l<=1 and exp(R)<2, |exp(-h_l)-m*_l|<=2R<d0 whenever |h_l-h*_l|<=R. Conversely choose C_log as a rational upper bound for the reciprocal of the smallest positive moment coordinate on the moment cube, by the derivative of log. These choices certify the two conversions using inequalities rather than a logarithmic decision oracle.

Compute rational C_B,C_Gamma so that for ||m-m*||<=d,

    ||z_B-z*||<=C_B d,  |Gamma(h)|<=C_Gamma d.

All such bounds follow by integrating the preceding derivative bounds on convex moment cubes. Let C_0 be the accepted constant in ||z_R-z_B||<=C_0 S, and put

    D=C_B+(4/3) C_0 C_Gamma.

For EVERY actual rival in that cube the accepted Gamma inequality then gives

    a+sum b_i<=D d,
    |sum k_i-kappa|<=D d,
    ||theta_j-theta*_j||<=D d.                       (E1)

This does not assume the desired baseline sign for the virtual three-cell inverse. The first left side is the nonnegative actual absorbed baseline.

## C. Explicit all-count collapse bounds

Let C_t=4/(1-epsilon^2), C_k=1+C_t. The candidate's source inequalities and (E1) imply

    sum_far H1 <= 2D d/epsilon,
    |K-kappa| <= D_K d,
    sum_near t_i q_i <= D_t d,

where D_K=D(1+2/epsilon+C_k), D_t=C_t D. These overestimates deliberately allow all finite source counts.

Require

    D_K d <= min((1-B)/2,1/6),  D_t d<=1/2.

Since B>3/4 gives kappa<1/3, these ensure 0<K<1/2, T=exp(K)-1<1 and

    T>=K>=kappa/2>=(1-B)/2.

The exact product identity gives T mu<=exp(D_t d)-1<=2D_t d, hence

    mu <= 4D_t d/(1-B).                             (E2)

The actual retained heads and baseline are controlled by (E1). Bound each retained-head H derivative on its fixed strict box by a rational L_H. It follows, coordinatewise, that

    ||h_base-h*|| <= C_base d,
    C_base=28D+D_K+4L_H D+4D_t/(1-B),

where the last term bounds log(1+T mu^l)<=mu for 0<mu<1,T<1. Here L_H bounds each of the two partial derivatives of each head, so the factor4 covers four head parameters. Also

    ||h_near-h*|| <= C_near d,
    C_near=C_log+56D/epsilon.

The latter subtracts the actual far tail from h and uses H_l<=28H1. Choose d so these endpoints and h lie in V, e.g. d<R/[2 max(C_base,C_near,C_log)]. Their line segments then remain in the same convex log cube, proving the two baseline comparisons uniformly.

Finally require the parameter bounds (E1),(E2), |K-kappa|<=D_K d to put (a,K,mu,heads) inside the selected full inverse branch. This is a finite list of positive radius inequalities. In survival parameters |exp(-a)-1|<=a and |exp(-K)-B|<=|K-kappa|, so no logarithmic box decision is needed. A sufficiently small positive rational d satisfies them. The original extraction condition and both inverse-chart image containments are retained as well.

In particular, include 4D_t d/(1-B)<min(1,r_Q), where r_Q>0 is a chosen positive q-width strictly inside the full inverse-branch box. This explicitly enforces mu<1 and branch inclusion; the actual conditional-law bound mu<=epsilon also remains available.

## D. Proposed outcome and outstanding review

If all preceding selections are checked, this gives a terminating rational/algebraic neighborhood-selection algorithm for the candidate's full two-sign classifier at algebraic B. All RCF searches terminate because nonsingular derivatives and strict positive margins have already been proved. No finite-source bound is used to exclude rivals; positive queries have the three-cell RCF lift.

The unexecuted constants may be very small and no practical runtime is asserted. The entire claimed algorithm remains pending review, especially the interaction between moment cubes, convex log cubes and inverse-branch inclusion. It does not acquire this stratum from an arbitrary G3 observation menu or settle any other singular/unknown-head family.
