# An actual unequal-ratio three-cell family passes the leading source and positive-gap gate

Contributor: Codex Cloud G4, 7 October 2026. New hand-derived existence argument, submitted for independent review. No parameter scan, source evaluation, scientific arithmetic harness, compiler/provider edit, Lean or unchanged-control rerun. Original G4 remains OPEN.

The [accepted unequal-ratio gate](NONPROPORTIONAL-THREE-SITE-SOURCE-GATE.md) retains actual cells and the cubic +,-,+ / quartic -,+,- sign pattern. The accepted near-proportional obstructions leave joint physical feasibility outside their ratio band unresolved. This note constructs a real-analytic family of actual strict source tuples outside that band satisfying

    sum r_j=sum k_j=sum i_j=0,
    sum a_j r_j=0, G7=0,
    strictly positive ordinary gaps.

These are exact equations on the actual leading source coefficients, not exact finite-epsilon response equality. The construction supplies neither a full cap-nine kernel return nor a fixed-target full-prefix rival.

Use the original accepted polynomials

    eta=(3t^2-d^3)/2, z=t+d,
    delta=-t^3/6+d^3 t/6+d^5/15-d^6/90,
    A=d^4(1-2d/5+d^2/15), I+96delta=-A-8z eta.

For a cell with opposite eta/delta signs and scale u positive, set s=u|eta/delta|. Then

    r=s^3 eta, k=s^4 delta, i=s^4 I,
    M=|r|/u^3=|eta|^4/|delta|^3,
    beta=b/u=z|eta/delta|,
    alpha=I/delta+42.

For an outer eta-positive/delta-negative cell alpha=A/(-delta)+8beta-54; for the middle eta-negative/delta-positive cell alpha=8beta-54-A/delta. These use the same physical d,z values throughout.

## 1. A concrete actual limiting middle cell with strict clock slack

Fix d1=d2=1/2 and put h=1/(2sqrt(6)). For the first outer cell at t1=-h, eta1=0 and

    Delta0=delta(1/2,-h)=(11-40/sqrt(6))/5760<0,
    A0=49/960,
    alpha0=A0/(-Delta0)-54
           =294/(40/sqrt(6)-11)-54.

The exact bounds are

    1<alpha0<3/2.

For the lower bound, sqrt(6)>2200/899 follows from 6 times 899^2 minus 2200^2 equalling 9206. For the upper bound, sqrt(6)<1480/603 follows from 1480^2 minus 6 times 603^2 equalling 8746. Direct substitution gives the two alpha inequalities.

For the actual middle cell d2=1/2 and positive t=T, write

    P(T)=-960T^3+120T+11,
    Q(T)=552-3600T-34560T^2-17280T^3,
    delta2=P/5760,
    alpha2(T)=Q/P,
    beta2(T)=360(T+1/2)(1-24T^2)/P.

On 2/25<=T<=1/12, P is positive and increasing, Q is positive and strictly decreasing. Thus alpha2 strictly decreases. Its exact endpoint values are

    alpha2(2/25)=106152/62839>3/2,
    alpha2(1/12)=9/92<1.

There is a unique Tstar strictly between these endpoints with alpha2(Tstar)=alpha0, and its derivative alpha2'(Tstar) is strictly negative. This actual middle cell has eta2<0,delta2>0,z2>0 and normalized amplitude Mstar=M2(Tstar)>0.

The beta numerator decreases and its denominator increases on this interval: the numerator derivative has sign 1-24T-72T^2<0, while P'=120-2880T^2>0. Consequently

    beta2(Tstar)<beta2(2/25)=552276/62839<729/82.       (1)

The final comparison has positive cross-product difference 522999. No numerical root or source sample was computed; the cell is defined by its unique exact scalar equation.

## 2. Actual outer cells with different physical degenerations

Let L=41/40 and introduce a small positive real parameter tau. The required amplitude and scale ratios will be

    theta=1/tau, lambda=L/tau^2,
    u3=1, u1=lambda,
    u2=(lambda+theta)/(1+theta)
       =(L+tau)/(tau(1+tau)).                       (2)

Use three as-yet unknown positive/physical functions X,D,T near fixed values, and choose actual source tuples

    d1=1/2, t1=-h-tau X;
    d2=1/2, t2=T;
    d3=tau^3 D, t3=200d3, z3=201d3.                 (3)

The first cell approaches its cubic-zero branch from eta1>0 with delta1<0. The last cell uses the positive-t eta3>0,delta3<0 branch, which is allowed by the unequal-ratio late clock. For every sufficiently small positive tau, all three tuples have strict 0<d_j<1,z_j>0. Boundary values at tau=0 serve only to prove existence; they are not claimed as admitted rivals.

The normalized amplitudes have analytic rescalings

    H1(tau,X)=M1/tau^4,
    H3(tau,D)=tau^3 M3.

Indeed eta1/tau=3hX+(3/2)tau X^2 and delta1 remains negative, so

    H1(0,X)=C1 X^4, C1=(3h)^4/(-Delta0)^3>0.

For the third cell, with v=200 and d=tau^3D,

    eta3=d^2 e(d), e(d)=(3v^2-d)/2,
    delta3=d^3 g(d),
    g(d)=-v^3/6+v d/6+d^2/15-d^3/90,
    H3(tau,D)=e(tau^3D)^4/[D(-g(tau^3D))^3].

This is analytic near positive D and tau=0, with

    H3(0,D)=K3/D, K3=2187/400,
    beta3->9(201/200)=1809/200,
    alpha3->18+72/200=459/25.                       (4)

The actual alpha1,alpha3 have analytic extensions under (3), because their displayed source denominators Delta0 and g(0) are nonzero. In particular alpha1(0,X)=alpha0, independently of X.

## 3. A nonsingular exact three-equation source system

The exact actual cubic amplitudes and i weights required by the unequal-ratio gate become

    H3(tau,D)-L^3 H1(tau,X)=0,
    M2(T)-[(1+tau)^4/(L+tau)^3]H3(tau,D)=0,
    alpha2(T)-[L alpha1(tau,X)+tau alpha3(tau,D)]/
                    (L+tau)=0.                    (5)

At tau=0 these equations have the explicit limiting solution

    T=Tstar,
    Dstar=K3/(L^3 Mstar)>0,
    Xstar=(Mstar/C1)^(1/4)>0.

The Jacobian in T,D,X is nonsingular. The third equation's T derivative is alpha2'(Tstar)<0, while its X,D derivatives vanish at tau=0. The second equation's D derivative is K3/(L^3 Dstar^2)>0, with zero X derivative. The first equation's X derivative is -4L^3 C1 Xstar^3<0. Ordering the equations third, second, first and the variables T,D,X gives a triangular Jacobian with three nonzero diagonal entries.

The real-analytic implicit-function theorem therefore supplies X(tau),D(tau),T(tau) near their strictly positive/physical limiting values, satisfying (5) EXACTLY for every sufficiently small positive tau. Define the actual scales s_j=u_j|eta_j/delta_j| from these functions. They are finite and positive for each such tau, even though they need not be bounded as tau approaches zero.

The first amplitude equation gives r3/r1=1/tau=theta; the second gives r2=-r1-r3. Equations (2) then give k1+k2+k3=0 with the required quartic signs. The third equation is precisely i1+i2+i3=0, since i_j=k_j(I_j/delta_j). Thus the cubic amplitudes, quartic weights and i balance are exact actual-source equalities, without treating any coefficient as independently adjustable.

## 4. Both positive gaps have strict physical limits

For the ratios (2), the necessary effective clock bounds are

    J1=(9/2)[1+1/(L+tau)]->729/82,
    J2=(9/2)[1+L/(1+tau)]->729/80.

Equation (1) gives beta2(Tstar)<729/82. Equation (4) gives beta3->1809/200<729/80, with strict difference 27/400. Analytic continuity therefore keeps both beta2<J1 and beta3<J2 for every sufficiently small positive tau.

Set the actual ordinary gap coefficients using the accepted exact supplied-source gate:

    D1=(9/2)[theta+lambda/(1+theta)],
    D2=(9/2)[1+lambda/(theta(1+theta))],
    ell1=D1-u2 beta2>0,
    ell2=D2-beta3>0.

These are genuine positive gap coefficients, with u3=1 as chosen. The effective distances are ell1+b2 and ell2+b3. They solve the full quartic chronological moment and the exact inherited G7 equation, while all source coefficients remain those of the actual cells constructed in (3)-(5).

Consequently the complete stated leading gate has actual strict solutions far outside the excluded bands. In particular lambda=L/tau^2 grows without bound. The near-proportional obstructions do not extend to this family automatically; the late positive-t source branch is an actual escape from their small late-clock premise.

## 5. The remaining response and full-G4 bridges

For any fixed sufficiently small positive tau, these actual source tuples and gaps can be inserted in the original rare-route epsilon family B(rho,exp(-epsilon s z),epsilon s). All parameters are finite and strictly positive at that fixed tau, so the physical source remains admitted for sufficiently small positive epsilon. The same tuples and parameters apply to every original admitted experiment; no observation or copy-access change is made.

This note establishes exact leading source balances and the vanishing G7 coefficient. It does not establish every remaining forest grade, the complete ordinary diagonal/lower-band equations, exact capped response equality or a full response return. The inherited universal quartic correction is a separate source step; no further complete-response claim is inferred here from the leading gate.

The next bounded task is to compute or prove a necessary higher-grade/full-target obstruction on this actual analytic escape, retaining both small parameters and fixing tau before any epsilon expansion. A joint limit of tau and epsilon cannot substitute for exact response equality. Original G4 still requires either one fixed positive full target with exact inequivalent finite positive rivals after every full legal prefix, or a full-rival finite forcing theorem with effective detectable stopping. No such endpoint, executed witness, Lean proof or historical novelty is claimed.
