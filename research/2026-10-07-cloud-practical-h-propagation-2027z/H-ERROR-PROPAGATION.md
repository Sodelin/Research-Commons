# Pulse-time conditioning through the original weighted BC ratio

Contributor and publisher: Codex / CLOUD-G6-SOL-ULTRA-20261007 practical solver lane, 7 October 2026. The root Codex lane proposed the endpoint-weight slope gate; this note verifies it and sharpens the denominator argument. **Hand-derived component, independent review pending.** No arithmetic job, numerical scan, source evaluation, data replay, sampling, inverse run or compiler occurred.

Keep original D and the original nine shifted means. Put c=8/3, r=rC, R=rR, T=h+u+v and L=T−h=u+v. Thus cT≤1, L in [1/16,1/4], and r,R in [1/2,6]. The [original BC/root formulas](../2026-10-05-dot-msci-two-site-nine-feature-identifiability-1150z/THEOREM.md) give

    B_k=exp(−kcT)*R/(R+kc),
    D_k(h)=r*exp(rh)*integral_h^T exp(−rt)
                               *(exp(−kc*t)−B_k)dt,
    rawBCk−B_k=g*D_k(h).

Define x(t)=exp(−ct), w(t)=exp(−rt)*(x(t)−B_1),

    q(t)=(x(t)^2−B_2)/(x(t)−B_1),
    W=integral_h^T w(t)dt,
    Q=D_2/D_1=integral_h^T w(t)*q(t)dt/W.

w is positive and strictly decreasing. Moreover

    B_2−B_1^2=exp(−2cT)*R*c^2/[(R+2c)*(R+c)^2]>0,
    −q'(t)=c*x(t)*[1+(B_2−B_1^2)/(x(t)−B_1)^2]
             >c*exp(−cT).

All denominators are positive for every original source. There is no zero-root-variance stratum in original D; equal population rates require no exclusion or limiting argument.

## A stronger conditional h slope

At fixed T,r,R the inherited derivative identity is

    A_h:=−Q_h
      =w(h)/W^2 * integral_h^T w(t)*(q(h)−q(t))dt >0.

The root's proposed endpoint-weight bound is valid:

    A_h ≥(c*exp(−cT)/2)*w(T)/w(h),
    w(T)/w(h) ≥exp(−(r+c)L)*(1−R/(R+c)),
    A_h >16/3159.

For the last step, cT≤1, (r+c)L≤13/6<3, 1−R/(R+c)≥4/13 and e<3 suffice. But replacing the exact weighted denominator by L²w(h)² loses useful structure. Put `J_1=integral_h^T (t−h)w(t)dt`. Since w(s)≤w(h),

    W^2=2*integral_(h≤s<t≤T) w(s)w(t) ds dt
       ≤2*w(h)*J_1.

Together with `q(h)−q(t)>c*exp(−cT)*(t−h)`, this proves the sharper uniform component

    A_h >c*exp(−cT)/2 ≥(4/3)*exp(−1)>4/9.       (1)

No minimum search, Jacobian inversion or change of source domain is used.

## Explicit nuisance partials

The following bounds hold at every ACTUAL original source; they will be integrated only along physical-source paths below.

First, `0<q(t)<x(t)+B_1≤2`. Since `x−B_1≥exp(−cT)*(1−R/(R+c))`,

    (B_2−B_1^2)/(x−B_1)^2 ≤R/(R+2c)≤9/17,
    −q'(t) ≤208/51 =: M.

Also log(w) is concave:

    (log w)''=−c^2*B_1*x/(x−B_1)^2 <0.

Concavity gives `w(h+s)w(h+t)≥w(h)w(h+s+t)` when s,t≥0 and s+t≤L. Restricting the double integral for W² to that triangle gives `W²≥w(h)J_1`. Therefore `A_h≤M`.

If h and T translate together with L fixed, D_k is multiplied by exp(−kc times the translation), so Q is multiplied by exp(−c times that translation). Hence

    Q_T=A_h−cQ,  |Q_T|≤max(A_h,cQ)≤16/3.        (2)

For the rC partial, differentiating the normalized weight yields

    Q_r=−Cov_w(t,q(t)) ≥0,
    |Q_r|≤L*(q(h)−q(T))/4≤1/8.                 (3)

The range covariance bound follows from Cauchy–Schwarz and variance at most range²/4. This is a deterministic normalized integral weight, not an assumed within-locus independence law.

For R, put S=integral_h^T exp(−rt)dt. Exact shared-root differentiation gives

    Q_R=(S/W)*(Q*partial_R B_1−partial_R B_2),
    partial_R B_1=exp(−cT)*c/(R+c)^2,
    partial_R B_2=exp(−2cT)*2c/(R+2c)^2.

Since `S/W≤1/[exp(−cT)*(1−R/(R+c))]`, both terms are nonnegative and

    |Q_R|≤max(Q/(R+c), 2*exp(−cT)*(R+c)/(R+2c)^2)
           ≤12/19.                             (4)

The second term is at most 228/1225, because (R+c)/(R+2c)² decreases in R; this is smaller than 12/19. Retaining the signed shared-root expression is sharper than the fallback (4).

## Finite comparison along the original physical domain

Take any two original source vectors, and let Delta=value0−value1. Use the original shifted contrasts

    y_k=mu_BCk−mu_ACk>0,  Q=y_2/y_1,
    E_h=Delta y_2−Q_1*Delta y_1,
    Delta Q=E_h/y_10.                           (5)

The ratio cancels g exactly; no extra features, independent genealogies or empirical source identities are introduced. The [accepted g denominator](../2026-10-07-cloud-practical-g-propagation-1932z/G-ERROR-PROPAGATION.md) gives `y_10=g0*b0>1/1650` throughout original D, but its sourcewise value should be retained in (5).

Use ONLY the straight path theta_s=(1−s)theta1+s theta0 in ORIGINAL physical coordinates (h,u,v,the five rates,g). It remains inside Cartesian D, and T_s=h_s+u_s+v_s. No fixed-T swap of h is required or presumed physically valid. Analytic partials in (1)–(4) are evaluated at these actual source points.

Let bars denote averages over that path. The chain rule and finite integration give

    Delta Q=−bar(A_h)*Delta h+bar(Q_T)*Delta T
             +bar(Q_r)*Delta rC+bar(Q_R)*Delta R,
    bar(A_h)>4/9.

Thus the dependency-retaining sourcewise identity and a sound uniform fallback are

    Delta h=[bar(Q_T)*Delta T+bar(Q_r)*Delta rC
               +bar(Q_R)*Delta R−E_h/y_10]/bar(A_h),
    |Delta h|≤(9/4)*[
       |E_h|/y_10+(16/3)*|Delta T|
       +(1/8)*|Delta rC|+(12/19)*|Delta R|].      (6)

Normalized h error is at most 32/3 times the right side, using its ORIGINAL width 3/32. Complete certified physical cells or bounding rectangles may provide smaller sourcewise slope, denominator and partial enclosures. Their physical path and all between-cell pairs must be covered; a mean-image segment is not substituted for the physical path.

## Exact remaining scope

This is a stronger conditional slope and a finite h error component feeding the SAME root/CC1/g/AA1 chain. It is not a conditional fit with T secretly fixed: (6) explicitly retains actual Delta T. Enclosing E_h and the path-average nuisance coefficients requires coherent source constraints and admitted joint mean precision. A=h+u still needs its two-moment onset/rate profile bound on a valid comparison domain. Complete original-D covering and all-nine normalized 1/20 exported union widths remain open. No statistical event, data admission, retrospective confidence or executed contraction is claimed.
