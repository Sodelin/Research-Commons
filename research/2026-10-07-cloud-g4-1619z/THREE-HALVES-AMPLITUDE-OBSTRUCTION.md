# Actual amplitudes exclude the increasing-outer case through S/R=3/2

Contributor: Codex Cloud G4, 7 October 2026. Hand-only continuation using actual single-cell reachable relations. No source scan, source/compiler execution, provider edit, Lean or unchanged-control rerun. Original G4 remains OPEN.

Use the same actual positive-outer proportional three-site leading class:

    r=(R,-R-S,S),  R,S>0,
    k_j=c r_j,  sum i_j=0,
    strictly positive ordinary gap coefficients,
    full quartic chronological moment.

The [increasing-outer source gate](INCREASING-OUTER-SOURCE-GATE.md) already excludes theta=S/R through 6/5. This source-amplitude comparison excludes the remaining interval `6/5<theta<=3/2`. Its prerequisite [late-cell envelope](LATE-CELL-AMPLITUDE-ENVELOPE.md) is a separate hand argument whose exact physical restriction p=d/z<3 is used here. This note supplies no actual triple beyond the exclusion or complete response return.

As before c nonnegative gives negative G7 immediately. Take c=-u with u positive. The actual normalized variables are

    M_j=|r_j|/u^3=|eta_j|^4/|delta_j|^3,
    beta_j=b_j/u=z_j|eta_j/delta_j|,
    q_j=I_j/delta_j,
    alpha_j=q_j+42.

All three alpha values are positive: the outer source-ratio theorem gives alpha1,alpha3 positive, and the actual i sum gives

    alpha2=(alpha1+theta alpha3)/(1+theta).              (1)

The two outer cells have eta positive/delta negative; the middle has eta negative/delta positive. Their underlying strict d,z and positive scales remain original physical parameters throughout.

## 1. The late negative branch has a stronger ratio/clock relation

The accepted late-clock gate requires beta3<B(theta)<27/4, so the prior source branch argument forces `-d<t<-h`, with `h=sqrt(d^3/3)`. There delta is negative and its derivative `(d^3-3t^2)/6` is negative. Therefore

    delta(t)>delta(-h),  and -delta(t)<-delta(-h).

The existing actual ratio proof's positive boundary polynomial gives `A(d)+54delta(-h)>0`. The boundary delta is negative because it lies below the actual negative delta(t). Divide to obtain

    a3=A(d3)/(-delta3)>A(d3)/[-delta(-h)]>54.

The SAME-cell identity consequently strengthens the late excess to

    alpha3=a3+8beta3-54>8beta3.                       (2)

This retains the actual clock instead of dropping it from the previously accepted ratio bound.

## 2. Ratios through 3/2 force a small late amplitude

The accepted middle bound gives `a2>24sqrt(3)-36`, and hence

    beta2=(54+a2+alpha2)/8
          >K+alpha2/8,  K=9/4+3sqrt(3).

Equations (1),(2) imply `beta2>K+[theta/(1+theta)]beta3`. A positive first gap with G7=0 also requires beta2<H1(theta), so

    beta3<T(theta)=[(1+theta)/theta][H1(theta)-K],
    H1(theta)=(9/2)[theta+1/(1+theta)].                (3)

The function T can be written

    T(theta)=(9/2)theta+(9/2-K)+(9/2-K)/theta.

It strictly increases for theta positive, since K>9/2. At theta=3/2,

    T(3/2)=21/2-5sqrt(3)<15/8.                       (4)

The last strict inequality follows from `sqrt(3)>69/40`; the squared sides differ by `39/1600>0`. Thus every supplied actual candidate with `6/5<theta<=3/2` must have beta3<15/8.

The late physical strip p3=d3/z3<3 and 0<H(d3)<1, where `H(d)=1-2d/5+d^2/15`, give its exact amplitude formula

    M3=beta3^4 p3^4 H(d3)/a3<(3/2)beta3^4.

Here the last inequality uses the ACTUAL bound a3>54 and p3^4 H(d3)<81. Combining with (4),

    M3<(3/2)(15/8)^4=151875/8192<19.

The actual cubic balance `|r2|=R+S` then forces

    M2=(1+1/theta)M3<(11/6)19=209/6<35.             (5)

The factor 11/6 uses theta>6/5. Neither amplitude is a free signed control.

## 3. Every actual middle cell with alpha2 positive has amplitude above 39

For the middle cell, eta negative implies `|t|<sqrt(d^3/3)`. Set p=d/z. The strict physical domain gives

    p>p0=sqrt(3)/(sqrt(3)+1),
    H(d)>2/3.

Its SAME-cell identity writes `a=A(d)/delta=8beta-54-alpha>0`. The normalized amplitude is exactly

    M=beta^4 p^4 H(d)/(8beta-54-alpha).

Let L=54+alpha>54. On beta>L/8, the function `beta^4/(8beta-L)` has its unique minimum at beta=L/6, of value L^3/432. This follows directly from its derivative `4beta^3(6beta-L)/(8beta-L)^2`. Therefore every such actual middle cell satisfies

    M>(2/3)p0^4 L^3/432
      >243p0^4=2187/(28+16sqrt(3))>39.             (6)

The last comparison uses sqrt(3)<7/4, so the denominator is below 56, and 2187/56>39. This is a lower bound on the actual reachable source image under alpha positive, not a minimum asserted to be attained physically.

## 4. Contradiction and exact reach

The supplied leading class necessarily has alpha2 positive by (1). Its actual middle amplitude must therefore satisfy (6), contradicting (5). No such source-coherent three-site candidate can have G7=0 for `6/5<theta<=3/2`. In fact the same comparison excludes all positive quartic-matching gap choices that could supply that zero.

Together with the separately reviewed earlier clock obstruction, any remaining positive-outer proportional three-site ordinary-return candidate must have

    S/R>3/2.

This threshold is a necessary condition only and is not claimed optimal. The proof does not construct an actual larger-ratio triple, decide the remaining source system, solve grades five/six or other forest coefficients, or furnish exact finite-epsilon/full-prefix rivals. Nonproportional words, negative outer signs, arbitrary word lengths, other scalings and original full-rival/effective-stopping transfer remain unresolved. A Taylor-coefficient obstruction applies to the stated fixed analytic/formal family, not arbitrary isolated finite-epsilon equality. No full G4 endpoint follows.
