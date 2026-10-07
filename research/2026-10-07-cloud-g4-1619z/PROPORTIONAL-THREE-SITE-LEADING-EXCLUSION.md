# A tighter actual late amplitude excludes the remaining proportional three-site leading gate

Contributor: Codex Cloud G4, 7 October 2026. New hand-derived argument, submitted for independent review. It uses and credits the programme auditor's read-only helper middle ratio/defect inequality already independently reviewed and reconstructed in the ratio-two note. No scientific arithmetic program, parameter scan, source/compiler evaluation, Lean or unchanged-control rerun occurred. Original G4 remains OPEN.

**Claim at the stated restricted scope:** no actual positive-outer proportional three-site coefficient sequence can simultaneously satisfy the full cubic/quartic prerequisites and G7=0 with strictly positive ordinary gaps. This is a fixed finite formal/analytic leading obstruction, not an all-word or isolated finite-epsilon theorem.

The controlling class is exactly

    r=(R,-R-S,S), R,S>0,
    k_j=c r_j, sum i_j=0,
    full quartic clock moment and strictly positive ordinary gaps.

Each site is an actual rare-route source cell with strict 0<d<1,z>0,s>0 and the accepted eta/delta/I polynomials. The supplied source, observations and shared parameters are retained. The [reviewed ratio-two proof](TWO-RATIO-SOURCE-AMPLITUDE-OBSTRUCTION.md) has already excluded S/R<=2. We therefore consider theta=S/R>2. Nonnegative c has strictly negative G7 by the accepted area equation; put c=-u with u>0.

Use the SAME actual normalized quantities

    M_j=|r_j|/u^3=|eta_j|^4/|delta_j|^3,
    beta_j=b_j/u=z_j|eta_j/delta_j|,
    alpha_j=I_j/delta_j+42>0,
    w=theta/(1+theta).

Cubic and i balance give M2=M3/w and alpha2=(alpha1+theta alpha3)/(1+theta). The reviewed late-cell boundary identity gives alpha3>8beta3, hence

    alpha2>8w beta3.                                  (1)

The reviewed physical middle strip p2>5/6 gives

    M2>E(54+alpha2)^3>E(54+8w beta3)^3,
    E=625/839808.                                     (2)

The two necessary positive gaps and the independently supplied middle ratio/defect bound retain the exact restrictions

    beta3<B(theta)=(9/2)[1+1/(theta(1+theta))],
    beta3<U(theta)=[D H1(theta)-54]/(8w),
    D=11-3sqrt(2), H1(theta)=(9/2)[theta+1/(1+theta)]. (3)

These are consequences of actual cells, not independent coefficient permissions.

## 1. The actual late strip improves to 1<p<25/9

For theta>2, the late clock in (3) is below 21/4. The accepted late branch has t=z-d<0. Put p=d/z>1 and retain the exact same-cell expressions

    eta/z^2=N/2, delta/z^3=T/6,
    N=3(p-1)^2-d p^2>0,
    T=(p-1)^3-d p^2(p-1)+d^2p^3(6-d)/15<0,
    beta=3N/(-T).

The [reviewed upper-ratio proof](THREE-RATIO-UPPER-OBSTRUCTION.md) used the exact polynomial L=4N+7T. Its d derivative increases to the negative endpoint p^2[3-(14/5)p] whenever p>=25/9, so

    L(d,p)>L(1,p)=(7/3)p^3-6p^2-3p+5.

At p=25/9 this last polynomial equals 835/2187 and its derivative equals 1432/81. Its derivative increases thereafter because 14p-12>0. Thus L>0 for p>=25/9, forcing beta>21/4 and contradicting (3). Any remaining actual late cell therefore has

    1<p<25/9.                                        (4)

The actual N>0,T<0 and original parameter bounds remain separately required.

## 2. An actual late amplitude coefficient strictly below 4/9

For this same late cell,

    M3=beta3^4 C, C=(-delta3)/z3^4>0,
    C(d,p)=p^3(p-1)/6-p(p-1)^3/(6d)-d p^4(6-d)/90.  (5)

We prove C<4/9 on the whole strip (4), using strict 0<d<1. This bound will be applied only to actual late cells; it does not create an admitted source by itself.

For p<=13/5, the already reviewed AMGM envelope and its monotonicity give

    C<Phi(p)<=Phi(13/5)
      =(114244/24375)[1-sqrt(32/39)]<4/9.

Here sqrt(32/39)>1811/2000 because 32 times 2000^2 minus 39 times 1811^2 equals 90881. The resulting upper fraction is 21592116/48750000; multiplying to compare it with 4/9 leaves the positive integer difference 670956. This is hand arithmetic, not an executed control.

For 13/5<=p<=25/9, put

    J=p(p-1)^3/6,
    C1=C(1,p)=(-p^4+6p^3-9p^2+3p)/18,
    L0=2p^4/45-J,
    kappa=2J-p^4/45.

The d curvature obeys

    C_dd=-2J/d^3+p^4/45<=-kappa.

Taylor's integral formula around d=1, with y=1-d, therefore gives

    C(d,p)<=C1+L0 y-(kappa/2)y^2
              <=C1+L0^2/(2kappa),                  (6)

provided kappa>0. The displayed endpoint certificates below show this condition. On this p interval, C1 increases, L0 is positive and decreases, and kappa increases. To check these directions directly, their first-derivative numerators are

    18 C1'=-4p^3+18p^2-18p+3,
    90 L0'=-44p^3+135p^2-90p+15,
    45 kappa'=56p^3-135p^2+90p-15.

C1'' is negative and decreasing here; C1'(25/9)=4487/13122>0. L0'' is negative and decreasing here; L0'(13/5)=-9968/11250<0, and L0(25/9)=2650/59049>0. Finally kappa'' is positive and increasing here and kappa'(13/5)=36332/5625>0. These certify all three directions without parameter sampling.

The following rational endpoint bounds can now be substituted into (6):

| p interval | C1 upper bound | L0 upper bound | kappa lower bound | Upper bound for C |
| --- | --- | --- | --- | --- |
| [13/5,27/10] | 5/12 | 13/50 | 5/2 | 5/12+169/12500 < 4/9 |
| [27/10,11/4] | 7/16 | 4/25 | 3 | 7/16+8/1875 < 4/9 |
| [11/4,25/9] | 221/500 | 9/100 | 18/5 | 709/1600 < 4/9 |

For reproducibility, the exact endpoint values supplying these deliberately loose bounds are

    C1(27/10)=74439/180000,
    C1(11/4)=1991/4608,
    C1(25/9)=52175/118098;
    L0(13/5)=7202/28125,
    L0(27/10)=15111/100000,
    L0(11/4)=1969/23040;
    kappa(13/5)=71279/28125,
    kappa(27/10)=121527/37500,
    kappa(11/4)=20977/5760.

The first two row comparisons with 4/9 reduce respectively to 169/12500<1/36 and 8/1875<1/144. The third comparison is 6381<6400 after cross multiplication. Thus every p,d in the relevant strip satisfies the strict bound

    C<4/9, M3<(4/9)beta3^4.                          (7)

## 3. Two coupled clock envelopes contradict actual middle balance

Combining (2), (7) and M2=M3/w forces

    E<V(theta,beta3),
    V(theta,beta)=4beta^4/[9w(54+8w beta)^3].          (8)

For fixed theta, V strictly increases with positive beta, with derivative sign 216+8w beta. At fixed beta it strictly decreases with w. Let theta0=97/40 and w0=97/137.

On 2<theta<=theta0, use beta3<U(theta). We claim V(theta,U(theta)) increases with theta over this interval. Put Y=D H1>54. Apart from a fixed positive factor this expression is

    (Y-54)^4/(w^5Y^3).

Its logarithmic derivative, multiplied by theta(1+theta), is

    [theta^2(theta+2)/(theta^2+theta+1)]
       [1+216/(Y-54)]-5.

The first bracket exceeds one for theta>1. On the stated bounded interval D<7 and H1(theta0)<49/4, so Y-54<127/4 and the second bracket exceeds 991/127>5. The logarithmic derivative is strictly positive. Consequently

    V(theta,beta3)<V(theta0,U(theta0)).

The endpoint satisfies U(theta0)<81/16. For an exact source-independent radical bound, sqrt(2)>140/99 because the squared comparison leaves 2/9801; hence D<223/33. Also H1(theta0)=134001/10960. The desired U bound follows from

    223 times 134001 < 1320 times 22653,

whose right side minus left side is 19737. Thus V(theta,beta3)<V(theta0,81/16) on the entire first interval.

For theta>=theta0, use the other actual clock condition beta3<B(theta), with B decreasing and w increasing. Its endpoint obeys

    B(theta0)=134001/26578<81/16,

whose cross multiplication leaves 8802. Therefore V(theta,beta3)<V(theta0,81/16) on this second interval as well. Neither branch relaxes the same-cell source or weighted ratio conditions used to obtain (3).

Finally

    V(theta0,81/16)
      =[(548/873)(81/16)^4]/(22653/274)^3
      <413/(165/2)^3
      =3304/4492125<E.

The numerator is below 413 by exact rational comparison and the denominator base exceeds 165/2. The final comparison with E=625/839808 leaves

    625 times 4492125 minus 3304 times 839808
      =32852493>0.

This contradicts (8) for every theta>2. Together with the separately reviewed earlier exclusions, the stated actual positive-outer proportional three-site leading gate has no solution.

## 4. What this would close and what remains open

If independently accepted, the result excludes this entire three-site proportional positive-outer mechanism for a fixed finite formal/analytic ordinary return. It adds an actual source obstruction to the abstract free-coefficient gap gate. It proves neither a sign theorem for all words nor the original finite-stopping conclusion.

The source-admitted finite quartic feasibility result remains valid: it neither assumed this specific proportional three-site class nor cancelled every remaining forest coefficient. Longer words, nonproportional k/r, negative-outer patterns, other relative rare-route scales, other grades/coordinates and isolated finite-epsilon equalities remain unresolved. There is still no one fixed full ordinary target with inequivalent finite positive rivals after every full legal prefix, and no general effective detectable stopping theorem. No full G4 or G6 endpoint, executed scientific validation, Lean proof or historical novelty is claimed here.
