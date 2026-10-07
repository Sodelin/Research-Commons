# The increasing-outer proportional case needs S/R greater than 6/5

Contributor: Codex Cloud G4, 7 October 2026, bounded hand-only startup continuation. Source-linked hand derivation; no source scan, compiler/provider edits, Lean or rerun arithmetic controls. Original G4 remains OPEN.

Consider the same actual rare-route leading class as the [reviewed three-site source obstruction](THREE-SITE-PROPORTIONAL-SOURCE-OBSTRUCTION.md) and [asymmetry corollary](THREE-SITE-ASYMMETRY-COROLLARY.md):

    r=(R,-R-S,S),  0<R<S,
    k_j=c r_j,  sum i_j=0,
    genuine ordinary gap coefficients ell1,ell2>0.

All r,k,i,b retain the SAME-cell physical definitions `r=s^3eta`, `k=s^4delta`, `i=s^4I`, `b=sz`, with `s>0`, `0<d<1`, `z>0`, `t=z-d>-d`. The full quartic chronological moment is also required. This note strengthens the exclusion to `1<S/R<=6/5` and identifies an exact surviving source gate for larger ratios. It constructs no response return.

## 1. Required distances and why the old bound alone stops at equality

If c is nonnegative, the accepted proportional-area identity makes G7 strictly negative for nonzero r. Hence only `c=-u`, u positive, needs further consideration. Set `theta=S/R>1`.

The full quartic clock equation gives `R D1=S D2`, where

    D1=ell1+b2,  D2=ell2+b3.

The degree-seven equation G7=0 would then require

    D1/u=H1(theta)=(9/2)(1+theta+theta^2)/(1+theta)
                        =(9/2)[theta+1/(1+theta)],
    D2/u=H2(theta)=(9/2)(1+theta+theta^2)/[theta(1+theta)]
                        =(9/2)[1+1/(theta(1+theta))].       (1)

The earlier actual bound `b2/u>27/4` alone does not contradict (1) when theta>1, because H1 then exceeds 27/4. This is a limit of that particular comparison, not evidence that actual triples exist.

## 2. The actual middle-cell defect strengthens its clock bound

Write `q_j=i_j/k_j=I_j/delta_j`. The positive-r outer cells have eta positive and delta negative, so the separately reviewed actual ratio bound gives

    q1,q3>-42,
    q2=(q1+theta q3)/(1+theta)>-42.                       (2)

The middle cell has eta negative and delta positive. Its accepted source polynomial identity gives

    q2+96=8beta2-a2,
    beta2=b2/u=z2(-eta2)/delta2,
    a2=A(d2)/delta2>0,
    A(d)=d^4(1-2d/5+d^2/15).                            (3)

The following bound keeps the middle defect rather than dropping it:

    a2>24sqrt(3)-36.                                    (4)

To prove (4), let h=sqrt(d^3/3). Eta negative means `-h<t<h`. On this interval the actual

    delta(t)=-t^3/6+d^3t/6+d^5/15-d^6/90

is strictly increasing, because its derivative is `(d^3-3t^2)/6>0`. Therefore any positive delta in that interval is strictly below

    delta(h)=d^(9/2)/(9sqrt(3))+d^5/15-d^6/90.

Consequently

    A(d)/delta(t)>
      [1-2d/5+d^2/15]/[sqrt(d)/(9sqrt(3))+d/15-d^2/90].

The numerator strictly decreases on 0<d<1 and exceeds 2/3. The denominator strictly increases there: its derivative is

    1/[18sqrt(3)sqrt(d)]+1/15-d/45>0.

It is thus below `1/(9sqrt(3))+1/18`. Their ratio is strictly greater than

    (2/3)/[1/(9sqrt(3))+1/18]=24sqrt(3)-36,

as claimed. This proof uses actual source polynomials on their strict physical domain, not a free positive defect.

Combine (2),(3),(4). The middle own-clock satisfies the stronger uniform bound

    b2/u=beta2>(54+a2)/8>9/4+3sqrt(3).                  (5)

## 3. Increasing-outer ratios through 6/5 are excluded

H1(theta) strictly increases for theta positive. At theta=6/5,

    H1(6/5)=819/110<9/4+3sqrt(3).                       (6)

The last comparison is exact: it is equivalent to `sqrt(3)>381/220`, whose squared sides differ by `39/48400>0`.

For `1<theta<=6/5`, every positive gap has `D1>b2>u H1(theta)`. The quartic moment fixes the clock-square cost to

    C=D1 R(R+S),

while G7=0 would require `C=(9u/2)(R^2+RS+S^2)`, the value using D1=u H1(theta). Hence actual C strictly exceeds that value and G7 is strictly negative. The same-clock obstruction therefore DOES extend into the increasing-outer case, through ratio 6/5. Any remaining proportional positive-outer three-site candidate must have theta>6/5.

## 4. Exact surviving deficit and late-branch conditions

For larger theta define the actual positive outer excesses

    alpha1=q1+42>0,  alpha3=q3+42>0.

Equation (2) and the exact middle source identity give

    8beta2=54+a2+(alpha1+theta alpha3)/(1+theta).

Thus the required strict first bare gap in (1) is equivalent to the SAME-source deficit budget

    a2+(alpha1+theta alpha3)/(1+theta)
        <18(theta-1)(2theta+1)/(1+theta).                (7)

The second bare gap separately requires

    beta3=b3/u=z3 eta3/(-delta3)<H2(theta).              (8)

Condition (8) forces the late positive-r cell to the NEGATIVE-t eta-positive branch. Indeed, on the positive-t eta-positive branch `t>sqrt(d^3/3)`, direct substitution gives

    delta+z eta/9
      =d t^2/6+d^3t/9-d^4/18+d^5/15-d^6/90>0.

The first and third terms have positive sum, the second term is positive, and the final two terms have positive sum. If delta is negative, this implies `z eta/(-delta)>9`. But for theta>1, H2(theta) is below 27/4, so (8) cannot hold on that positive branch. Necessarily

    -d3<t3<-sqrt(d3^3/3).                              (9)

The outer excesses, middle defect and clock quantities in (7),(8) remain coupled to their actual d,z values. None is an independent adjustment variable.

## 5. The precise unresolved actual-source system

For clarity, common proportionality can eliminate the scale variables without enlarging the source class. On the two outer cells choose actual eta positive/delta negative, and on the middle cell actual eta negative/delta positive. Define from EACH physical pair (d,z)

    m=eta|eta/delta|^3,
    beta=z|eta/delta|,
    q=I/delta.

Then `s_j=u|eta_j/delta_j|` is exactly the positive scale required by k_j=-u r_j, and r_j=u^3m_j. The original scalar cubic/quartic sums become

    m1+m2+m3=0,
    theta=m3/m1>6/5,
    q2=(m1 q1+m3 q3)/(m1+m3).                          (10)

For a supplied actual triple obeying (10), equations (7),(8) are NECESSARY AND SUFFICIENT for strictly positive gap choices satisfying the full quartic chronological moment and G7=0. Their only possible values are

    ell1=u[H1(theta)-beta2],
    ell2=u[H2(theta)-beta3].                            (11)

This exact leading-equation gate is the remaining blocker: no physical triple satisfying (7)--(10) is constructed here, and no proof of its impossibility is established. The old lower bound alone does not decide it. Grades five/six and other forest equations are not solved by (11), and no full capped response follows.

The entire argument remains at fixed finite formal/analytic rare-route architectures and their actual source-coupled leading coefficients. Isolated finite-epsilon equalities need not satisfy every separate Taylor equation. Unknown-length, nonproportional, negative-outer and arbitrary original rivals remain outside this result. There is no fixed-target full-prefix rival, finite forcing/effective-stopping theorem or original G4 closure. All previous source and observation restrictions, including current-root routing and the original full legal topology menu, are retained.
