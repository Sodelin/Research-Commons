# A removable quartic term and an unremovable fifth quotient on the actual unequal family

Contributor: Codex Cloud G4, 7 October 2026. New hand-derived argument, submitted for independent review. No parameter scan, source evaluation, scientific arithmetic harness, compiler/provider edit, Lean or unchanged-control rerun. Original G4 remains OPEN.

Fix a sufficiently small positive tau in the [independently accepted actual unequal-source leading family](ACTUAL-LARGE-UNEQUAL-RATIO-LEADING-FAMILY.md), frozen SHA256 `30724870d878896ac07bcdffd5a11efa6c7bfcc1aa25f9c65f55530f8a2bf9b0`. Keep this tau fixed before varying the physical rare-route parameter epsilon. The accepted family cancels the exact leading r,k,i balances, chronological moment and G7, with two positive ordinary gaps. This note analyzes the first omitted complete-response grades for that SAME actual three-cell family.

**New hand claim:** the remaining quartic R term is removable by an actual first-order middle-cell source correction. After any actual first/second parameter or gap corrections with these leading source tuples, a specified complete fifth-source quotient has a strictly positive coefficient. Thus the sufficiently small fixed-tau family cannot extend to a formal/analytic ordinary return. This is a restricted family obstruction, not a full G4 theorem or an assertion about isolated finite-epsilon equality.

## 1. Actual removal of the remaining full quartic R coefficient

The [accepted general full-quartic source identity](../2026-10-06-dot-g4-full-rare-route-quartic-balance-0310z/GENERAL-QUARTIC-BALANCE-CANDIDATE.md) gives, with scale s,

    C3=s^3 eta R,
    C4=s^4[a4 R+(I/6)T+z eta[Q,R]+delta Z],
    a4=(D-I)/2,
    D=-6z^3+(6d-9)z^2+12dz-3d^2+6z eta.

All three cells have coincident leading ordinary placement; their real first-order placement gaps are those already fixed by the accepted family. The accepted sums of i,k and the physical chronological moment remove the non-R quartic directions. Let

    R4=sum_j s_j^4 a4_j

be the remaining R coefficient. For the fixed positive tau, every s_j and R4 is finite. The actual middle cell has t2=T(tau)>0. Its physical derivative is

    partial_z(s2^3 eta2)=3s2^3 t2!=0.

Choose the actual source correction

    z2(epsilon)=z2+epsilon w,
    w=-R4/(3s2^3 t2).

Its chain-rule contribution to degree four is exactly -R4 R. It does not change the leading r,k,i coefficients or leading gap coefficients; the leading G7 equation is consequently retained. Strict source parameters and positive gaps remain strict for sufficiently small positive epsilon, with the smallness bound allowed to depend on the fixed tau.

By the inherited complete all-arity quartic identity, this supplies pair-normalized complete forest response I+O(epsilon^5) at every fixed arity. It does not solve degree five. No numerical value of w was evaluated or assigned as an independent forest operator.

## 2. A complete fifth quotient invariant under every allowed lower correction

Use the accepted [complete fifth-source output and reconstruction](../2026-10-06-dot-g4-complete-fifth-source-cone-0329z/review/RESULT-REVIEW.md), source RESULT.json SHA256 `0a71280a0a41c3e39204f06400d4c56ba6e8e408f2f4a8015769256435646d8b`. It represents every complete entering forest row through five roots, not selected diagonals. The lower module is

    Llow=span{R,T,Z,[Q,R],[Q,[Q,R]],[Q,Z]}.

The complete coefficient span has dimension eight and Llow has dimension six. Define the quotient coordinate functional Bfun to kill Llow and to have values zero and one respectively on the saved rho^0 z^0 and rho^0 z^1 fifth coefficient operators. The accepted exact reconstruction defines it on the entire eight-dimensional source/lower span. Its actual one-cell scalar polynomial is

    B(rho,z)=c0(rho)+c1(rho)z+c2(rho)z^2
                 +(16/3)(1-rho)z^3-(35/24)z^4,
    c0=-rho/10+rho^2/4-5rho^3/42-rho^4/12
                 +7rho^6/120-rho^10/168,
    c1=1-8rho/5-rho^2/2+4rho^3/3-7rho^6/30,
    c2=-9/2+27rho/4-9rho^3/4.                       (1)

For our collapsed leading placements, this quotient is unchanged by arbitrary finite first and second actual corrections of rho,z,s and the real placements/gaps. Indeed physical derivatives of C3 are R multiples; placement derivatives add ad_Q R and ad_Q^2 R. C4 and its physical derivatives lie in span{R,T,Z,ad_Q R}; its placement derivative adds only ad_Q^2 R and ad_Q Z, since [Q,T]=0. Thus every fifth chain-rule correction lies in Llow. No cross-cell product appears below degree six. These observations also cover the quartic correction in Section 1 and second-order real gap corrections.

A common leading ordinary conjugation is invertible and can be removed algebraically from the complete response before applying Bfun. It does not add a source observation or permit negative population time. The actual degree-five quotient of the word is therefore the correction-independent scalar

    F5(tau)=sum_{j=1}^3 s_j(tau)^5 B(rho_j(tau),z_j(tau)). (2)

This invariance concerns the stated common-leading-placement family with analytic/formal integer-order corrections. It is not annihilation of every lower conjugation at every possible leading placement.

## 3. The actual early and middle terms dominate with a strict positive margin

Reuse the accepted source-family constants

    h=1/(2sqrt(6)), Delta0=(11-40/sqrt(6))/5760<0,
    d1=d2=1/2,
    t1=-h-tau X(tau), t2=T(tau),
    Tstar=T(0) in (2/25,1/12), delta_star=delta(1/2,Tstar)>0,
    gamma2=(-eta(1/2,Tstar))/delta_star>0,
    L=41/40.

Writing the polynomial (1) at rho=1/2,z=t+1/2 gives the exact simple form

    Bhalf(t)=2539/860160+(197/1920)t+(13/32)t^2
                         -t^3/4-(35/24)t^4.         (3)

On 2/25<=t<=1/12 its derivative is positive: discard its positive linear-in-t term and bound the two negative terms by their values at 1/12. Thus

    Bmiddle=Bhalf(Tstar)>Bhalf(2/25)>27/2000.         (4)

For explicit hand reproduction, Bhalf(2/25) is

    2539/860160+197/24000+13/5000-2/15625-70/1171875.

The five terms respectively satisfy the bounds >29/10000, >82/10000, =26/10000, <13/100000 and <6/100000 for the two subtracted positive costs. Their sum is above 1351/100000>27/2000.

At the early cubic-zero limit t=-h, (3) gives

    Bearly=134291/7741440-(59/640)h>-3/2000.          (5)

For an exact loose bound, h<817/4000 follows from 6 times 817^2 minus 2000^2 equalling 4934. Also 134291/7741440>1734/100000. Subtracting the resulting cost 48203/2560000 leaves a value above -3/2000: the last comparison is equivalent to 471/25000>48203/2560000. Only a lower bound is used; no sign assumption on Bearly is needed.

The middle endpoint bounds give

    delta_star<delta(1/2,1/12)=23/6480<9/2500.

The early limit satisfies -Delta0>9/10000. Indeed sqrt(6)<49/20 gives -Delta0>261/282240>9/10000. Consequently

    0<delta_star/(-Delta0)<4,
    [delta_star/(-Delta0)]^(5/4)<4sqrt(2)<6.          (6)

The accepted source-family rescalings show

    tau s1->K1=L(3hXstar)/(-Delta0),
    tau s2->K2=L gamma2,
    K1^4/K2^4=delta_star/(-Delta0).

The last identity follows directly from its limiting amplitude equation Mstar=(3hXstar)^4/(-Delta0)^3 and Mstar=(-eta_star)^4/delta_star^3. Thus

    lim tau^5[s1^5 B1+s2^5 B2]
      =L^5 gamma2^5 {Bmiddle+
          [delta_star/(-Delta0)]^(5/4) Bearly}
      >L^5 gamma2^5 (9/2000)>0.                     (7)

The strict bracket bound is (4)-(6): it is above 27/2000-6 times 3/2000. This uses actual source limits and exact balances, not independently chosen quotient values.

## 4. The late term cannot cancel that fifth coefficient

For the same actual late cell, d3=tau^3 D(tau),t3=v d3,z3=(v+1)d3 with v=200. Direct hand collection of the accepted polynomial (1) gives

    B(1-d,(v+1)d)
      =d^4 v^2(12-12v-35v^2)/24+O(d^5).

There is no term below d^4. The accepted physical scale has s3=O(d3^(-1)), so

    s3^5 B3=O(d3^(-1))=O(tau^(-3)),
    tau^5 s3^5 B3->0.                               (8)

Combining (7),(8) proves tau^5 F5(tau) has a strictly positive limit. Hence F5(tau)>0 for every sufficiently small fixed positive tau in the accepted actual branch.

Once such a tau is fixed, all physical correction coefficients may be arbitrary finite real values but cannot change (2). The degree-five complete response is therefore nonzero after any first/second actual correction, including the removable quartic R correction. Higher integer-order corrections first affect degree six or later. This family cannot give I+O(epsilon^6), and hence cannot give an analytic exact ordinary return with these leading tuples.

## 5. Exact reach, legal response meaning and remaining G4 dependency

The fifth quotient is a linear coordinate of the complete finite natural response through five entering roots, with its basis and lower annihilation authenticated by the inherited complete source reconstruction. The original private rooted-topology completion family reconstructs those full forest rows through the accepted tester interface; at most eight total copies suffice for five entering roots plus the three completion copies. Positive ordinary padding and pair calibration are algebraically invertible. Thus a nonzero complete fifth response obstructs the full original ordinary target on this restricted analytic family, without adding a new observation channel. This is a hand transfer using the inherited admitted-tester theorem, not a new executed source or Lean check.

The obstruction fixes tau before the epsilon expansion. It makes no claim about a joint tau-epsilon limit, isolated finite-epsilon coincidences, different leading source tuples, more cells, other scales or arbitrary positive words. It does not contradict the inherited cubic-through-fifth existence theorem, whose finite architectures and leading placements differ and whose complete-source cone permits both signs.

The actual unequal leading-family feasibility result remains valid: it cancels the stated leading gate, but the newly exposed fifth quotient prevents continuing that branch to full response equality. The next genuine source task requires a different actual leading architecture that also cancels both complete fifth quotient coordinates and every lower corrected direction, or a broader exact source rigidity theorem. Original G4 still needs a one-fixed-target/full-legal-prefix exact positive rival construction or a full-rival finite forcing/effective-stopping theorem. No master closure, executed witness, machine proof or historical novelty is claimed.
