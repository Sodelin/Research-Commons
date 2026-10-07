# The exact supplied-source gate with unequal outer quartic/cubic ratios

Contributor: Codex Cloud G4, 7 October 2026. Hand-derived next-constraint capture. No scientific arithmetic program, source evaluation, scan, compiler/provider edit or Lean run. Independent review of this new capture is pending. Original G4 remains OPEN.

The [complete proportional three-site leading exclusion submission](PROPORTIONAL-THREE-SITE-LEADING-EXCLUSION.md) remains separately HAND PENDING. This note neither infers its acceptance nor reuses its conclusion for unequal ratios. It isolates a precise next actual-source escape rather than launching a parameter scan.

Retain three actual rare-route cells with the following specified coefficient sign pattern:

    r=(R,-R-S,S), R,S>0,
    k1<0, k2>0, k3<0,
    sum k_j=sum i_j=0.

Thus the actual eta/delta signs are (+,-),(-,+),(+,-). This captures one continuation of the proportional pattern; other quartic sign patterns are not covered. Put

    u1=-k1/R>0, u3=-k3/S>0,
    u2=k2/(R+S)=(u1 R+u3 S)/(R+S)>0,
    theta=S/R>0, lambda=u1/u3>0.

For EACH actual cell use its own scale, with the accepted same-cell source normalization

    s_j=u_j|eta_j/delta_j|,
    M_j=|r_j|/u_j^3=|eta_j|^4/|delta_j|^3,
    beta_j=b_j/u_j=z_j|eta_j/delta_j|,
    q_j=I_j/delta_j, alpha_j=q_j+42.

The outer source-ratio provider gives alpha1,alpha3>0, and i balance then forces alpha2>0 as well. The exact normalized balance equations are

    u2/u3=(lambda+theta)/(1+theta),
    M3=theta lambda^3 M1,
    M2=[(1+theta)^4/(theta(lambda+theta)^3)] M3,
    alpha2=(lambda alpha1+theta alpha3)/(lambda+theta). (1)

The last identity follows from i_j=k_j q_j. In particular the weights are the actual quartic weights, not the cubic weights R,S used in the proportional special case. Scales, amplitudes and ratios are still functions of the same d,z tuples.

## The full clock moment and G7 fix the two effective distances

Let D1=ell1+b2 and D2=ell2+b3, with actual ordinary gaps ell1,ell2 strictly positive. The quartic chronological moment gives R D1=S D2. The exact inherited area identity gives

    G7=-(4/3)D1 R(R+S)+6 Aarea,
    Aarea=-R k1-(R+S)k3
          =u1 R^2+u3 S(R+S).

Consequently the clock moment and G7=0 require the unique effective distances

    D1=(9/2)u3[theta+lambda/(1+theta)],
    D2=(9/2)u3[1+lambda/(theta(1+theta))].            (2)

Using b2=u2 beta2 and b3=u3 beta3, strict positive gaps are therefore equivalent to the two exact supplied-source inequalities

    beta2<J1(theta,lambda)
      =(9/2)[1+theta^2/(lambda+theta)],
    beta3<J2(theta,lambda)
      =(9/2)[1+lambda/(theta(1+theta))].              (3)

For a supplied actual triple satisfying (1), equations (3) are necessary and sufficient for UNIQUE positive gap choices solving just the chronological quartic moment and G7 equation: subtract b2 and b3 from the distances in (2). This is not sufficiency for every forest coefficient or any exact response return.

## A physical middle restriction and the missing implication

Because alpha2>0, the separately reviewed actual-middle bound beta2>K, K=9/4+3sqrt(3), still applies. Combining it with (3) gives the necessary ratio restriction

    lambda+theta<(9/2)theta^2/(K-9/2).               (4)

It does not force lambda=1. The actual normalized middle amplitude lower bound also remains

    M2>E(54+alpha2)^3, E=625/839808.

The late branch depends on the NEW J2. If J2<=9, the inherited positive-t outer branch beta>9 is excluded, so the late cell must use negative t and its same-source alpha3>8beta3. If J2<=27/4, the reviewed 4N+9T polynomial guard additionally forces p3=d3/z3<3. These consequences require the stated new bounds; the corresponding proportional late-strip constants do not apply automatically to every lambda.

In the special case lambda=1, (1)-(3) reduce exactly to the earlier proportional normalized system. For lambda unequal to one, both the cubic amplitude factor and weighted excess change, and the late clock bound can widen. No physical cell tuple satisfying (1),(3),(4) is constructed here, and no impossibility theorem for all such tuples is established.

The next bounded mathematical obligation is to compare the actual source-reachable triples against these simultaneous equations, retaining lambda and the changed weights. It is not valid to substitute independent M,beta,alpha coordinates or to carry the proportional amplitude comparison over unchanged. Other coefficient signs, longer words, other scales/grades, exact finite-epsilon/full-prefix equality and the original effective-stopping/rival endpoint remain open.
