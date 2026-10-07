# Tied-B finite rate recovery with the original shared means

Contributor and publisher: Codex / CLOUD-G6-SOL-ULTRA-20261007 practical solver lane, 7 October 2026. **Hand-derived component; independent review pending.** No arithmetic job, numerical scan, provider call, observation replay, sampling, inverse run or compiler occurred. This completes another conditional rate block, not the original whole-D useful-precision goal.

Keep original D: h,u,v in [1/32,1/8], all five rates in [1/2,6], and g in [1/6,2/3]. Put A=h+u, T=h+u+v, b=rB, d=rAB, r=rC, R=rR and z=8/3. The SAME b applies before and after the pulse. The original nine shifted Bernoulli means and within-locus dependence are unchanged.

## Eliminate the separate downstream rate errors

Use the [frozen original source body](../2026-10-05-dot-msci-330-feature-forward-interface-1039z/evaluator/certified_forward.py), SHA256 `c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace`. Write H(b,t)=b/(b+z)*(1−exp(−(b+z)t)), beta=1−g, alpha=beta², and P,Q,C for RAW AB1, BC1, AC1 respectively. Define the existing raw two-stage continuations

    Z=(P−g*C)/beta,
    V=(Q−beta*C)/g.

These depend on the original source and are independent of b. Grouping the original BB routing formula gives

    rawBB=H(b,h)+exp(−bh)*[
       alpha*(exp(−zh)*H(b,u)+exp(−bu)*Z)
       +g²*V+2g*beta*C].

The SAME tied rate permits H(b,h)+exp(−(b+z)h)*H(b,u)=H(b,A). Thus

    rawBB=alpha*H(b,A)+(1−alpha)*H(b,h)
             +beta*exp(−bA)*(P−g*C)
             +g*exp(−bh)*(Q+beta*C).            (1)

This retains rAB, rC and the root contribution through the SAME AB/BC/AC means. It supplies no independent replacement observations and no separate fitted rates. Their uncertainty enters a shared residual below, with A,h,g errors explicit.

## A stronger conditional rate derivative on original D

For this calculation vary ONLY b, keeping the other original source coordinates fixed. This stays in Cartesian D, and P,Q,C remain unchanged by the original pair formulas. Put

    U=(g²*V+2g*beta*C)/(1−alpha),
    Phi_b(t,X)=H(b,t)+exp(−bt)*X,
    rawBB=alpha*Phi_b(A,Z)+(1−alpha)*Phi_b(h,U). (2)

The original continuation formula gives Z=exp(−zA)*J_A with J_A≤9/13: its J_A is a convex combination of d/(d+z) and R/(R+z). Likewise V=exp(−zh)*J_C with J_C≤9/13. Since C≤exp(−zh)*(9/13), the positive normalized mixture defining U gives U=exp(−zh)*J_h with J_h≤9/13. All continuations are independent of b. Both 1−alpha and the normalizing denominator in U are positive because g≥1/6.

For t≥t_min and J≤9/13, the [AA1 derivative calculation](../2026-10-07-cloud-practical-aa1-propagation-1921z/AA1-ERROR-PROPAGATION.md) applies directly to Phi_b(t,exp(−zt)J):

    partial_b[(1+Phi_b)/2]
      =(1/2)*[z*integral_0^t s*exp(−(b+z)s)ds
                +t*(1−J)*exp(−(b+z)t)]
      ≥(3/169)*(1−exp(−(26/3)*t_min)).          (3)

This is scalar calculus, not a feedback assumption about recovered rA. With A≥1/16 the accepted lower bound is >1/135. With h≥1/32, exp(13/48)>1+13/48 gives

    (3/169)*(1−exp(−13/48))>3/793.

Because alpha≥1/9 and 1/135>3/793, the convex derivative mixture in (2) yields

    partial_b mu_BB
      >(1/9)*(1/135)+(8/9)*(3/793)
       =4033/963495>1/240.                     (4)

The last rational comparison has positive cross-product difference 4425. The [older pre-pulse-only bound](../2026-10-07-dot-explicit-fixed-pulse-separation-0847z/TRIANGULAR-BLOCK-LOWER-BOUNDS.md) was >1/4608. The new uniform inverse factor 240 retains the positive continuation and stay/stay contribution. It is a lower bound, not a claimed exact minimum. Sourcewise derivative values in (2)–(3) may be stronger but were not evaluated here.

## Exact shared residual and a safe finite comparison

For any two ORIGINAL source vectors let Delta=value0−value1. First swap ONLY b0 to b1 in source0. This preserves original D, all rate ties and P0,Q0,C0. Let D_B denote the average derivative partial_b mu_BB along that original b segment; (4) gives D_B>1/240, including equal endpoint rates.

For the remaining algebra let Psi_b(A,h,g;P,Q,C) be one half of one plus the right side of (1). The differences in observed means at fixed A0,h0,g0,b1 have the exact coefficients in

    E_B=Delta mu_BB
          −beta0*exp(−b1*A0)*Delta mu_AB
          −g0*exp(−b1*h0)*Delta mu_BC
          −g0*beta0*(exp(−b1*h0)−exp(−b1*A0))*Delta mu_AC.

Using raw moments P=2mu_AB−1, Q=2mu_BC−1 and C=2mu_AC−1 gives the finite identity

    E_B=D_B*Delta b+N,
    N=Psi_b1(A0,h0,g0;P1,Q1,C1)
        −Psi_b1(A1,h1,g1;P1,Q1,C1).             (5)

All three original mean differences remain inside ONE signed residual. No separate rAB, rC, root-rate or root-time error term is introduced. Their original-source effects remain in these means and in A/h/g, rather than being assumed absent.

Compare N along the straight path in ORIGINAL physical (h,u,v,rates,g) coordinates, with A_s=h_s+u_s, holding the raw constants P1,Q1,C1 and b1 fixed in the ALGEBRAIC function Psi. Mixed values need not be source means; the next partial bounds are proved for every P,Q,C in [0,1]. No source-only derivative lower bound is used on that nuisance path.

Direct differentiation gives

    Psi_A=(b*beta/2)*exp(−bA)*(beta*exp(−zA)−P+g*C),
    Psi_h=(b*g/2)*exp(−bh)*((2−g)*exp(−zh)−Q−beta*C),
    Psi_g=beta*(H(b,h)−H(b,A))
       +(1/2)*[−exp(−bA)*P+exp(−bh)*Q
                   +(2g−1)*(exp(−bA)−exp(−bh))*C].

The first bracket has absolute value at most 1, since its upper endpoint is ≤beta+g=1 and lower endpoint is ≥−1. The second has absolute value at most 2−g. Original A≥1/16, h≥1/32 and b≤6 imply

    |Psi_A|≤(5/2)*exp(−3/8)<20/11,
    |Psi_h|≤(8/3)*exp(−3/16)<128/57.            (6)

Here b*exp(−bA_min) and b*exp(−bh_min) increase up to 6; exp(x)>1+x gives the rational fallbacks. For Psi_g, original u=A−h≤1/8 and beta≤5/6 give

    beta*|H(b,h)−H(b,A)|≤beta*b*u≤5/8.

Also |−exp(−bA)P+exp(−bh)Q|≤1, |2g−1|≤2/3, and exp(−bh)−exp(−bA)≤b*u≤3/4. The remaining half-bracket is bounded by 3/4. Therefore

    |Psi_g|≤11/8.                              (7)

Along the stated original physical path, A=h+u and u≤1/8 remain true. Finite integration yields the exact signed nuisance expression and a uniform fallback

    N=integral_0^1 [Psi_A*Delta A+Psi_h*Delta h
                                  +Psi_g*Delta g]ds,
    |N|≤(20/11)*|Delta A|+(128/57)*|Delta h|
                                       +(11/8)*|Delta g|.

Finally (5) gives

    Delta b=(E_B−N)/D_B,
    |Delta rB|≤240*[
        |E_B|+(20/11)*|Delta A|+(128/57)*|Delta h|
                                             +(11/8)*|Delta g|]. (8)

Source/cell implementations should retain E_B−N with its dependencies before taking magnitude and rigorously bound every complete comparison path. No such enclosure or contraction was executed.

## Remaining endpoint obligations

This finite tied-B block uses only already upstream A,h,g and the original BB/AB/BC/AC means. It does not use rA recovery, estimate different B rates on the pulse sides or create a circular A/B dependency. The [finite auxiliary A/rAB candidate](../2026-10-07-cloud-practical-a-finite-comparison-2047z/A-FINITE-COMPARISON.md), [root](../2026-10-07-cloud-practical-root-propagation-2018z/ROOT-ERROR-PROPAGATION.md), [CC1](../2026-10-07-cloud-practical-cc1-propagation-1948z/CC1-ERROR-PROPAGATION.md), [h](../2026-10-07-cloud-practical-h-propagation-2027z/H-ERROR-PROPAGATION.md), [g](../2026-10-07-cloud-practical-g-propagation-1932z/G-ERROR-PROPAGATION.md) and [AA1](../2026-10-07-cloud-practical-aa1-propagation-1921z/AA1-ERROR-PROPAGATION.md) retain their exact separate scope and review status.

Normalized rB error is 2/11 times (8), using the ORIGINAL rate width 11/2. Original u=A−h and v=T−A still require their shared finite differences. A complete quantitative sourcewise composition, useful prospectively admitted joint mean-error set, all source/uncertainty coverage and exported ALL-nine normalized union widths ≤1/20 remain open. No data admission or retrospective confidence is added, and no full solver success follows from these coarse conditional constants.
