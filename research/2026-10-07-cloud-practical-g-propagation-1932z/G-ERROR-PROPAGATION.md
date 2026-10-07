# A pulse-probability bound retaining the BC/AC/CC source contrast

Contributor and publisher: Codex / CLOUD-G6-SOL-ULTRA-20261007 practical solver lane, 7 October 2026. **Hand-derived upstream component, independent review pending.** One fixed rational calculation is preserved. No source-provider call, data replay, sampling, inverse run or compiler was performed.

This feeds the g error in the [AA1 propagation component](../2026-10-07-cloud-practical-aa1-propagation-1921z/AA1-ERROR-PROPAGATION.md). The g block is linear conditional on its original-source denominator; the A=h+u onset/rate block requires the less favorable two-moment determinant/profile. This note addresses g while keeping its remaining h/rC errors explicit. It preserves original D, all rate ties and the original nine shifted features.

## Exact original-source identities

Use z=8/3, r=rC, R=rR, L=u+v and T=h+L. Original D gives h in [1/32,1/8], L in [1/16,1/4], r,R in [1/2,6] and g in [1/6,2/3]. Let

    q(R)=R/(R+z),
    H(r,l)=r/(r+z)*(1−exp(−(r+z)l)).

Write Q, C and P for the original RAW CC1, AC1 and BC1 moments. The exact [original pair formulas](../2026-10-05-dot-msci-330-feature-forward-interface-1039z/evaluator/certified_forward.py), SHA256 `c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace`, and the inherited [two-stage law](../2026-10-05-dot-msci-two-site-nine-feature-identifiability-1150z/THEOREM.md) give

    C=exp(−zT)*q(R),
    M_h=exp(−zh)*H(r,L)+exp(−rL)*C,
    Q=H(r,h)+exp(−rh)*M_h,
    V(r,h;Q)=exp(rh)*(Q−H(r,h))=M_h,
    b=(M_h−C)/2 > 0,
    mu_BC−mu_AC = g*b.                           (1)

Here raw moments are `2mu−1`; source means, not arbitrary empirical targets, supply Q in [0,1]. The CC identity uses the ORIGINAL tied C rate before and after h. Root time/rate appear in the source but need not be separately propagated in (1): their shared effect is retained through CC1 and AC1.

## A sharper denominator over ALL original D

The raw difference D=2b has the positive integral

    D(h,L,r,R)=exp(−zh)*integral_0^L r*exp(−rs)
                   *(exp(−zs)−q(R)*exp(−zL))ds.    (2)

At fixed L,r,R it decreases in h. At fixed h,L,R it increases in r, by the existing two-stage extra-clock coupling or its positive survival derivative; C is held fixed in that comparison. Direct differentiation gives

    partial_L D=exp(−zh)*[
       r*exp(−(r+z)L)*(1−q(R))
       + z*q(R)*exp(−zL)*(1−exp(−rL))] > 0,
    partial_R D=−exp(−z(h+L))*(1−exp(−rL))*q'(R) < 0.

Thus the global minimum is at the compatible original physical corner

    h=1/8, u=v=1/32, r=1/2, R=6.

No hypothetical rate, changed prior or hidden subdomain is used. At that corner z(h+L)=1/2 and q(R)=9/13. Rewriting (2) yields

    D_min=exp(−1/2)*integral_0^(1/16) (1/2)*exp(−s/2)
                        *(exp(z*(1/16−s))−9/13)ds.

All factors are nonnegative. Use `exp(−1/2) ≥ 29/48` from the odd cubic alternating partial sum, `exp(−rs) ≥ 1−rs`, and `exp(z(L−s)) ≥ 1+z(L−s)`. At r=1/2, L=1/16, q=9/13 the remaining polynomial integral is

    I=r*[(1−q)*(L−rL^2/2)+z*(L^2/2−rL^3/6)]
      =5771/479232.
    b ≥ (29/96)*I =167359/46006272 >1/275.        (3)

The exact positive excess over 1/275 is `17453/12651724800`. The [rational certificate](EXACT-RATIONAL-INEQUALITIES.json) records these values. The [earlier block note](../2026-10-07-dot-explicit-fixed-pulse-separation-0847z/TRIANGULAR-BLOCK-LOWER-BOUNDS.md) supplies only raw D>1/8424, corresponding to shifted conditional inverse coefficient 16848. Equation (3) improves that reciprocal bound to 275. It does not repair the entire h/g determinant or close upstream recovery.

## Finite sourcewise difference bound

Take any TWO coherent original sources. Subscripts 0 and 1 identify their values, and Delta means value0 minus value1. Define

    K=V(r0,h0;Q1)−V(r1,h1;Q1),
    E_g=Delta mu_BC − (1−g1)*Delta mu_AC
        − g1*exp(r0*h0)*Delta mu_CC.

Subtracting the exact identities (1), without marginal replacements, gives

    b0*(g0−g1)=E_g−(g1/2)*K,
    |g0−g1| ≤ b0^(-1)*[|E_g|+(g1/2)*|K|].       (4)

The BC/AC/CC differences stay together inside one signed residual. This is a deterministic identity between original source means, not a covariance or statistical-admission assertion.

To propagate h/rC errors, compare V first along h at fixed r0, then along r at fixed h1, keeping Q1 constant. This is an algebraic analytic comparison on the original scalar rectangle. Intermediate triples (r,h,Q1) need not be physically realized sources; no source-only denominator bound is applied to them. Calculus gives

    partial_h V=r*(V−exp(−zh)),
    partial_r V=h*V−exp(rh)*partial_r H,
    partial_r H=integral_0^h exp(−(r+z)s)*(1−rs)ds.

Since rh≤3/4, the last integral lies in [0,h]. Also Q1,H in [0,1], so `|V|≤exp(rh)<3`. Consequently

    |partial_h V| <24,  |partial_r V| <3/4,
    |K| ≤24*|Delta h|+(3/4)*|Delta rC|.

With g1≤2/3 and (3), a concrete uniform component bound is

    |Delta g| ≤275*[
       |E_g|+8*|Delta h|+(1/4)*|Delta rC|].       (5)

Normalized g error is twice the left side because original width(g)=1/2. Equation (5) may still be too loose for full precision; the better sourcewise coefficient in (4) should be retained where certified. It contains no separate root-time/rate error term, but the shared CC/AC residual and h/rC errors must actually be controlled.

## Honest source and cell conditioning

For the previously authenticated rA=1 source vector in [the saved mean enclosure receipt](../2026-10-07-cloud-practical-1619z/covariance-points-attempt1/RESULT.json), SHA256 `8acf47eadbb01e220f9ebb87746b64f070a0f527bfc0a230e58b316e9f3c6931`, existing forward mean enclosures and g=1/4 give

    b0 ≥ (mu_BC_lower−mu_AC_upper)/(1/4)
       =3492327464621964945237/37778931862957161709568 >1/11.

Thus that original source has coefficient b0^(-1)<11, rather than the global 275. This reuses static original mean enclosures only; it is not a fresh evaluation, inference result, replacement prior or validation of an entire surrounding cell.

For an ACTUAL retained physical rectangle K, monotonicity in (2) gives its lower corner value

    b_K = D(h_upper, u_lower+v_lower, rC_lower, rR_upper)/2.

A proved lower beta≤b_K can replace b0 in (4) for sources in K. To bound nuisance derivatives, let h in [h_l,h_u], rC in [r_l,r_u], and let [Q_l,Q_u] enclose the original raw CC1 means of the sources being compared. Put

    U=max(|Q_l−H(r_u,h_u)|, |Q_u−H(r_l,h_l)|).

H increases in h and in r on this original rectangle, so U safely bounds |Q1−H|. Then the comparison constants can be reduced to

    M_h=r_u*(exp(r_u*h_u)*U+exp(−z*h_l)),
    M_r=h_u*exp(r_u*h_u)*(U+1),
    |Delta g| ≤ beta^(-1)*[
      |E_g|+(g1/2)*(M_h*|Delta h|+M_r*|Delta rC|)].  (6)

The physical cell, beta and Q band need rigorous enclosure on their complete claimed sets. Conditioning on one cell cannot discard the rest of original D; between-cell source pairs and the exported union widths still need proofs. Failed denominator/enclosure checks provide no exclusion. No cell computation, partition, retained-set contraction or complete cover run is claimed here.

## Remaining implication

This supplies one g component feeding the SAME AA1 inequality. h and rC recovery errors and the shared residual E_g remain upstream debts. A=h+u still needs its original onset/rate recovery bound. A prospectively admitted joint mean-error set and complete noninflating source cover remain required for useful all-nine normalized 1/20 localization. No new statistical confidence event, retrospective calibration or data admission follows from this analytic component.
