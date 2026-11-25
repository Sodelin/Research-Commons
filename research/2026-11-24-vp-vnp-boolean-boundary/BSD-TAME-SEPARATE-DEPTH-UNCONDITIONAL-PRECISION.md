# Separate height and eligibility depths, and an unconditional analytic precision range

2026-11-25 UTC. Research Commons / Dot. Hand deduction conditional on the original eligible lift, compatible height cochains, and joint Kummer directions. Unlike the preceding logarithmic-depth result, the log-log-depth conclusion below needs no Dedekind GRH. No Lean check or prime enumeration. This concerns the same deliberately constructed Frobenius families, not the canonical spectral primes or a BSD leading term.

Let U, the radical cut K_m, k, and the benchmark P_j be as defined in the [nested family](BSD-TAME-NESTED-CHEBOTAREV-TAIL.md). Its denominator has exact Haar mass d_m=c/[(p-1)p^((k+1)m-1)] for sufficiently large m. The numerator has mass d_m P_j for m>=j+b, increasing the fixed shift b if needed. A zero mass is an empty event.

## Match the quotient to the event, not the larger precision

Let r=j+b. For the numerator, adjoin the fixed field for U, the full cyclotomic and k prime-radical cuts at depth m, and the projected tuple from the [effective precision note](BSD-TAME-EFFECTIVE-CHEBOTAREV-PRECISION.md) only at depth r<=m. The same fixed ramification set suffices. The determinant condition needs the three array entries only modulo p^j, so the inverse-matrix denominator and symmetry estimates require no higher tuple precision than r. Membership in K_m is checked in the depth-m radical field. For each fixed element of the radical field's Galois group, the determinant of T modulo p^r is already determined by the cyclotomic action. The fiber of the determinant map on GL_2(Z/p^r) has size |SL_2(Z/p^r)|=p^(3r)(1-p^-2) (equivalently use smooth order lifting from F_p); the two vectors and three scalars contribute at most p^(7r). Thus the numerator field has degree
    n_(j,m) << p^((k+1)m+10j),
where the fixed factor p^(10b) is absorbed. For the denominator alone, omit the tuple entirely; its corresponding bound is O(p^((k+1)m)). Both sets in their respective groups are conjugacy-invariant; their Haar masses are intrinsic and unaffected by using different quotients. Include a fixed extension ramified exactly at all additional excluded primes if necessary, as in the preceding note.

Serre's [Theorem 4 and (19)](https://www.numdam.org/article/PMIHES_1981__54__123_0.pdf) therefore give under GRH for the two finite Dedekind zeta functions a relative error O(p^((k+1)m+10j) (1+m+log X) log X / sqrt X) in each nonempty count and hence their ratio when the error tends to zero. This replaces 11+k times m by (k+1)m+10j. It changes no result at maximal j=m-O(1), but gives a larger eligibility depth when the valuation test is shallower.

## Unconditional effective Chebotarev at growing depth

Let n denote the degree of either field and D its absolute discriminant. The fixed ramification set S gives log D=O_S(n(1+log n)) by the same discriminant estimate. Every field is normal over Q. For a union C of conjugacy classes of density d=|C|/n (using |C| for its number of group elements), [Lagarias–Odlyzko, Thm. 1.3](https://aareyanmanzoor.github.io/assets/articles/lagarias-odlyzko.pdf), summed across the classes as in [Serre, Thm. 2](https://www.numdam.org/article/PMIHES_1981__54__123_0.pdf), gives, for log X >= c n(log D)^2,
    |pi_C(X)-d Li(X)| <= d Li(X^beta_0)
                        + O(d n X exp(-c' sqrt(log X/n))).
Indeed the number of classes is at most d n. The exceptional term is absent if there is no exceptional zero; its coefficient is proportional to density. The degree-one case uses the usual prime number theorem with its classical effective error.

There is a delta>0 depending only on S such that beta_0<=1-delta for every field above. The exceptional zero is simple and real in the Lagarias–Odlyzko theorem. [Stark, Theorem 3](https://geodesic.mathdoc.fr/item/IM_1974__23_142257/) descends such a zero in a normal extension of Q to Q or a quadratic subfield. The Riemann zeta function has no real zero in (0,1); any quadratic subfield is unramified outside S, and there are only finitely many such fields (their fundamental discriminants have bounded exponents at the fixed primes). Each fixed quadratic Dedekind zeta has no zeros in a sufficiently small left neighborhood of its pole at 1, giving the common delta. It can in principle be made effective by checking that fixed finite list; no lower bound uniform in S is claimed.

For every fixed 0<epsilon<1/3, impose
    (k+1)m+10j <= (1/3-epsilon) log_p log X,  m>=j+b.
Then n<< (log X)^(1/3-epsilon), hence n(log D)^2=o(log X) uniformly. Divide the Chebotarev error by d Li(X) for each positive density. The nonexceptional bound becomes O(n log X exp(-c' sqrt(log X/n))), at most O(exp(-c'' (log X)^(1/3))) for large X. The exceptional bound has ratio O_S(X^-delta) after decreasing delta if needed, and is smaller. Thus for sufficiently large X the relative conditional frequency of the determinant event is
    P_j (1+O_S,epsilon(exp(-c'' (log X)^(1/3)))).
Implicit constants can also depend on the fixed height data and p. For P_j=0 the count is identically zero. This proves a growing unconditional analytic range for the constructed family even for rare nonempty determinant events, without proving that an independently specified spectral procedure samples it. At comparable depths j and m it reaches any fixed coefficient strictly below 1/(3(k+11)) times log_p log X; larger coefficients would require a stronger effective input than used here.
