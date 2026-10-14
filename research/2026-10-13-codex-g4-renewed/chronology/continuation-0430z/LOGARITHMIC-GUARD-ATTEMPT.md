# Exact obstruction to resource-only logarithmic Fatou and window averaging

Contributors: Codex lead G4 researcher (the zero-relative-entropy construction, window bound and summed-reservoir strengthening); Codex / logarithmic_guard (independent hand audit, prior search and written proof), 14 October 2026.

Status: **HAND theorem / obstruction to a specified inference.** The construction uses strict unequal finite cells, one fixed tuple per cell across arities, zero binary relative entropy, and the exact two resource budgets of one fixed finite strict target. It does **not** match that target's all-arity diagonals. It therefore does not refute finite persistence under the full target-matching premise, construct admitted exact-prefix rivals, or close G4. No numerical, compiler, integration, Lean or Rust verification is claimed.

## 1. Precise conclusion and prior boundary

The accepted [quadratic survival/resource proof](../continuation-0350z/UNEQUAL-ALL-ARITY-QUADRATIC-SURVIVAL-RESOURCE.md) and [linear entropy resource proof](../continuation-0350z/UNEQUAL-COUNTABLE-LINEAR-ENTROPY-RESOURCE.md), with their [whole-source review](../continuation-0350z/RESOURCE-WHOLE-SOURCE-REVIEW.md), justify the exact resource identities for an auxiliary compatible carrier matching every diagonal of one fixed finite strict target. They also justify absolute convergence at each fixed arity of

    r_i(n) = -log d_n(B_i) - kappa_i lambda_n + beta_i n,
    beta_i = kappa_i - ell_i,
    lambda_n = n(n-1)/2.

Each fixed strict cell has `r_i(n)=(1/2)log n+O_i(1)`. Under the full target premise, the sum is `(L/2)log n+O(1)`, where L is the fixed target's strict cell count. A proposed logarithmic Fatou step would need a summable lower correction, or another sign/averaging result retaining that full premise.

**Theorem.** Positive triple survival, summable `kappa_i` and `ell_i`, and even their exact equality to the two budgets of one fixed finite strict target do not imply that there are nonnegative summable constants `c_i` with

    r_i(n)/log n >= -c_i                    for every n>=N0, every i,  (1)

for any fixed N0>=2. They also do not imply a summable additive correction `r_i(n)+c_i>=0`. The same obstruction survives averaging within a fixed multiplicative arity window. More strongly, a fixed countable family with these budgets has summed residual `R(m)<=-i log m` on infinitely many such windows, although every fixed cell has positive half-logarithmic asymptotics. This remains true when **every cell has `g_i=alpha_i`, hence `KL(alpha_i||g_i)=0`**. It is not caused by boundary factors or accumulated coin bias.

Commons prior checked: the accepted exact resources above; [finite-unequal/countable-equal normalization](../continuation-2110z/UNEQUAL-RESOURCE-NORMALIZATION.md); the completed finite-unequal phase-removal scope recorded in its continuation; the earlier [bounded paired log-score obstruction](../../../2026-10-09-dot-reviewed-guard-boundaries-1615z/g4/EXACT-BOUNDED-LOG-GUARD-OBSTRUCTION.md); and the calibrated chronological mixed-tail notes. The bounded score obstruction concerns a different finite linear score architecture. The completed equal-tail meromorphic persistence argument does not require, or supply, the general unequal lower envelope attacked here. No historical novelty is claimed.

## 2. One exact strict cell with zero relative entropy

Fix an integer N>=4 and kappa>0. Set

    alpha=g=1/(2N),     q=1-g,
    a=kappa/alpha=2 kappa N,
    b=kappa/(1-alpha)=2 kappa N/(2N-1).

Both arms are finite positive and unequal; the coin is interior. Directly,

    b/(a+b)=alpha,
    ab/(a+b)=kappa,
    KL(alpha||g)=0,
    ell=kappa/2,       beta=kappa/2.                       (2)

The parameters describe one cell and are kept fixed when its arity varies. For J~Bin(N,g), Bernoulli's inequality gives

    Pr(J=1) = (1/2)(1-1/(2N))^(N-1) >=1/4.

On this routing event the long arm carries one root and has zero pair exposure. Therefore the exact natural-cell sum gives

    d_N >= (1/4) exp[-b lambda_(N-1)].

Using (2),

    r(N) <= log 4 + b lambda_(N-1) - kappa lambda_N + kappa N/2
         = log 4 - kappa N(N-2)/[2(2N-1)]
         <= log 4 - kappa N/7.                            (3)

The last inequality is equivalent to N>=4. This is a routing-term bound, not a moving-parameter saddle approximation.

Meanwhile change-of-measure Jensen, already accepted in the linear resource proof, becomes especially simple because `g=alpha`:

    -log d_n <= kappa lambda_n.

In particular the exact triple hazard obeys

    xi=-log d_3 <=3 kappa.                                (4)

Thus a large negative residual at N costs only a small summable quadratic/triple budget. The small arm balance delays the fixed-cell saddle regime.

## 3. An exact uniform moving-window bound

Keep the single cell of section 2 fixed, and let N<=m<=floor(3N/2). Its exact one-long-arm-root routing probability satisfies

    Pr(J_m=1) = [m/(2N)] q^(m-1)
              >=(1/2)[1-(m-1)/(2N)] >=1/8.

Consequently

    r(m) <= log 8 + kappa [m^2-2(N+1)m+4N]/[2(2N-1)].   (5)

The numerator is convex in m. At m=N it equals `-N^2+2N`; at the continuous upper endpoint m=3N/2 it equals `-3N^2/4+N`. Both are at most `-N^2/2` for N>=4. Therefore throughout the whole window,

    r(m) <= log 8 - kappa N/8.                          (6)

The same cell also satisfies at every integer m>=2

    r(m) <= kappa m/2,                                  (7)

by the zero-relative-entropy Jensen bound `-log d_m<=kappa lambda_m`.

## 4. One fixed countable family with a summed negative reservoir

Choose the positive budgets

    kappa_i=99*100^(-i),       i>=1.

Then `sum_i kappa_i=1` and `sum_(j>i) kappa_j=kappa_i/99`. We now choose one fixed integer N_i>=4 per cell recursively, and then retain its parameters at every arity:

    alpha_i=g_i=1/(2N_i),
    a_i=2 kappa_i N_i,
    b_i=kappa_i/(1-alpha_i).

For every earlier fixed cell j<i, the accepted strict-cell saddle result supplies finite constants `C_j>=0` and integer thresholds H_j such that

    r_j(m) <= (1/2)log m+C_j       for every m>=H_j.      (8)

The constants depend only on that already chosen cell. Choose N_i beyond all previous thresholds, with `N_i>2N_(i-1)` when i>1, and large enough that

    (31/264) kappa_i N_i
        >= log 8 + [(3i-1)/2]log(3N_i/2) + sum_(j<i) C_j. (9)

Such an integer exists: the left side grows linearly in N_i with fixed positive coefficient, whereas the right side grows logarithmically. This recursive definition is noncircular. After choosing N_i and hence B_i, obtain its C_i and H_i for subsequent steps. There is one fixed tuple for each i, not an arity-specific parameter fit.

Equations (2) and (4) give

    sum_i kappa_i=1,
    sum_i ell_i=1/2,
    sum_i |beta_i|=1/2,
    sum_i xi_i<=3.                                      (10)

Take C=1 and fix target T to have ordinary duration C_T=1 and **one** balanced strict cell `a_T=b_T=2, g_T=1/2`. Its budgets are exactly

    C_T+kappa_T=2=C+sum_i kappa_i,
    C_T+ell_T=3/2=C+sum_i ell_i.                         (11)

The countable diagonal product has `D_3>=exp(-6)>0`; the accepted all-arity survival bound makes it positive at every fixed arity. Its residual series is absolutely convergent there, by the same fixed-arity hazard and resource estimates used in the accepted linear proof. Denote that sum by `R(m)=sum_i r_i(m)`.

Fix i and an integer m in `[N_i,floor(3N_i/2)]`. The earlier cells obey (8). The ith cell obeys (6). The later cells obey (7), which is summable, and consequently

    sum_(j>i) r_j(m) <= (m/2)(kappa_i/99)
                      <= kappa_i N_i/132.

Adding these three bounds gives

    R(m) <= [(i-1)/2]log m + sum_(j<i) C_j + log 8
              - (31/264) kappa_i N_i
         <= -i log m,                                  (12)

where (9) and `log m<=log(3N_i/2)` prove the last inequality. Thus

    R(m)/log m <= -i

throughout infinitely many disjoint multiplicative windows. In particular `liminf_(n->infinity) R(n)/log n=-infinity`. Nevertheless every individual fixed strict factor satisfies `r_j(n)/log n ->1/2`.

Any probability-weighted average of `R(m)/log m` over the ith window is at most -i. This refutes resource-only proposals to recover a positive logarithmic factor count by this fixed-window averaging. It does not exclude a transform that uses the full target identity and additional analytic structure.

This family also proves the factorwise lower-envelope obstruction: (9) implies `kappa_i N_i/log N_i` grows at least proportionally to i, and (6) then gives `r_i(N_i)/log N_i ->-infinity`. A summable lower correction in (1), or a summable additive correction, is impossible. The uniform window bound proves the same for factorwise window averages.

Every finite truncation can retain exactly (11): after the first M cells, append one balanced strict cell with kappa equal to `sum_(j>M) kappa_j=100^(-M)`, arms `2*100^(-M)` and fair coin, and retain C=1. For M>=i, the cells later than i plus this replacement cell still have total kappa `kappa_i/99` and satisfy (7), so their finite summed residual obeys (12) on the ith window. These are finite actual strict words of unbounded cell count with the fixed target's two resource budgets. They are **not** claimed to match any finite legal observation prefix of T.

## 5. Exact remaining gate

The theorem blocks a precise inference: the accepted quadratic/linear budgets, even with zero relative entropy and exact numerical target matching, cannot by themselves make the logarithmic summands suitable for Fatou or dominated convergence. Pointwise positive logarithmic limits and fixed-arity absolute convergence do not control the moving negative part.

The full all-arity identity

    sum_i r_i(n)=(L/2)log n+O(1)

could impose additional collective rigidity on a carrier. No counterexample here satisfies that identity for the fixed target. Conversely, one cannot use that identity to discard each factor's negative moving window without a new argument. Here the summed bound (12) rigorously controls earlier positive terms and the entire later tail. It shows that numerical resource matching cannot prevent a superlogarithmic summed negative reservoir. The constructed family therefore fails the full fixed-target diagonal identity; it is not a counterexample to that stronger premise.

The countable carrier remains an AUXILIARY analysis object. The finite truncations are actual strict words, but resource equality is weaker than exact legal topology-prefix matching. General finite persistence under the full diagonal-matching premise remains open, and finite persistence would still leave the weak-reservoir chronology and original-observation bridge. Full G4 still requires a finite legal topology certificate against every finite unknown-size rival, or exact all-prefix admitted rivals for one fixed strict target.

Verification: independent hand check of all displayed cell parameters, routing probabilities, exponent algebra, convex endpoint bounds, summability and quantifiers. No program was executed to verify a universal mathematical claim. Next proof action: exploit the full target identity to control collective cancellation or analytic continuation of this extreme-balance tail; a resource-only logarithmic normalization cannot supply that step.
