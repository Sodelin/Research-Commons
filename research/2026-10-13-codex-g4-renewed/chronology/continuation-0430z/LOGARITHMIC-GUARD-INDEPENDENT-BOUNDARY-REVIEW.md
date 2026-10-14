# Independent review of the resource-only logarithmic obstruction

Reviewer: Codex / boundary_carrier, delegated by the G4 lead. 14 October 2026.

**Verdict: SCOPED HAND ACCEPTANCE; no mathematical defect located.** This is an independent audit of [LOGARITHMIC-GUARD-ATTEMPT.md](LOGARITHMIC-GUARD-ATTEMPT.md), frozen SHA256 `228d99931772ee2433a38d925ab166236ff3a4579f5372218774f7847a321ce6`. The reviewer did not coauthor that construction. The lead is a coauthor; this review supplies the additional independent check requested by the lead. No Git action, compiler, simulation, integration, numerical theorem check, formal verification, or historical-novelty assessment was performed.

The accepted conclusion is an obstruction to deriving a logarithmic lower envelope or positive logarithmic factor count from the two scalar resource budgets alone. The construction does not match the target's full all-arity diagonal identity or any arbitrary finite legal observation prefix. It is not a boundary-source rival or a counterexample to the full finite-persistence premise.

## 1. Exact one-cell algebra

For fixed N>=4 and kappa>0, the specified parameters have

    a=2 kappa N,  b=2 kappa N/(2N-1),
    alpha=g=1/(2N),  ab/(a+b)=kappa.

Both arms are strictly positive finite; the coin is interior. Arm balance equals the coin, so relative entropy is exactly zero, ell=kappa/2 and beta=kappa/2. Every subsequent arity uses this one fixed tuple.

At n=N the exactly-one-long-arm-root probability is

    (1/2)(1-1/(2N))^(N-1) >=1/4,

by Bernoulli's inequality. Its exposure is b lambda_(N-1), since a single long-arm root has no pair exposure. The normalized exponent equals

    b lambda_(N-1) - kappa lambda_N + kappa N/2
      = -kappa N(N-2)/[2(2N-1)].

The comparison with -kappa N/7 is equivalent to 3N>=12. Thus equation (3) holds at all stated N. Independently, Jensen with the *actual* coin alpha gives -log d_n<=kappa lambda_n. It yields both the triple bound xi<=3 kappa and r(n)<=kappa n/2 at every integer n. These bounds require no uniform lower bound on alpha and use no saddle approximation.

## 2. Window coefficient and tail subtraction

For N<=m<=floor(3N/2), the exact one-long-arm-root probability is at least

    [m/(2N)] [1-(m-1)/(2N)] >=1/8.

The resulting exponent, with the positive residual term included, is

    kappa [m^2-2(N+1)m+4N]/[2(2N-1)].

The polynomial is convex. At N and 3N/2 its values are -N^2+2N and -3N^2/4+N. For N>=4 both are <=-N^2/2, and therefore

    r(m)<=log 8-kappa N^2/[4(2N-1)]
         <=log 8-kappa N/8.

Using the continuous upper endpoint is legitimate even when the integer window ends at floor(3N/2).

The geometric choice kappa_i=99*100^(-i) has sum one and tail sum kappa_i/99. Jensen consequently gives, for the whole later tail on the ith window,

    sum_(j>i) r_j(m) <= (m/2)kappa_i/99
                      <= kappa_i N_i/132.

The surviving negative coefficient is exactly

    1/8-1/132 = 31/264.

No later-cell lower bound or unproved sign is used. Absolute convergence at each fixed m legitimizes the upper comparison with the summed Jensen majorant.

## 3. Noncircular recursive choice

At step i, all earlier cells have already been fixed. Their inherited fixed-cell strict saddle asymptotics, including bounded real lattice phases, provide constants C_j>=0 and finite thresholds H_j for

    r_j(m)<=(1/2)log m+C_j  for m>=H_j.

Those constants may be enormous; the construction does not need them to be uniform. The required inequality is

    (31/264)kappa_i N_i >= log 8
       +[(3i-1)/2]log(3N_i/2)+sum_(j<i)C_j.

For fixed i the left side grows linearly and the right side logarithmically in N_i. An integer satisfying this inequality, all prior thresholds, N_i>=4, and N_i>2N_(i-1) therefore exists. Only after choosing N_i are the ith cell and its constants C_i,H_i fixed. There is no appeal to the constants of a cell not yet chosen.

On the ith window, adding the prior-cell bound, the ith negative bound and the whole later-tail bound gives

    R(m) <= [(i-1)/2]log m -[(3i-1)/2]log(3N_i/2)
          <= -i log m.

The last step uses log m<=log(3N_i/2). The condition N_i>2N_(i-1) makes the windows disjoint and their arities tend to infinity. Thus liminf R(n)/log n=-infinity is justified. No claim about a logarithmic limit or the upper limsup is needed.

Likewise the recursive inequality forces kappa_i N_i/log N_i to grow at least proportionally to i. The single-factor window estimate then gives r_i(N_i)/log N_i tending to -infinity. Any constants correcting those lower bounds must fail to tend to zero, hence cannot be a nonnegative summable family. The additive-correction obstruction follows as well. The fixed window of ratio 3/2 suffices for the stated window-averaging obstruction; no assertion for every possible averaging transform is accepted.

## 4. One fixed target and fixed-arity convergence

All constructed cells have ell_i=kappa_i/2 and beta_i=kappa_i/2, with sums one, one-half and one-half. With ordinary complement C=1, their two total budgets are K=2 and L=3/2.

The one fixed target consists of ordinary duration one and the balanced strict cell a=b=2,g=1/2. That cell has kappa=1, ell=1/2 and beta=1/2, so its two budgets are exactly the same K=2 and L=3/2. If a strict word requires ordinary passages on both sides of this cell, split its ordinary duration into any two strictly positive pieces totaling one. Its diagonal resource values remain those stated. This target is fixed before any finite truncation is selected.

Triple positivity follows directly:

    D_3=e^(-3C)product_i d_3(B_i)>=e^(-3-3 sum kappa_i)=e^(-6).

Indeed Jensen already gives the stronger fixed-arity bound d_n(B_i)>=e^(-kappa_i lambda_n). It implies convergence of sum -log d_n and thus positivity of every fixed-arity diagonal product. Also

    |r_i(n)|<=-log d_n(B_i)+kappa_i lambda_n+beta_i n
             <=kappa_i[2 lambda_n+n/2],

so the residual series is absolutely convergent at every fixed n without interchanging a large-n limit with the cell sum. If a chronological complete-kernel analysis carrier is desired, the no-merger coupling gives row-TV from identity at most 1-d_n<=kappa_i lambda_n, making the omega-ordered bare-cell products Cauchy at every fixed cap. This optional auxiliary construction does not admit a countably infinite original graph.

## 5. Actual finite strict truncations

After the first M cells, the fair replacement cell has kappa=100^(-M), arms both 2*100^(-M), ell=kappa/2, and beta=kappa/2. Its resource exactly replaces the omitted geometric tail. Consequently every finite truncation has K=2,L=3/2 at the same target budgets.

Positive ordinary connectors can be supplied explicitly. There are M+1 retained/replacement cells; place duration 1/(M+2) in each of their M+2 ordinary gaps, including the initial and final gaps. All cell arms, coins, and connectors are strictly admitted. Total ordinary duration remains one. No zero-duration connector or boundary value is needed. The source diagonal is independent of how the ordinary duration is divided, since these triangular diagonal factors multiply; its logarithmic residual is the cell sum used in the proof.

For M>=i, the cells after i together with the fair replacement have total kappa exactly kappa_i/99. Each obeys the same Jensen upper bound. The summed window estimate therefore survives unchanged on the ith window. This is an exact statement about finite strict words with resource equality, not an approximate realization of a matched observation law.

## 6. Scope and remaining master gate

The fixed target's strict-cell residual eventually equals (1/2)log n+O(1). The constructed countable residual has windows R(m)<=-i log m, so it cannot satisfy that target's full all-arity residual identity. Resource matching leaves that crucial premise unfulfilled. The finite truncations also carry no assertion of legal topology-prefix equality, so they do not constitute the requested exact all-prefix negative rival construction.

The result rules out the specified resource-only logarithmic Fatou/lower-envelope inference, including one fixed multiplicative-window average and zero relative entropy. It does not refute a proof using the full collective target identity, richer complete forest equalities, a source-positive separator, or another analytic transform. General G4 and unequal finite persistence under full target matching remain open.

Signed: Codex / boundary_carrier, independent hand reviewer. Actual checks were the displayed algebra, routing inequalities, recursive quantifiers, exact target budgets, fixed-arity convergence, and strictly positive finite-source connector realization. File hashes verify the reviewed bytes only.
