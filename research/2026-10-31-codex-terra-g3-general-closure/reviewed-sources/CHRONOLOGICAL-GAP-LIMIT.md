# A chronological two-variable limit for the actual full G3 fibre

Contributor: Codex (OpenAI), 31 October 2026 UTC. **Hand-derived conditional corollary, not independently reviewed or Lean formalized.** It reuses the source-cost, cap4 charge and event-minorization providers named in `REFERENCE-SCALE-GAP-BUDGET.md`. It supplies a genuine necessary limiting equation, not AG-Pair, an outlier exclusion, a witness selector or original G3 closure.

## Result

Use exactly the full-cap12 strict equal-arm paired fibre and small-domain hypotheses of `REFERENCE-SCALE-GAP-BUDGET.md`. Set H=-log c, h=-log t and L=H/4. For each actual cell put

    z_i=u_i/h,     y_i=beta_i u_i/h²,
    beta_i=(2g_i-1)²,   ell_i=log[(q_i+2v_i(1-q_i))/q_i].

Let w_i be its ACTUAL cap4 chronological charge weight: the product of all preceding b4 factors and following b2 factors, including every ordinary population. The source and paired COMMON clock give

    c^6<=w_i<=1.

Define the source-presentation-dependent probability measure

    mu_h=sum_i (ell_i/L) delta_(w_i,z_i,y_i).                (1)

For the same fixed constant b=8 exp(H0) C0 as the preceding note,

    integral z^4 dmu_h <= b,     integral y² dmu_h <= b.    (2)

The second moment of z also has the positive lower bound already proved in `REFERENCE-SCALE-GAP-BUDGET.md`. At the exact full commutator fibre there is, with a constant uniform on the original small domain,

    integral w(z²-6y) dmu_h
       = [16/(15H)](c^(3/4)-b4I(K)) + O(h).               (3)

The integrand uses the actual same-source chronology and may have either sign. No weight is replaced by an ordinary clock, common constant or reference power.

Fix H>0 in that domain and consider ANY sequence of fitting actual finite words with h->0. A subsequence has b4I(K)->k4* and mu_h converging weakly to a probability measure mu on [c^6,1] x [0,infinity)^2. Every such subsequential limit satisfies

    integral w(z²-6y) dmu
       = [16/(15H)](c^(3/4)-k4*)
       >= [16 gamma(H)]/(15H) > 0,                          (4)

where gamma(H)=exp(-3H)(1-exp(-3H))/24. The original complete fibre imposes other constraints on these measures; this single equation is not asserted sufficient for realizability.

## Moment bounds and exact weights

The existing all-coin source cost is

    sum_i v_i[beta_i² u_i³+beta_i u_i^4+u_i^5] <= C0 H h^4.

The pair gap obeys 2v_i u_i<=ell_i<=2 exp(H0)v_i u_i. These inequalities include coins arbitrarily close to either endpoint. They give the first bound in (2) as previously, and also

    integral y² dmu_h
       = (1/Lh^4) sum_i ell_i beta_i² u_i²
       <= [8 exp(H0)/(Hh^4)] sum_i v_i beta_i² u_i³
       <= b.

For the weight lower bound, every factor's no-merger diagonal is at least its COMMON pair survival to the ordinary lambda_r power. If C_before and C_after are the products of the actual COMMON pair factors before and after cell i, then C_before C_after=c/q_i>=c. Since C_after>=C_after^6,

    w_i>=C_before^6 C_after >=(C_before C_after)^6>=c^6.

This is a bound on the actual cell-specific weights, not a claim they agree. All factors and cells are finite and strictly positive.

## Uniform expansion of the signed charge

The exact bare cap4 charge is

    chi=(v/3)(1-e^(-u))²[(1-e^(-u))-(5+e^(-u))beta],
    ell=log[1+2v(exp(u)-1)], v=(1-beta)/4.

After cancelling the common v factor, ell/(2vu) has a continuous positive extension to the CLOSED small (u,v) rectangle and equals 1+O(u) uniformly. The elementary Taylor formulas for exp and log therefore give, uniformly for ALL strict coins and small u,

    chi/(ell h²)
      = (z²-6y)/6+O[u(z²+y)].                              (5)

In particular the apparent quotient is controlled before taking a rare-coin limit; no positive lower coin margin is used. Since u=hz, Hölder and (2) imply

    integral u(z²+y) dmu_h
       = h integral (z³+zy) dmu_h
       <= 2 h b^(3/4).                                     (6)

The bound is interpreted with harmless max(1,b) if one wants a common coefficient for b<1. The exact whole-word x charge is x(K)=sum_i w_i chi_i. Dividing by Lh² and using (5)–(6) gives

    integral w(z²-6y) dmu_h
       =6 x(K)/(Lh²)+O(h).                                 (7)

The actual commutator supplies x(K)=(k2-k4)x(S)/(s2-s4), k2=c^(3/4). For the SAME strict reference, direct expansion of its known cap4 source gives

    x(S)=(2/3)h³+O(h^4),    s2-s4=15h+O(h²),
    x(S)/(s2-s4)=(2/45)h²+O(h³).

Since k2-k4<=c^(3/4)-c^6<=21H/4, substituting into (7) yields (3) with an O(h) constant uniform also as H ranges over the chosen small interval. No unknown k4 is replaced by s4^nu.

## Subsequential limit and dust

For fixed H, the support of w is compact and (2) makes the (z,y) marginals tight. Thus ordinary weak sequential compactness gives a probability-measure subsequential limit; b4I(K) can be taken convergent along the same subsequence. The lower bound k2-k4>=gamma(H) is the exact specified-cherry consequence already proved and independently reviewed in `REVIEW-G3-GAP-BUDGET.md`.

The functions z² and y are uniformly integrable: their respective tails are bounded by b/R² and b/R. Hence the unbounded continuous function w(z²-6y) passes to the weak limit after truncation, proving (4). This proof uses fourth moments of z and second moments of y, not an unjustified exchange of arbitrary weak limits and unbounded integrals.

Diffuse microscopic mass remains possible at the level of these necessary bounds. It may appear at z=0,y=0, and it may also appear at z=0 with finite positive y: for example, u of order h² with fixed nonfair beta has z->0 but beta u/h² of order one. Equation (4) says that such negatively charged dust must be balanced by sufficiently positive weighted z² mass; it does not prove that the full original fibre admits or excludes that dust. No mass is removed, no physical source is inferred from an arbitrary measure, and no finite weak-limit argument is promoted to exact commutation.

The concrete next attack is to combine (4) and its actual chronological weighting with the complete cap12 hybrid scalar energy equation and the remaining independent full-band constraints, retaining relative source costs for dust. A sign or phase conclusion from the cap4 moment alone would be unsupported.
