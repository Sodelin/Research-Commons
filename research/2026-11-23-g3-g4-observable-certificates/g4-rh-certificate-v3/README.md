# G4 v3: a certified chronology interval at positive gap

Same scope as v1–v2: the exact ordinary COMMON face, admitted same-source BOTH observables and their private kernel adapter, and a matched strict finite equal-arm E/B word. Not a result for alternate cores, INDEPENDENT-only interfaces, approximately COMMON-ordinary data, or all G4.

## Statement and construction

Use v2 notation. Assume U>0 and Δ<3UR², so the unique dominant cell has excess m≥m_min. Put b=b_max (the data-only ceiling on aggregate tail excess), and let c be an upper bound for the dominant coin's deviation, for example sqrt(Δ/12)/m_min capped at 1/2. The checker rounds this square root upward rationally.

Let a=1/q be the inverse survival of the actual dominant cell, and a0=1+2U (so q0=1/a0). The local bias contribution d=3m²(1/(4h)−1) obeys 0≤d≤Δ. Consequently

    a = 1+2m + 2d/(3m)
    a_minus = max{1+2m_min, a0−2(1+U)b}
    a_plus  = min{1/C, a0+2Δ/(3m_min)}
    a_minus ≤ a ≤ a_plus.

Indeed U−m=(1+m) times the actual aggregate tail excess. Positive ordinary durations give a<1/C. The expected proxy a0 is in the closed range above, and D0=C a0<1 by the v1 strict clock screen. For the difference of the true and proxy bigon clock lengths we have

    |log a−log a0| ≤ τ := max{a0−a_minus,a_plus−a0}/a_minus.

After replacing tail bigons by ordinary steps and making the dominant coin fair as in v2, write E(x) B(q,q,1/2) E(y), with D=xy=C a. The time fraction s=log(x)/log(D) in (0,1) is the hidden chronology of interest: the fraction of the nondominant clock before the dominant cell. The clocks of tail cells remain counted in their original positions. Replace q with q0 and x,y with x0=D0^s,y0=D0^(1−s). This preserves both C and s. The sum of the absolute changes to the three segment clock lengths is 2|log a−log a0|, since the two ordinary lengths scale by fractions of one common clock change. Each homogeneous segment's pair rate is at most choose(n,2) when it starts with at most n roots; after coupling its overlapping duration, any discrepancy due to differing remaining durations has probability at most rate times duration difference. This applies to both arms together. Composing with v2's coupling, the original and this proxy differ at finite arity n in labelled-forest total variation by at most

    E_n := min{1, choose(n,2)(b+2τ)+n c}.

This bound is asserted for the forest state transported through words, not absolute external time markers that explicitly distinguish segment boundary times.

Now write p for the measured INDEPENDENT probability of four entering roots exiting as two. The proxy's v1 chronology formula is p0+K(1−r), where

    p0 = (B(q0,q0,1/2) E(D0))[4,2]
    K  = D0(1−q0)^3/40 > 0
    r  = x0^5 = D0^(5s).

Hence r belongs to the following conservative closed intersection (physical r must also be strictly between D0^5 and 1):

    [r_lo,r_hi] = [D0^5,1] ∩ [1+(p0−p)/K−E_4/K, 1+(p0−p)/K+E_4/K].

An empty admissible intersection excludes the data on the stated face. Otherwise this gives a computable interval for s by reversing and applying log(r)/(5 log D0). The checker needs no approximate logs. It also outputs a rational interval for the actual x^5 since x^5=r(a/a0)^(5s). Multiply r_lo by min{1,(a_minus/a0)^5} and r_hi by max{1,(a_plus/a0)^5} (clipped at one). At Δ=0 these intervals collapse to the original exact inversion; reversal can also be certified at Δ>0 if intervals are disjoint with common diagonals.

For a fully observation-derived fair representative, choose r_fit at the interval midpoint and set its pre-cell survival to r_fit^(1/5), post-cell survival D0/r_fit^(1/5). This is strict whenever the certificate does not exclude and, for rational inputs, uses an algebraic fifth root. Its full finite-arity forest bound follows by another duration coupling: the sum of its two clock changes from the proxy is at most (r_hi−r_lo)/(5r_lo). Thus the bound is E_n with the extra term choose(n,2)(r_hi−r_lo)/(5r_lo) inside the clipping. No recovery of the number, coins, or chronology of weak tail cells is claimed.

## Verification and limits

Run `python3 -B g4-rh-certificate-v3/chronology_certificate.py` with sibling v1 and v2 folders present. Six exact rational tests cover 48 nonzero-gap words with rational power-related clocks, disjoint intervals for reversed biased layouts, rejection of a contradictory p42, exact recovery at zero gap, and exclusion of both zero-gap clock endpoints. The 48-fixture containment checks compare integer powers of rational endpoints without floating-point logs. The tests check root-count kernels; full-forest estimates come from the hand coupling, not empirical coverage.

This procedure does not establish exact identifiability at a positive gap, and large or ill-conditioned intervals may add little. In particular inversion amplifies uncertainty when the dominant arm survival is near one, since K scales as (1−q0)^3. A match to the five numbers does not establish realizability or equivalence of additional rows. No formal kernel check or historical novelty assessment is claimed.
