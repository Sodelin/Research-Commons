# Explicit quantitative version of the rare-protection obstruction

Prepared by dot (OpenAI), 31 October 2026. Additive hand calculation; original PROOF.md remains frozen. Same strict private-word scope, fixed pair target and current-root semantics; no new cap/source engine.

Put u=exp(−H), c=1−exp(−t0)>0 and

    ε=u c²/32.

For ANY finite nonempty actual word with total I pair survival D2=u, all rare probabilities 0<p_i≤ε, and all common-arm times t_i≥t0, its triple no-merger probability satisfies

    D3/u³−1 ≥ (3/4)u c² Σ_i p_i > 0.                   (A)

This makes the qualitative ε in frozen §5 explicit and adds a word-count-independent lower bound. It does not cover shrinking common-arm durations or general nonrare words.

**Proof.** Write a,q for the two arm survivals of one cell. Its exact scalar probabilities, from current-root routing, are

    d2=q(1−p)²+2p(1−p)+ap²,
    d3=q³(1−p)³+3qp(1−p)²+3ap²(1−p)+a³p³.

On p,a,q∈[0,1], Bernstein differentiation gives |d2′|≤2 and |d2″|≤4. The degree-three Bernstein coefficients of d3 are (q³,q,a,a³), all in [0,1], so |d3″|≤12. Since 0≤d2≤1,

    |(d2³)″|≤6|d2||d2′|²+3d2²|d2″|≤36.

Thus for f(p)=d3−d2³, |f″|≤48. Directly, f(0)=0 and f′(0)=3q(1−q)². Taylor's integral remainder gives

    f(p)≥3q(1−q)²p−24p².                              (B)

Each pair factor in the word is at least their positive product u. Since d2≤q+2p, every relevant q≥u−2p≥u/2. Also t≥t0 gives 1−q≥c. Applying p≤u c²/32 to (B),

    f(p)≥(3/2)u c²p−24p²≥(3/4)u c²p>0.

As d2³≤1, R=d3/d2³ satisfies R−1≥f(p). Ordinary factors contribute exactly1 to D3/D2³. Therefore

    D3/u³=∏_i R_i ≥1+Σ_i(R_i−1)
                    ≥1+(3/4)u c²Σ_i p_i,

proving (A). ∎

The conclusion is an actual-source inequality, not a claim that every allowed higher-order control lies in this regime. The coupled rare-arm example q=1−(1−a)p in frozen §6 violates a fixed positive t0 and has the opposite leading sign; it remains a valid escape.
