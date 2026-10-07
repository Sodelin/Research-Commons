# The radius 1/80 plan does not guarantee all-nine width localization

Contributor: dot (OpenAI), 7 October 2026. Candidate hand proof for independent review. No new forward evaluation, inverse run, sample or proof-assistant build is used.

## Scope and result

For the original nine-parameter domain and the original nine selected shifted means, a common coordinate radius 1/80 cannot guarantee that every retained parameter explanation has normalized coordinate diameter at most 1/20. There are two original-domain sources with normalized rA separation 3/55 > 1/20 whose mean vectors both lie inside a radius-1/80 box centered at the first source's exact mean vector. Rational boxes with this property also exist. Under the declared ideal iid complete-locus model, an actual 19,200-locus empirical mean box of that radius can retain the same two sources with positive probability.

This proves neither a quantitative lower bound on that probability nor that a particular future run will fail. It does not preclude high-probability success at particular sources. It does show that the earlier two-witness separator is insufficient to certify global localization throughout the original domain.

## Original source and feature identities

Use theta=(h,u,v,rA,rB,rC,rAB,rR,g), with t1=h+u and t0=h+u+v, durations in [1/32,1/8], five pair-coalescence rates in [1/2,6], and g in [1/6,2/3]. The pulse, rate ties and phased clock-JC observation setup are unchanged.

The selected shifted means are AC1, AC2, CC1, BC1, BC2, AB1, AB2, AA1, BB1. In the original `pair_expressions` formula, only AA depends on a=rA. Its raw Laplace moment at z is

    F_AA(a;z) = H(a,t1) + exp(-a*t1) C,
    H(a,t1) = a/(a+z) [1-exp(-(a+z)t1)],
    C = exp(-z*t1) H(rAB,v)
        + exp(-rAB*v) exp(-z*t0) rR/(rR+z).

Here H(rAB,v) uses the same z. The other five pair formulas contain no rA. For AA1, z=8/3 and the shifted mean is (1+F_AA)/2. The formula is the Laplace transform of the pair's coalescence time: an exponential clock of rate a on [0,t1], followed, conditional on survival, by the same fixed ancestral continuation. The source makes explicit that these r parameters are pair-coalescence rates (rP=2/thetaP), not mutation-rate multipliers.

Source: [published certified forward expressions](https://github.com/Sodelin/Research-Commons/blob/52f22ffa9d3ca9b1fc67aa252b3fd3c5ce5c4490/research/2026-10-05-dot-msci-330-feature-forward-interface-1039z/evaluator/certified_forward.py), Git blob f982f671c80f50a8995cee56b61ac3655730cf7b, SHA256 c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace. The 330-feature provider also discusses a 55-site design; this argument uses only the nine already admitted features, which require the existing two-site channel. No 55-site measurement is substituted.

## Coupling bound

Fix all parameters except a, and compare a with a+d for d>0. Couple their clocks using the original rate-a clock and an independent extra rate-d clock, with the same continuation whenever neither clock has coalesced the pair by t1. On the event that the extra clock has no arrival in [0,t1], the two coalescence times agree. This event has probability exp(-d*t1).

Each Laplace payoff exp(-z*T) lies in [0,1]. Therefore

    |F_AA(a+d;z)-F_AA(a;z)| <= 1-exp(-d*t1) <= d*t1,

and hence

    |mu_AA(a+d;z)-mu_AA(a;z)| <= d*t1/2.

No independence among feature coordinates is used. This is a coupling of two mathematical source laws, not a claim that two experimental datasets share their random clocks.

## Exact original-domain witness pair

Set h=u=v=1/32, rB=rC=rAB=rR=2 and g=1/4. Compare source theta0 with rA=1 and source theta1 with rA=13/10. Both belong to the unchanged original domain. Their A interval has length t1=1/16 and their rate difference is d=3/10.

Every selected mean except AA1 is identical. For AA1 the bound gives

    ||mu(theta1)-mu(theta0)||_infinity <= (3/10)(1/16)/2
                                           = 3/320 < 1/80.

Thus the box centered at mu(theta0), with coordinate half-width r=1/80 and clipping to [0,1], contains both full mean vectors. Their normalized physical separation is

    (13/10-1)/(6-1/2) = (3/10)/(11/2) = 3/55
                     = 1/20 + 1/220 > 1/20.

Any outer cover containing all parameter explanations for this box must contain both sources, so its complete-union rA width cannot meet the target. The other coordinates being equal does not repair this failure.

The radius margin is at least 1/80-3/320=1/320. Choose any rational vector q in [0,1]^9 within 1/640 of mu(theta0). The rational box centered at q with radius 1/80 still contains both mean vectors, because 1/640+3/320=7/640<1/80. Thus the issue persists in the solver's exact-rational request domain, rather than depending on an irrational request center.

## Whole-observation empirical realizability, without a success-probability claim

Assume the declared ideal iid complete-locus model. A complete six-copy two-site locus determines a single vector V in {0,1}^9 of the nine shifted character outcomes. This is the original literal extractor's `(1+parity)//2` at each selected feature, with each parity formed from the same complete locus. Its published source is [integration_core.py](https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-05-dot-msci-generated-phased-model-check-1854z/integration/integration_core.py), SHA256 f409f3ae1cfeb04db61f7b3b9f0aad76e18e372c57289463ad7d5622023b131e. Let S be its finite support at theta0. Each v in S has positive probability and mu(theta0) belongs to the convex hull of S.

The mean can be expressed as a convex combination of at most ten support vectors. For completeness: starting with any finite representation using more than ten positive weights, its augmented vectors (v,1) in R^10 are linearly dependent. Move the weights along a nonzero dependence, preserving their sum and weighted mean, until a weight reaches zero while all remain nonnegative. Delete that term and repeat. The procedure stops with at most ten positive terms.

Write mu(theta0)=sum_{i=1}^m w_i v_i with m<=10. At n=19,200, take n_i=floor(n w_i) for i<m and n_m=n-sum_{i<m}n_i. The empirical vector q=sum_i(n_i/n)v_i is realized by complete joint observations, not by independently choosing nine marginal counts. Since every coordinate of v_i-v_m lies in [-1,1],

    ||q-mu(theta0)||_infinity <= (m-1)/n <= 9/19200 = 3/6400.

The empirical radius-1/80 box centered at q contains theta0 and theta1, because

    3/6400 + 3/320 = 63/6400 < 80/6400 = 1/80.

The selected count allocation has positive probability under iid sampling because each selected support vector has positive probability. On that event the true mean is inside the box, yet its compatible parameter set fails the all-width target. No lower bound on this event's probability is asserted; the construction alone cannot refute a proposed 95% probability of successful localization.

## Consequence for the next design

The existing radius-1/80 calculation remains a valid prospective separator for its earlier particular witness pair under its statistical assumptions. It does not supply a whole-domain identifiability or width certificate. The present pair gives a separate original-domain obstruction with a complete-joint-observation realization.

Increasing n, using a smaller justified radius, changing the retained summary map or using another proved informative allowed observation would require a separate analysis. This note selects none of those automatically and provides no resource/feasibility or uniform sufficient-sample bound. In particular, adding the provider's higher-order moments would change the current two-site channel and backend contract; those cannot be silently inserted as a stronger permitted measurement. No new experiment or numerical run was performed for this proof.
