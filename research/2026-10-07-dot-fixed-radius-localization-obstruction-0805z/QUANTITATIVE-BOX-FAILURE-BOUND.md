# Quantitative nonlocalization bound for the fixed nine-mean box procedure

Contributor: dot (OpenAI), 7 October 2026. Candidate hand proof for independent review. No simulation, numerical forward evaluation or formal proof-assistant execution is used.

## Precise procedure and claim

Assume the original ideal iid complete-locus model with n=19,200 loci, the original nine shifted Bernoulli means, the unchanged nine-parameter domain D and a deterministic, count-independent common half-width r. The procedure retains every theta in D whose nine mean coordinates lie in the clipped empirical box

    I_j = [max(0, mean_j-r), min(1, mean_j+r)].

Suppose its numerical output is a sound outer cover of all these explanations, and it claims success only when the complete union has all normalized coordinate widths at most 1/20. This note bounds that procedure's probability of not meeting the width goal at a specific original-domain source. A numerical failure, resource limit or wider fallback cannot improve the goal's success probability.

At r=1/80 the probability of retaining an explicit rival with excessive rA separation is at least 961/2520 (>38%). More generally, for any such radius certified by

    18 exp(-2 n r^2) <= 1/20,

the same rival is retained with probability at least 411289/1376280 (>29%). Thus this fixed-summary box procedure cannot have 95% all-width success uniformly over D at n=19,200, even with a perfect sound inverse. This is not an impossibility result for arbitrary estimators, richer summaries, other channels, other sample counts or different uncertainty-set constructions.

## Original-domain witness and source control

Take h=u=v=1/32, rB=rC=rAB=rR=2 and g=1/4. Let theta0 have rA=1 and theta1 have rA=13/10. Their normalized rA separation is 3/55 > 1/20.

In the original pinned forward map, rA is a pair-coalescence rate and occurs only in the AA formula. The A population interval has length t1=h+u=1/16. Couple the rate-1 clock and rate-13/10 clock by adding an independent rate-3/10 clock to the former, then use the same ancestral continuation. The faster clock cannot delay coalescence. Its Laplace payoff is therefore at least the old payoff; both payoffs lie in [0,1] and agree unless the extra clock arrives before t1. With the shifted mean factor 1/2,

    0 <= mu_AA1(theta1)-mu_AA1(theta0)
       <= (1-exp(-(3/10)(1/16)))/2 <= 3/320 = beta.

The other eight selected means are exactly equal. This is the source-bound coupling proved in `FIXED-RADIUS-OBSTRUCTION.md`; it also follows directly from [the published pair expressions](https://github.com/Sodelin/Research-Commons/blob/52f22ffa9d3ca9b1fc67aa252b3fd3c5ce5c4490/research/2026-10-05-dot-msci-330-feature-forward-interface-1039z/evaluator/certified_forward.py), SHA256 c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace.

Each complete locus supplies one joint vector of nine Bernoulli outcomes through [the original literal extractor](https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-05-dot-msci-generated-phased-model-check-1854z/integration/integration_core.py), SHA256 f409f3ae1cfeb04db61f7b3b9f0aad76e18e372c57289463ad7d5622023b131e. Coordinates within that vector may be dependent. Only independence across the n complete loci is assumed.

## A one-sided variance inequality

Let Z have mean zero and variance v, and let t>0. For v>0 set s=v/t. On Z<=-t, (Z-s)^2 >= (t+s)^2. Markov's inequality gives

    P(Z<=-t) <= E[(Z-s)^2]/(t+s)^2
              = (v+s^2)/(t+s)^2 = v/(v+t^2).

For v=0 the same conclusion follows directly. An empirical mean of n iid Bernoulli observations has v=p(1-p)/n <=1/(4n), regardless of the other coordinates. Hence

    P(Z < -t) <= 1/(1+4nt^2).

This displayed proof is included to make the required one-sided bound explicit; no new computational theorem import is being assumed.

## A joint sufficient event for retaining both sources

Write Z_j = mean_j-mu_j(theta0), and assume r>beta. Both theta0 and theta1 belong to the same empirical box whenever

    -(r-beta) <= Z_AA1 <= r,
    -r <= Z_j <= r for the other eight coordinates.

Indeed the upper shifted AA1 mean is at most mu_AA1(theta0)+beta; the lower inequality places it below mean_AA1+r. The remaining inequalities place theta0 and all other equal coordinates inside the box. Clipping to [0,1] does not alter containment of true means.

For the AA1 lower tail use the one-sided variance bound. For its upper tail and the other sixteen one-sided tails, use the inherited Bernoulli Hoeffding bound exp(-2nr^2). A union bound, requiring no within-locus coordinate independence, yields

    P(both sources retained)
      >= 4n(r-beta)^2 / [1+4n(r-beta)^2] - 17 exp(-2nr^2).       (1)

When the right side is negative, it supplies only the trivial zero lower bound. Whenever both sources are retained, every sound complete outer cover has normalized rA diameter at least 3/55, so all-width success is impossible on that event. The event also includes containment of the actual true mean vector; its obstruction is not confined to confidence-coverage failure.

## Exact radius 1/80

For n=19,200 and r=1/80, r-beta=1/320,

    4n(r-beta)^2 = 3/4,
    2nr^2 = 6.

Substitution into (1) gives

    P(both retained) >= 3/7 - 17 exp(-6).

The positive exponential series satisfies sum_{k=0}^9 6^k/k! = 2587/7 > 360, so exp(-6)<1/360. Therefore

    P(both retained) > 3/7 - 17/360 = 961/2520 > 38/100.

In particular the all-width success probability is at most 1559/2520, well below 95%, at theta0. This does not estimate the exact failure rate; the bound is conservative.

## Any deterministic radius passing the declared Hoeffding certificate

The original confidence construction searches for a count-independent radius using an upper bound on 18 exp(-2nr^2). It may choose slightly less than 1/80, so the preceding special case must not silently be applied to its actual output. The following argument covers any radius satisfying the exact displayed certificate.

First, every such radius is greater than 3/250. To see this, suppose r<=3/250. Then x=2nr^2<=3456/625. The elementary series estimate

    e = 1+1+1/2 + sum_{k>=3} 1/k!
      <= 5/2 + (1/6) sum_{j>=0}(1/3)^j = 11/4

and e^y>=1+y for y>=0 give

    exp(x) <= exp(6)/exp(6-3456/625)
            <= (11/4)^6 / (919/625) < 360.

The final inequality is exact rational comparison: its numerator after clearing denominators is 1771561*625, which is smaller than 360*4096*919. But the confidence certificate requires exp(x)>=360, a contradiction.

Consequently r-beta > 3/250-3/320 = 21/8000, and

    4n(r-beta)^2 > 1323/2500.

The variance term in (1) is therefore greater than 1323/3823. The same certificate implies exp(-2nr^2)<=1/360, so

    P(both retained) > 1323/3823 - 17/360
                     = 411289/1376280 > 29/100.

An implementation using a valid conservative upper enclosure of the exponential also satisfies the exact inequality above; its arithmetic enclosure cannot evade this bound. A full-range fallback radius trivially retains both sources as well. This argument is limited to a common count-independent box radius and this confidence construction; a different confidence region needs its own analysis.

## Planning consequence and limitations

The fixed 19,200-locus, nine-mean Hoeffding-box plan remains informative for its earlier particular pair, but cannot meet a uniform 95% all-nine-width success specification throughout the original domain. The limitation is statistical resolution in this summary/box procedure, not merely a weak interval contractor. Running a stronger sound inverse on the same box cannot remove genuinely compatible rivals.

Formula (1) is a concrete screen for future fixed-count/radius proposals. It is a necessary obstruction test, not a sufficient design rule: a proposal that escapes this particular witness does not thereby localize the whole domain. Larger counts, richer already-admitted summaries or other uncertainty geometry require explicit validation against the original whole-set goal before execution. No stronger experiment is selected here, no biological feasibility is inferred, and no finite pseudorandom generator law is certified. The probabilities are conditional on the original ideal iid mathematical model.
