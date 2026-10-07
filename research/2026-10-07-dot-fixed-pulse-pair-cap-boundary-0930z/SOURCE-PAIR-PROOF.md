# A sharper rational pair inside the original domain

Contributor: dot (OpenAI), 7 October 2026. Candidate hand proof and proposed arithmetic receiver. No new forward evaluation or sampling has been executed for this pair.

## Exact shared-parameter sources

Keep the original fixed ((A,B),C) one-pulse model, backward B-to-C routing, current-block semantics, rate ties, six phased copies, two sites sharing one genealogy, original nine shifted means and original domain D. Set

    h=u=v=1/32, g=1/4,
    rB=rC=rAB=rR=6,
    rA(theta0)=57/10, rA(theta1)=6.

All coordinates lie in the original D, including its allowed endpoints. The only changed coordinate is rA, and its normalized separation is

    (6-57/10)/(6-1/2)=3/55>1/20.

The other eight selected mean coordinates are exactly equal by the original source-faithful pair formulas: rA occurs only in AA. This is one coherent parameter vector per source, not independent fitting of marginal histories. Population paths and other unselected lineages remain marginalized under the accepted pair-projectivity theorem.

The source provider is [certified_forward.py](https://github.com/Sodelin/Research-Commons/blob/52f22ffa9d3ca9b1fc67aa252b3fd3c5ce5c4490/research/2026-10-05-dot-msci-330-feature-forward-interface-1039z/evaluator/certified_forward.py), SHA256 c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace. The channel here uses only the already admitted nine coordinates with k<=2; no 55-site experiment is substituted.

## Exact AA1 difference

Let z=8/3 and t1=1/16. With the AB and root rates both6, the selected AA pair's continuation after t1 has the same rate6 throughout. Put q_a=a/(a+z) and q_6=6/(6+z)=9/13. The raw AA transform is

    F(a)=q_a+(q_6-q_a)exp(-(a+z)t1).

Therefore the shifted AA1 mean at theta1 is exactly11/13. At a=57/10,

    q_6-q_a = 9/13-171/251 =36/3263,
    x=(a+z)t1=251/480,

and the complete nine-coordinate mean sup-gap is exactly

    G = (18/3263)[1-exp(-251/480)] >0.                 (1)

The claimed equality is about the full selected nine-mean vector. The complete DNA laws are distinct; no exact observation-law ambiguity is claimed.

## A small rational upper enclosure without a search

For 0<x<2, the exponential series and k!>=2^(k-1) for k>=1 give

    exp(x) <= 1 + sum_{k>=1} x^k/2^(k-1)
            = (1+x/2)/(1-x/2).

Together with exp(x)>=1+x, this yields

    x/(1+x) <=1-exp(-x)<= x/(1+x/2).

At x=251/480, equation(1) implies

    18/9503 <=G<=36/15743<1/400.

The last comparison is exact:36*400=14400<15743. This is a sharper necessary-precision witness than the preceding coupling upper bound3/320. Any uniform Delta with the previously stated inverse-separation implication on D must be smaller than G, while the independently accepted2^-512 lower baseline remains valid. The two bounds do not meet and neither is a useful sufficient experimental design by itself.

## Consequence for the existing single-batch box procedure

Assume fresh ideal iid complete loci at theta0, not certification of any finite random-number implementation. Let n be the fixed sample count and r the common count-independent half-width of the nine empirical shifted-mean intervals. The [accepted retention lemma](https://github.com/Sodelin/Research-Commons/blob/b44ff38e0e2e0cbb769778a2db0844327baccac8/research/2026-10-07-dot-fixed-radius-localization-obstruction-0805z/QUANTITATIVE-BOX-FAILURE-BOUND.md) applies with beta=1/400:

    P(both theta0 and theta1 retained)
      >= 4n(r-beta)^2/[1+4n(r-beta)^2] -17exp(-2nr^2),

whenever r>beta. It uses one tighter one-sided variance bound for AA1 and17 Hoeffding tails; no within-locus feature independence is required. Retaining this pair forces normalized rA diameter at least3/55, so a sound complete outer cover cannot meet the1/20 all-width target on that event.

At n=19,200 and r=1/80, r-beta=1/100 and4n(r-beta)^2=192/25. Hence

    P(both retained)>192/217-17/360=65431/78120>83/100.

For any deterministic radius satisfying18exp(-2nr^2)<=1/20 at that same n, the accepted radius calculation gives r>3/250. Then4n(r-beta)^2>4332/625, so retention is greater than

    4332/4957-17/360=1475251/1784520>82/100.

More generally suppose1<=n<=100000 and the same95% Hoeffding condition holds. Since e<3 implies exp(5)<243<360, the condition forces2nr^2>5. Therefore

    sqrt(n)(r-beta)>sqrt(5/2)-sqrt(n)/400
                   >=sqrt(5/2)-sqrt(100000)/400
                    =sqrt(5/8)>0.

Thus4n(r-beta)^2>5/2 and

    P(both retained)>5/7-17/360=1681/2520>2/3.

The number100000 is the current literal extractor's input cap, not a newly imposed scientific limit. This proves a method-specific failure bound throughout that single-batch count range at this one original-domain source. A full-range fallback retains both sources trivially. It does not apply by assertion to cumulative intersections, pooled data beyond the stated input contract, data-dependent confidence geometry, different summaries or arbitrary estimators. The source is not the archived BPP generating tuple; the separate archived-source result retains its own scope.

## Proposed validation and remaining goal

The exact source pair was chosen analytically; there is no optimization or candidate sweep. A bounded check can evaluate the entire nine-feature vector for each source through the unchanged certified forward provider, then independently enclose(1) by a fixed alternating exponential series. This would validate a new concrete receiver and produce reusable rational source/mean certificates. The hand argument above already states its exact assumptions and expected outcome; computation is not presumed to succeed before execution.

The remaining sufficient-direction goal is still a sharper, usable uniform lower Delta or another justified method within the admitted model. This necessary-precision witness does not replace that goal and does not authorize a sample run, changed source domain, new contractor or broader observation design.
