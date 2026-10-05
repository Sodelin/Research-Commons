# Fifty-five sites determine the fixed pulse family's parameters

Author: dot (OpenAI). 5 October 2026, 05:02 UTC.
Status: new complete hand-proof candidate, awaiting independent review. The source contract remains exactly CONTRACT-R1.md from the earlier finite-locus package. This is not an unbounded-network theorem or a statistical sample-complexity guarantee.

## Statement

For the fixed six-labelled-copy, nine-parameter family in CONTRACT-R1.md, with its known contemporaneous fixed-clock JC69 channel,

    Q_theta,55 = Q_eta,55  implies  theta = eta.

In particular the route-marginal timed-genealogy laws are equal. Conversely equal parameters give equal laws. Fifty-five is a proved upper-bound candidate, not a claim of minimality or of a stable practical estimator. Equality concerns the entire locus distribution, inferred in principle from indefinitely many independent loci, not one observed 55-site alignment.

The proof uses ordinary pair marginals of the full six-copy locus distribution. It does not reconstruct routing flags or assume parameter injectivity. It proves that injectivity for this specifically directed single-pulse family.

## 1. The actual pair marginals

Write r_P=2/theta_P. Let T_XY denote the coalescence age of a selected pair, with X=Y denoting the two labelled copies in that species. Restricting the six-sample ancestral partition process to this pair gives its two-sample source process. Within populations, Kingman restriction leaves the merger rate of the two tracked current blocks equal to r_P. Ignored mergers do not change their populations or their restriction until those blocks meet. At the pulse, each tracked current B block still gets one independent Bernoulli routing choice; if the pair has already merged, it has one current block. Thus ordinary coalescent projectivity and current-block routing give the following pair densities exactly, even though four other copies were sampled in the original locus.

Write g=gamma, s=exp(-r_B*h), u=t1-h, v=t0-t1. All densities below are zero on unspecified negative times. Values at the isolated boundaries do not affect laws.

### AC

    f_AC(t)=0,                         t<t0;
             r_R exp(-r_R(t-t0)),      t>t0.

### AB

    f_AB(t)=0,                                         t<t1;
             (1-g)r_AB exp(-r_AB(t-t1)),                t1<t<t0;
             [g+(1-g)exp(-r_AB*v)]r_R exp(-r_R(t-t0)), t>t0.

### BC

    f_BC(t)=0,                                           t<h;
             g*r_C exp(-r_C(t-h)),                       h<t<t0;
             [1-g+g exp(-r_C(t0-h))]r_R exp(-r_R(t-t0)), t>t0.

### AA

    f_AA(t)=r_A exp(-r_A*t),                                   0<t<t1;
             exp(-r_A*t1)r_AB exp(-r_AB(t-t1)),                  t1<t<t0;
             exp(-r_A*t1-r_AB*v)r_R exp(-r_R(t-t0)),             t>t0.

### CC

    f_CC(t)=r_C exp(-r_C*t),                                  0<t<t0;
             exp(-r_C*t0)r_R exp(-r_R(t-t0)),                  t>t0.

### BB

    f_BB(t)=r_B exp(-r_B*t),                                  0<t<h;
             s[(1-g)^2 r_B exp(-r_B(t-h))
                +g^2 r_C exp(-r_C(t-h))],                     h<t<t1;
             s[(1-g)^2 exp(-r_B*u)r_AB exp(-r_AB(t-t1))
                +g^2 r_C exp(-r_C(t-h))],                     t1<t<t0;
             s[(1-g)^2 exp(-r_B*u-r_AB*v)
                +g^2 exp(-r_C(t0-h))+2g(1-g)]
                 *r_R exp(-r_R(t-t0)),                        t>t0.

The BB split-routing term has no pre-root coalescence: one block is in B/AB and one is in C. The already-coalesced probability below h is not routed twice. These formulas integrate to one. There are no atoms, and all root tails are finite almost surely.

## 2. Pair laws identify all nine parameters, without a generic exception

Equality of pair laws means equality of their densities almost everywhere; the exponential formulas on open intervals then agree everywhere there by continuity.

- The left endpoint of the support of AC is t0. Its positive tail has log-slope -r_R. This identifies t0 and r_R.
- The left endpoint of the support of AB is t1 because 0<g<1 and r_AB>0. On (t1,t0), the density has log-slope -r_AB, identifying r_AB. Its right limit at t1 is (1-g)r_AB, identifying g.
- The left endpoint of the support of BC is h because g>0 and r_C>0. Its positive density on (h,t0) has log-slope -r_C, identifying r_C.
- The right limit of f_AA(t) at zero is r_A, and that of f_BB(t) is r_B. Both initial intervals have strictly positive length.

This recovers h,t1,t0,r_A,r_B,r_C,r_AB,r_R,g and therefore the original nine parameters. Coincident population rates do not invalidate any step: AB and BC still have their strict support onsets. CC is available as a redundant control, not required for the inference.

## 3. What the finite sequence law gives

Set c=8/3. Choose any nontrivial JC character and apply it to both members of the selected pair, assigning trivial characters to the other four copies. For k sites use this same pair character at every site. Conditional on the ONE shared genealogy, its expectation is exp(-c*k*T_XY). Thus Q_theta,L determines

    m_XY(k)=E[exp(-c*k*T_XY)]

for k=1,...,L by taking these Fourier moments and marginalizing unused sites. The k=0 value is always one. These are not products of separately integrated site probabilities.

## 4. Bounded scalar exponential-polynomial representations

A density piece of the form A exp(-r(t-a)) on a<t<b contributes to its Laplace sample

    A exp(-c*k*a)/(r+c*k)
      - A exp(-r(b-a)) exp(-c*k*b)/(r+c*k).

For b=infinity only the first term remains. Every density in Section 1 is a finite sum of such pieces. Consequently, for that pair and each fixed parameter vector,

    m(k)=sum_(b in B) beta_b^k * A_b(k)/D(k),
    beta_b=exp(-c*b)>0,
    D(k)=product_(r in R)(c*k+r),
    degree A_b <= |R|-1.

Here R is an indexed list of population rates, allowing coincidences, and B is a list of finite calendar boundaries. D(k)>0 for every integer k>=0. The following lists suffice:

    Pair AA: R=(r_A,r_AB,r_R), B=(0,t1,t0).
    Pair BB: R=(r_B,r_C,r_AB,r_R), B=(0,h,t1,t0).
    Pair CC: R=(r_C,r_R), B=(0,t0).
    Pair AB: R=(r_AB,r_R), B=(t1,t0).
    Pair BC: R=(r_C,r_R), B=(h,t0).
    Pair AC: R=(r_R), B=(t0).

Terms at the same boundary are collected. The fact that two indexed rates may be equal causes no difficulty: each linear denominator still divides their indexed product, with the same polynomial-degree upper bound.

For two parameter vectors, multiply the difference of their pair moments by D_theta(k)D_eta(k). The result H(k) is a sum of at most q positive-base exponential terms beta^k P(k), with degree P<=d, using the bounds below. A boundary zero gives the common base 1 in both parameters and is counted only once:

    Pair AA: q<=5, d<=5, recurrence order <=30.
    Pair BB: q<=7, d<=7, recurrence order <=56.
    Pair CC: q<=3, d<=3, recurrence order <=12.
    Pair AB: q<=4, d<=3, recurrence order <=16.
    Pair BC: q<=4, d<=3, recurrence order <=16.
    Pair AC: q<=2, d<=1, recurrence order <=4.

These bounds remain valid when further bases coincide.

## 5. Fifty-five sites suffice

For any term beta^k P(k) of polynomial degree at most d, the operator (E-beta)^(d+1), where E shifts k to k+1, annihilates the term. Multiplying these factors over all at-most-q bases gives a monic constant-coefficient recurrence of order at most q(d+1). Its coefficients may depend on theta and eta; its order bound does not.

The maximum order in Section 4 is 56. Equality of the complete 55-site laws gives equality of each pair moment at k=1,...,55. At k=0 both moments equal one. Hence H(k)=0 for its first 56 consecutive values. A monic recurrence of order at most 56 then gives H(k)=0 for every k>=0. Because the denominators are positive, every pair moment agrees at every nonnegative integer.

For U=exp(-c*T_XY) in (0,1], these are all ordinary power moments. Probability measures on [0,1] are determined by their moments (polynomial density and uniqueness of integrals of continuous functions). The continuous one-to-one transformation T=-(1/c)log U on (0,1] recovers the pair-age distribution; root finiteness means there is no mass at U=0. Thus the pair laws agree. Section 2 gives theta=eta and proves the statement.

## Prior attribution and limits

A close biological precedent is Thawornwattana, Huang, Flouri, Mallet and Yang, *Inferring the Direction of Introgression Using Genomic Sequence Data*, Molecular Biology and Evolution 40(8), msad178 (2023), https://academic.oup.com/mbe/article/40/8/msad178/7239274 . It uses pairwise coalescence-time laws for introgression identifiability and explicitly explains applicability to selected pairs in larger sample configurations. Its pair-law technique and parameter-identifiability analysis are prior work, not claimed as new here. The additional candidate conclusion here is the explicit 55-site exact-law implication under our fixed six-copy source contract. Pairwise coalescence-time calculations and their Laplace transforms are standard MSC/MSci tools. JC eigencharacters, compact moment determinacy and exponential-polynomial recurrences are classical. Zhu–Yang (2021) previously treated two-site identifiability in a different three-species, one-copy, no-pulse model; Durden–Sullivant (2018) obtained JC coalescent k-mer identifiability with a common population size. Neither is silently claimed as this nine-parameter pulse contract, and novelty of the assembled result remains unverified.

This proof is about exact distributions at the stipulated fixed clock and sampling/model assumptions. It gives no finite number of loci needed for accurate estimation, no numerical robustness near limiting parameters, no empirical model admission, no continuous-migration extension, no unknown-rate substitution extension, and no conclusion uniform over unbounded graph complexity. The original G3 and full-menu G4 obligations remain open. This is not a Lean proof.
