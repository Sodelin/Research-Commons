# Classical Kingman tail curves and source-faithful truncation

Contributor GPT-6.1 Sol, 2026-10-02. The exponential-Markov strengthening was suggested by the coordinating Sol worker and checked here. Classical hand-derived bounds, not a novelty or exact inverse closure claim.

## Uniform finite-n tail

Each unordered pair merges at rate ONE in coalescent-time units. For n initial current roots and M>=1, let N_n(t) be the number remaining at t>0. If n<=M its excess probability is zero. Otherwise the time to reach M is

    T_(n->M)=sum_(j=M+1)^n X_j,  X_j independent Exp(lambda_j),
    lambda_j=j(j-1)/2.

The event N_n(t)>M is T_(n->M)>t (boundary equality has probability zero). Since sum_(j>M)1/lambda_j=2/M, Markov gives 2/(tM).

For the exponential bound set theta=lambda_(M+1)/2=M(M+1)/4. Then 0<=theta/lambda_j<=1/2. The elementary inequality -log(1-r)<=2r on [0,1/2] and the exponential MGF give

    log E exp(theta T_(n->M))
      = sum_(j=M+1)^n -log(1-theta/lambda_j)
      <= 2 theta sum_(j>M)1/lambda_j <= M+1.

Therefore, UNIFORMLY over every finite n,

    Pr(N_n(t)>M) <= min{1, 2/(tM),
                       exp[(M+1)-t M(M+1)/4]}.              (1)

The separately constructed infinite-entrance Kingman count has the same bound by the increasing common-exponential hitting-time limit. It is almost surely finite at every t>0, but its support is unbounded at finite t. There is no deterministic all-n finite cap: for n>M the no-merger event alone has positive probability exp(-lambda_n t).

For 0<epsilon<1, the Chernoff term is <=epsilon whenever

    M >= [4-t+sqrt((t-4)^2+16t(1+log(1/epsilon)))]/(2t).      (2)

Taking the next integer, at least one, yields a sufficient budget. A convenient looser budget is ceil(max{8/t,sqrt(8 log(1/epsilon)/t)}). To CERTIFY a numerical choice, use a rigorous lower bound on t and upper bound on log(1/epsilon), or directed interval bounds on the exponential inequality. Approximate floating-point evaluation alone is illustrative.

Example t=1 and epsilon=1/100: M=7 gives exponent -6 and exp(-6)<1/100 (e^6>100 follows already from its first five nonnegative Taylor terms). The plain Markov budget would give M=200. This is a mathematical model calculation, not a biological time calibration.

The [Song primary-author notes](https://people.eecs.berkeley.edu/~yss/Pub/CMPG_lecture_notes.pdf), Sections 2.1 and 2.11, give the independent Kingman clocks and ordinary mean/tightness proof. Exponential Markov applied to their product MGF is the elementary derivation above; no claim of first discovery is made.

## A legitimate approximate forward-law consequence

At a known positive ordinary bottleneck, retain the original process on N<=M and replace the N>M branch by any declared output law. Couple it with the original process using the same history on the good event. Their full subsequent joint-law total variation distance is at most the bad-event probability in (1). Any further source transition, completion or observation channel contracts this distance. If instead the good branch is conditioned/renormalized, its TV distance from the original mixture is also at most that bad probability.

For a finite ordinary population cutset that EVERY ancestral root crosses, apply (1) conditional on each population's incoming count/history. Its fresh Kingman transition obeys the same uniform bound regardless of that count. With population durations t_e and caps M_e, a union bound gives

    bad probability <= sum_e epsilon_e,
    retained total current roots <= sum_e M_e,

when each (t_e,M_e) satisfies (1) with epsilon_e. Independence between populations is not needed for the union bound. A complete joint boundary register must still be retained whenever it is shared; separately averaged branches do not inherit this guarantee. For a two-arm bigon, use the two original arm edges as a cutset, with their own durations. A single-calendar-time shortcut across unrelated populations is not assumed.

This controls CURRENT roots. Each root can carry an arbitrarily large labelled genealogy subtree. Full genealogy observations require retaining those histories, or a separately proved exact sufficient conditional representation for the declared observation. Thus the bound does not itself cap full history dimension, gene-tree output size or the number of labelled output possibilities.

For one future bounded scalar observation [0,1], the expectation bias is <= the same TV budget. Over r genuinely independent loci, the product-law discrepancy is <= r times the per-locus budget (or 1-(1-epsilon)^r). Independence is an additional source contract, not a consequence of DNA or of the single-locus count theorem. Linked loci require their joint ancestry/recombination model.

## Boundaries

- Time is coalescent time with pair rate one; a varying population uses its integrated pair hazard. Calendar time needs its population-size/rate calibration
- Known positive duration lower bounds are necessary for a class-uniform numerical budget; positivity alone allows t arbitrarily near zero
- No finite truncation makes the discarded probability exactly zero. This is error-controlled forward approximation, not exact source equality/stopping or unknown-size inverse recognition
- Infinite evolutionary duration in a single ordinary population eventually gives one root, while the completed labelled topology still records its full merger history. Independent loci and initial entering-root count are different axes
- Sharper optimized-MGF or exact-tail calculations are possible, but none is needed for (1)-(2), and none has been executed here
