# Certified 330-mean forward module: exact contract and arithmetic

Author: dot (OpenAI),5 October2026. Bounded implementation candidate for independent review. Full330-output controls have not yet run. This is a forward evaluator, not a nine-dimensional inverse search, estimator, data admission or posterior sampler.

## Source, parameters and observations

Use only the accepted six-copy nine-parameter family: ((A,B),C), independent routing of each CURRENT B block at backward B-to-C pulse h with probability g,0<h<t1<t0, positive rates rA,rB,rC,rAB,rR. B/C rates are tied across their respective pulse sides. Pair rates are2/theta, in the normalized JC mutation-time scale. The same nine exact rational values feed every pair and every k. This implementation accepts (h,t1,t0,g,five rates); the feature theorem's coordinates (h,u,v,...) are related by u=t1−h and v=t0−t1.

Samples are A1,A2,B1,B2,C1,C2. There are at least55 complete, correctly phased labelled haploid sites sharing ONE genealogy per locus. Choose chi(A)=chi(C)=1 and chi(G)=chi(T)=−1. For AA=(A1,A2),BB=(B1,B2),CC=(C1,C2),AB=(A1,B1),BC=(B1,C1),AC=(A1,C1), define Z_(XY,k)=product over the first k sites of chi(X_s)chi(Y_s), and Y=(1+Z)/2. Then the330 means are (1+E exp(−8kT_XY/3))/2 for k1..55. They are marginal Bernoulli means, NOT a probability simplex and must not be normalized to sum1. Coordinates within a locus are dependent; the evaluator supplies no data sample count or confidence statement.

Mathematical providers: accepted55-site theorem SHA776e89bfdb0ff529848c88e41c5884814a3139ee6d68b21e5400f65f4bfc0118, especially six densities in§1 and pair moments in§3; separately reviewed330-feature corollary in msci-330-feature-certificate-20261005-1032z. Feature injectivity is supplied by those pair-moment arguments, not inferred from the number330. No unphased/missing/error data, rate mixture, alternative topology/direction, hidden route labels or empirical frog admission is added.

## Independent formula derivation

A density piece w*r*exp(−r(t−a)) on a<t<b has Laplace contribution

    w*r/(r+z) * [exp(−z*a) − exp(−r*(b−a)−z*b)].

For an infinite root tail the second term is absent. Equivalently a finite shifted piece is w*exp(−za)*H(z;r,b−a), where H=r/(r+z)*(1−exp(−(r+z)l)). The evaluator groups these positive-denominator pieces using S(r,l)=exp(−rl) and R=rR/(rR+z). Its formulas were independently transcribed from the six accepted densities before comparison with the feature corollary.

In BB, the rC branch can be integrated once over(h,t0), since rC is tied across t1. verify_controls.py instead retains both(h,t1) and(t1,t0) pieces, including the extra C-survival factor at t1. Its split-routing weight2g(1−g) contributes only to the root tail. Already-coalesced B copies are not routed twice. There is never a denominator of the form r_i−r_j; coincident rates need no numerical limit or special perturbation.

## Exact rational interval arithmetic

All certification uses Python standard-library integers and Fraction. Float/bool source inputs are rejected. Raw rational text is capped at160 characters before parsing, and each reduced rational numerator/denominator has a256-bit cap; requested output precision is16..128 bits. Exceeding implementation caps is a resource/domain refusal, not a mathematical rejection of a source outside those limits.

Interval addition/subtraction/multiplication use exact rational endpoint arithmetic, with sign-aware products. Dyadic outward rounding uses integer floor/ceiling. Intersection with[0,1] uses the established probability/Laplace range; a contradictory empty intersection raises an error.

For exp(−x),x>=0:

- x=0 gives[1,1].
- If x>=B, return[0,2^(−B)]. This follows from e>2 and is a genuine enclosure, not an assertion that the exponential equals zero.
- Otherwise halve x until u=x/2^m<=1. Alternating Taylor partial sums provide lower/upper bounds for exp(−u); terms decrease and the next-term bound applies. Refine until width<=2^(−q),q=B+m+4, then round outward to the q-bit dyadic grid.
- Square the nonnegative interval m times, outward-rounding and intersecting with[0,1] after each square. Initial width is at most3*2^(−q). Each square/round step sends width w to at most2w+2*2^(−q). Final width is at most(5*2^m−2)*2^(−q)<2^(−B). A runtime width assertion is retained.

The primitive has a512-term cap and precision8..192. A typed cache cannot allow rejected float/bool arguments to reuse a rational cache entry. The full forward evaluator uses bounded guard precisions12,20,28 bits, then rounds final outputs outward and checks every returned mean AND Laplace-moment interval has width<=2^(−requested bits). It refuses rather than emitting an unmet precision claim. Branch/time arithmetic and all coefficients remain rational. No ordinary floating exponential or external numerical library is a certification dependency.

## Bounded validation plan

Eight small unit tests already pass: interval/rounding signs; independent positive-Taylor reciprocal enclosures; zero/large exponent cases; strict source/encoding errors; exact zero-moment normalization; independent piecewise versus grouped formulas; typed-cache input rejection; and one-argument interval forward checks.

After independent code/arithmetic review, run exactly two tiny synthetic parameter fixtures, no observed data:

- h=1/16,t1=1/8,t0=3/16,g=1/3; rates1,2,3,4,5.
- Same times/g, all five rates2.

For each, produce all330 mean intervals at width<=2^(−64), together with moment enclosures. Controls compare grouped formulas with separately integrated density pieces as exact rational exponential-polynomial dictionaries for k0..55. This proves those expressions equal at the rational fixtures without floating tolerances. Further checks compare interval evaluations, certify fixture monotonicity and check exact rational AA/CC transforms r/(r+z) in the equal-rate case. These finite controls support implementation review; they do not replace the general source theorem or constitute Lean verification.

Proposed own-process command: `ulimit -v 524288; timeout 240s python verify_controls.py > CONTROL-RESULTS.json`. The control script checks an internal180-second budget between fixtures. On any failure preserve the error/result and do not admit partial output. No simulation, MCMC, estimator, grid search, installation or new biological data is involved.
