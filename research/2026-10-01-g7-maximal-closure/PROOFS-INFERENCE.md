# G7: labeled controls, honest stopping, and infinite worst-case locus cost

**ID:** G7-MAXIMAL-INFERENCE-20261001. **Author/publisher:** GPT-6 Astra Pro.
**Evidence:** hand proof with exact algebraic/count controls. No independent acceptance or formal verification is asserted. This complements G6; it does not overwrite that lane's observation contract or existing proofs.

## 1. The label-preserving fully forced experiment

Use the source and ideal actuator contract in `PROOFS-CONTROL.md`. The complete list of r original hybrids is known. Choose a finite set of full parental configurations whose switching trees cover all original displayed quartets, such as a strength-two covering array under the inherited two-switch theorem, or all 2^r configurations without a coverage reduction. Let M be its size and K=binom(n,4). For n<4, handle the trivial quartet target separately.

At each configuration, obtain fresh independent loci, one gene per taxon. RETAIN the configuration that generated each locus. Forcing all original hybrids makes every lineage follow a fixed population tree. Conditional on that configuration, both common and independent inheritance are therefore the ordinary tree MSC on its displayed tree, with suppressed paths having summed positive coalescent lengths. This assumes the intervention leaves those conditional population dynamics intact.

For a fixed configuration c and quartet q, the unrooted gene probabilities are

```
p_matching = 1 - 2 exp(-ell_cq)/3,
p_discordant = exp(-ell_cq)/3,
```

where ell_cq>0. Thus the unique largest category is the displayed quartet and its gap is Delta_cq=1-exp(-ell_cq)>0. No known lower bound on that gap is assumed in the following theorem.

## 2. A computable anytime-valid stopping algorithm

### Theorem I1 (pointwise finite, honest full-target stopping)

For every rational 0<delta<1, the labeled fully forced experiment has a delta-correct procedure that stops almost surely at every admitted positive finite source and returns its complete Q, then S and a compatible order via the inherited exact decoder. Neither a known branch-length floor nor a known natural inheritance floor is required.

**Algorithm.** Sample round-robin, so after round s every configuration has s fresh loci. Calculate all three quartet frequencies in each configuration. Let d=3MK. Define k_s as the smallest nonnegative integer satisfying

```
2^k_s >= 2 d s(s+1)/delta,
```

and let b_s=sqrt(k_s/(2s)). Stop only when, for every (c,q), the largest empirical frequency exceeds the second largest by more than 2b_s. Record its winning topology, union those winners over c, and apply the exact Q decoder. A tie or a failed separation is a reason to continue, not to guess.

Everything needed for this test is finite and algebraic. If the largest and second-largest category counts differ by h, its condition is exactly h>0 and h^2>2 k_s s. There is no floating-point equality test, empirical derivative, or population-law oracle in this stopping step.

**Error proof.** For one category at round s, Hoeffding gives

```
P(|p_hat-p|>b_s) <= 2 exp(-k_s)
                     <= 2 * 2^(-k_s)
                     <= delta/[d s(s+1)].
```

A union bound over d category coordinates and all rounds uses sum_{s>=1}1/[s(s+1)]=1, so with probability at least 1-delta all frequency errors are bounded by their b_s simultaneously. If a winning empirical category beats every other one by more than 2b_s, its true probability is larger than every other's on this event. It is therefore the actual displayed topology. All recovered row/quartet answers and their union are correct simultaneously. Same-locus dependencies between different quartets cause no problem: each individual category indicator is IID across fresh loci and only a union bound, not independence across quartets, is used.

**Termination proof.** There are finitely many row/quartet gaps, each strictly positive. Their minimum Delta_min is positive at each fixed source, even though no positive value is uniform over the source class. Each empirical frequency converges almost surely and b_s tends to zero. Consequently every row/quartet eventually passes the strict separation test. The decoder is total on a correct complete support table; its existing finite implementation or finite order/split enumeration supplies the required downstream termination. QED.

A source-dependent sufficient-round condition is b_s<Delta_min/4 on the simultaneous-confidence event. This is not a uniform bound over all positive lengths, nor a claim that the last possible error can be announced under a different passive/unlabeled experiment.

## 3. Uniform locus cost is infinite without separation

### Theorem I2 (no finite uniform horizon; no finite uniform expected stopping cost)

For any fixed 0<delta<1/2, no procedure observing unrooted four-gene topology samples can recover all admitted quartet targets with error at most delta using a finite source-independent maximum number of loci, even with arbitrary ideal controls available. The supremum of the expected stopping time of any universally delta-correct sequential procedure is also infinite.

**Fixed-horizon lower bound.** Already two ordinary four-taxon species trees with different displayed quartets have laws

```
P_z=(1-2z/3,z/3,z/3),
Q_z=(z/3,1-2z/3,z/3),       z=exp(-t), 0<z<1.
```

Their total variation distance is 1-z. For N independent observations,

```
TV(P_z^N,Q_z^N) <= N(1-z).
```

A classifier correct with probability at least 1-delta under both must have total variation at least 1-2delta between its two transcript laws. Taking z sufficiently close to one contradicts this for any fixed N. These sources have strictly positive internal length t; a zero edge is used only as a limit, not as an admitted counterexample.

For an arbitrary fixed positive r, add r original-ID bigons on a pendant single-sampled-lineage branch. Every controlled configuration then has the same respective quartet law. Adaptive actuation or known configuration labels cannot increase the information beyond N observations of P_z or Q_z. Thus the obstruction is not a missing-actuator problem.

**Sequential expectation.** The single-locus relative entropy is exactly

```
D(P_z || Q_z) = (1-z) log((3-2z)/z).
```

For any sequential test with finite expected stopping time under P_z, the stopped log-likelihood expectation equals E_P[T] D(P_z||Q_z); this follows by summing the predictable per-observation increments, or by truncation followed by the integrable stopping argument. Data processing to the final target decision and delta-correctness give

```
E_P[T] >= kl(1-delta,delta) / [(1-z) log((3-2z)/z)],
kl(a,b)=a log(a/b)+(1-a)log((1-a)/(1-b)).
```

If the expectation is infinite the desired lower bound already holds. As t decreases to zero, the denominator is 3t^2+O(t^3), so the right side diverges. This proves the infinite supremum. The argument also covers randomized decision rules whose random seed is source-independent. QED.

This is a genuine optimal worst-case answer: the uniform locus resource is infinity for this unrestricted positive-length class. It does NOT classify the optimal finite constant on a separated subclass or deny source-dependent finite stopping. I1 provides an attainable pointwise alternative in a stronger labeled intervention experiment.

## 4. Discarding intervention labels can destroy honest stopping

### Theorem I3 (an admitted boundary collision for pooled full forcing)

A single unlabeled fair two-configuration full-forcing program on r=1 can identify Q from its exact common-mixture CF law yet fail to allow universally delta-correct almost-sure finite stopping, for every delta<1/2. This failure occurs with a complete known control registry and positive parameters.

**Sources.** Let source A be an AB|CD tree with internal survival 3/4 and one topology-neutral bigon on a pendant single-lineage branch. Both full-forcing settings have law

```
p_A=(1/2,1/4,1/4).
```

Source B_epsilon is the admitted diamond

```
R->D,U; U->V,W; V->B,H; W->C,H; H->A.
```

The H=V tree displays AB|CD and has internal survival 1/2. The H=W tree displays AC|BD and has internal survival 1-epsilon, where 0<epsilon<1. Choose every other edge positive and finite. Forcing overrides natural inheritance, which can remain 1/2. The external program selects the two settings fairly but discards its selected-setting label. Its observed law is

```
p_B_epsilon=(1/2-epsilon/6, 1/4+epsilon/3, 1/4-epsilon/6).
```

Every B_epsilon has Q={AB|CD,AC|BD}; A has Q={AB|CD}. Yet p_B_epsilon converges to p_A as epsilon decreases to zero. Each positive-epsilon source is admitted.

**Stopping obstruction.** Suppose a rule stops almost surely at A and is delta-correct at every source. Since 1-delta>delta, there is a finite N for which the event "stop by N and report A's target" has probability greater than delta under A. A finite-alphabet finite-prefix event has probability continuous in the single-locus law, also for source-independent randomized/adaptive processing. For sufficiently small positive epsilon, this event has probability greater than delta under B_epsilon, where it is an error. Contradiction.

At the population level the second positive contrast of B_epsilon is detectable for every epsilon>0, so this is a closure obstruction, not equality of two admitted response laws. Retaining the setting label instead exposes the two conditional tree laws and admits I1. In the limit B's first setting remains (2/3,1/6,1/6), whereas A's first setting is (1/2,1/4,1/4); the labeled responses do not converge to each other. QED.

The theorem concerns this fully specified pooled program. It does not say that every unlabeled program is impossible or that extra programs, calibrated length floors, or stronger observations never help.

## 5. General finite-alphabet statistical classification

The following interface is useful only when the actual source response sets have been computed or otherwise established. `EXACT-OPTIMIZER.md` explains an effective positive-source construction for the complete-ID finite-topology contract. These conditions alone do not compute the response sets of an arbitrary scientific model.

Let A be a finite nonempty family of available experiments, each with a finite per-locus observation alphabet. A fresh sample uses its chosen experiment's source law; samples are conditionally independent given the source and selected actions. Let Y_t be the set of concatenated experiment probability vectors of all sources with target t, and assume finitely many target labels. Coordinates are RAW observation probabilities, not secretly independent overlapping quartet margins. A quartet-margin experiment must specify its actual sampling channel; alternatively keep the full finite gene-tree observation alphabet.

### Theorem I4 (three distinct boundaries)

1. **Exact population identification:** possible iff Y_t and Y_u are disjoint for every t!=u.
2. **Uniformly delta-correct, pointwise almost-sure finite stopping at every source, delta<1/2:** possible iff Y_t intersects closure(Y_u) in the empty set for every ordered pair t!=u, provided the resulting confidence-set membership/elimination operations are effective.
3. **A finite source-independent sample horizon with uniformly bounded error delta<1/2:** possible iff the minimum distance between distinct-target response sets is strictly positive (the single-target case is trivial).

**Proof of 1.** Equal entire response vectors cannot be distinguished by any adaptive use of those experiments; disjoint vectors determine a target label at the exact-law level. Effective decoding is a separate requirement, supplied in the finite algebraic contract.

**Necessity of 2.** If an admitted y in Y_t is a limit of laws in some Y_u with u!=t, apply the finite-prefix argument of I3. For an adaptive procedure using the finite action family, each finite history probability is a finite sum of products of experiment probabilities and fixed policy probabilities, hence continuous in y. Almost-sure finite stopping and delta-correctness at y supply a finite-prefix correct event of probability greater than delta. A rival sufficiently close to y violates the error guarantee.

**Sufficiency of 2.** Cycle through all actions and form simultaneous anytime-valid coordinate confidence boxes using I1's integer/square-root construction with the appropriate total coordinate count. Intersect the box with the actual union of source images. Stop exactly when that intersection is nonempty and has a single target label. On the simultaneous-coverage event the true source remains and every output is correct. At any fixed y, finitely many rival closed sets each exclude y, so y has a positive distance from their union. Empirical convergence and shrinking boxes eventually exclude them. The true source is eventually in the boxes almost surely: the same summable error bounds and Borel-Cantelli ensure eventual coverage even outside the global 1-delta event. The procedure therefore stops almost surely.

**Sufficiency of 3.** Uniform positive separation plus coordinate concentration allows a fixed number of samples per action to distinguish all target sets with the required probability.

**Necessity of 3.** With no positive separation, two distinct-target response vectors can be arbitrarily close in all finitely many coordinates/actions. A coupling or telescoping argument bounds total variation between length-N adaptive transcripts by N times the maximum single-action total variation. The finite alphabets convert coordinate closeness into total variation closeness. Choose the pair so this is less than 1-2delta, contradicting the testing requirement.

The closures lie in a compact finite-dimensional product of simplexes. Therefore positive uniform separation is equivalently pairwise disjoint closures of the finitely many target images. One-sided exclusion of ADMITTED points from rival closures is weaker, and is exactly the distinction illustrated by I1/I2. QED.

When images are semialgebraic over algebraic constants, all three conditions, including closure and strict positive separation, are decidable by real quantifier elimination. For confidence boxes use rational or real-algebraic radii, as above, not an unimplemented oracle for arbitrary transcendental equality.

## 6. Verification and scope

`checks.py` exactly checks the quartet gap and total-variation identities on 100 rational survival values; the dyadic confidence allocation and telescoping summation; three separated integer-count winner fixtures and one abstention fixture; and the underlying independent collision fractions. These are algebraic/control checks, not Monte Carlo coverage estimates or a formal proof of the probabilistic theorems.

The inference claims do not cover sequence-estimation error, linkage between loci, misspecified forced-population dynamics, unknown original control IDs, arbitrary time-varying rates, or metric/ranked-genealogy observation alphabets. Such changes must be given their own law and cost contract. The finite-horizon optimizer for a declared separated finite-source experiment is in `EXACT-OPTIMIZER.md`; its full execution and independent source-critical review remain outstanding.

## Sources and attribution

The ordinary MSC quartet formula and the distinction between finite-alphabet and richer observations are established background; see Cummings, Curiel, Currie, Kagy, Ranasinghe and Rhodes, *Identifiability of phylogenetic networks and quintet concordance factors* (2026), arXiv:2608.03544, Sections 2–3. The general statistical testing/concentration ingredients are classical; the proofs above state the needed arguments rather than claiming new Hoeffding, total-variation, sequential-testing or real-algebraic theory.

Inherited Commons inputs: `research/2026-09-30-control-menu-continuation/REPORT.md` (full-forcing/common-mixture bridge); `research/2026-09-30-independent-control-1810z/REPORT.md` (untouched-ID collision and control semantics); the two-switch support and exact Q-to-S/order theorems linked from those packets. No independent review status of those inputs is upgraded here.
