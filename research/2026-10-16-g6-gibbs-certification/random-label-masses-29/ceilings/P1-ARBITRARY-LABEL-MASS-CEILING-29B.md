# Arbitrary common label masses cannot improve this alphabet's polynomial testing power

17 October 2026, 23:09 UTC. Author: dot (OpenAI), working with Nolan.

Status: candidate hand-proof boundary, submitted for review. It supplies a testing ceiling for a declared conditional-product alphabet, not an upper bound for arbitrary Gibbs states or a historical-novelty claim. It strengthens the specific family29 ceiling by allowing any common label probability vector and any number of mass scales.

## 1. Declared statistical class and conclusion

Let `D>=2`, `s>=3`, `0<alpha<=1/2`, `ell=1/s`, `h=1/2`, and `delta=alpha/s` be known. Each sample is a visible label `i in [D]` and a complete string of `s` bits. The two sources have an arbitrary UNKNOWN but common label distribution `pi`, allowing zero probabilities. Conditional on a label, the bits are independent. Samples are independent over time.

The coordinate pairs belong to this fixed alphabet:

- Equal heavy: `(p,q)=(h,h)`.
- Equal light: `(p,q)=(ell,ell)`.
- Differing light: `(p,q)=(ell+sigma delta,ell-sigma delta)`, with unknown `sigma in {+1,-1}`.

On a null every coordinate is equal. On an alternative there is an unknown label set `J` of total mass at least `1/6`, each of whose labels has at least `s/3` differing-light coordinates. Other labels may contain any alphabet coordinates. This condition includes the retained alternatives of29. It is an explicit stronger promise than arbitrary full-trace-distance separation of general Gibbs states.

Put

    L=ceil(32 log(D+2)), C=10^6,
    n=ceil(C s D^(2/3) L^(2/3)/alpha^(4/3)).         (1)

Assume `n<=DL`. The procedure below has a worst-case ideal-row budget `6n` and an explicit error upper bound tending to less than `0.01` along the regimes of interest. For fixed `k>=5`, `D=binom(s,k-1)` and fixed positive alpha, the condition `n<=DL` holds for sufficiently large s. The resulting ceiling is

    O_alpha(D^(2/3) s (log(D+2))^(2/3)).             (2)

The guarantee is uniform over every permitted `pi`, every null and every declared alternative. It is not prior-average testing. The tester never receives `pi`, the labels in `J`, coordinate types or signs.

## 2. Pilot construction: observable label splitting

Use an independent `Poisson(n)` number of complete rows from the first source as a pilot, discarding its data bits. Abort if its total exceeds `2n`. Let `A_i` be the pilot label counts and define known positive integers

    K_i=L+2A_i.

For every later sample with label i, attach an independently uniform artificial index `j in [K_i]`. The enlarged label `(i,j)` is classical random postprocessing; no physical qubit, source parameter or additional oracle is introduced. The complete data string is unchanged. Both sources use the same observed pilot and the same splitting rule.

For the analysis, first consider the untruncated pilot: the `A_i` are independent `Poisson(n pi_i)`. Let E be the event that its total is at most `2n` and `K_i>=n pi_i` for every i. If `n pi_i<=L`, the latter inequality holds deterministically. Otherwise its failure implies `A_i<(n pi_i)/2`, with probability at most `exp(-n pi_i/8)<=exp(-L/8)`. Thus

    Pr(E^c)<=exp(-n/3)+D exp(-L/8)
             <=exp(-n/3)+D/(D+2)^4.                (3)

No test of the unknown inequalities is performed by the algorithm; E is only a proof event. On E,

    sum_i K_i=DL+2sum_i A_i<=DL+4n<=5DL,            (4)
    n pi_i/K_i<=1.

The expected flattening bound also holds without E. Since `K_i>=1+A_i`, for `pi_i>0` the Poisson identity gives

    E[1/(1+A_i)]=(1-exp(-n pi_i))/(n pi_i),
    E[sum_i pi_i^2/K_i]<=1/n.                      (5)

Zero-mass labels contribute zero. The two uses of the pilot differ: (3)--(4) lower-bound signal collisions on a high-probability event; (5) controls the unconditional variance without incorrectly conditioning an expectation bound on E.

## 3. Fresh complete-row counts and a labelwise paired statistic

Independently draw fresh `Poisson(n)` totals from each source and split their labels with the observed pilot. Abort if either fresh total exceeds `2n`. Conditional on the untruncated pilot, counts from the two sources at an enlarged label `(i,j)` are independent Poisson variables of mean

    nu_i=n pi_i/K_i.

For each enlarged label with at least one row from each source, use only the first row from each. All `s` coordinates share that single row pair. This does not create independent coordinate clocks. The used pairs are disjoint, so their bits are independent conditional on the counts and the fixed source parameters.

For a paired bit `(X,Y)` define

    f(X,Y)=XY-(h+ell)(X+Y)/2+h ell,

the statistic already used in component27 and addendum29A. Its absolute value is at most one. An equal coordinate has mean zero; a differing-light coordinate has mean `-delta^2`. Let Z be the sum over every selected pair and its `s` bits. Let K denote the number of selected enlarged labels and K_J those originating in J. Conditional on pilot, counts and source parameters,

    Var(Z)<=sK,
    E Z=0 on every null,
    E Z<=-alpha^2 K_J/(3s) on every alternative.     (6)

Other alphabet coordinates never contribute positive mean, so extra differing labels cannot cancel the signal.

## 4. Signal collisions for arbitrary unknown masses

On E, `0<=nu_i<=1`; the probability of both source counts being nonzero at `(i,j)` is at least `nu_i^2/4`. Hence

    E[K_J | pilot]
      >=(n^2/4) sum_(i in J) pi_i^2/K_i
      >=(n^2/4) (sum_(i in J) pi_i)^2/(sum_(i in J) K_i)
      >=n^2/(720DL)=:m0.                            (7)

The middle inequality is weighted Cauchy--Schwarz. The last uses mass at least `1/6` and(4). Conditional on the pilot, enlarged-label occupancy events are independent. Therefore

    Pr(K_J<m0/2 | pilot in E)<=exp(-m0/8)
                              =exp(-n^2/(5760DL)).  (8)

Neither E, J, nor K_J is supplied to the test. They only justify a deterministic threshold computed from known D,s,alpha,n,L.

## 5. Variance, threshold and all error terms

For any nonnegative nu, `(1-exp(-nu))^2<=nu^2`. Thus, still considering the untruncated experiment,

    E[K | pilot]<=n^2 sum_i pi_i^2/K_i,
    E K<=n,
    E[ Var(Z | pilot, counts, source) ]<=sn.         (9)

Set

    tau=alpha^2 m0/(12s)=alpha^2 n^2/(8640sDL).

Reject equality if `Z<-tau`. On a null its conditional mean is zero for every pilot and count array. On an alternative satisfying(8), (6) gives a conditional mean at most `-2tau`. Apply Markov's inequality to the squared deviation from this conditional mean and then average over the pilot and counts. Equation(9) yields the common noise-error bound

    sn/tau^2 =8640^2 s^3 D^2 L^2/(alpha^4 n^3)
              <=8640^2/C^3 < 10^(-9).              (10)

This argument does not substitute an unconditional alternative mean for the random conditional mean. It separately controls the event that the conditional signal is sufficiently large.

The pilot and both fresh Poisson totals each exceed `2n` with probability at most `exp(-n/3)`. Including these observable abort events, (3), (8) and (10) give the following conservative upper bound on either error:

    3exp(-n/3)+D/(D+2)^4
        +exp(-n^2/(5760DL))+8640^2/C^3.              (11)

The null does not need the last two signal-related events, but the common bound is convenient. This proves a worst-case `6n` ideal-row budget: the pilot, first-source fresh batch, and second-source fresh batch are each capped at `2n`. Poisson variables are internal randomness; no unbounded or merely expected sample budget is hidden in the statement.

For `D=binom(s,k-1)`, fixed `k>=5` and fixed alpha, `n/(DL)` tends to zero, `n` diverges and `n^2/(DL)` diverges. Thus(11) is eventually below `0.01` uniformly over all allowed source parameters.

## 6. Transfer to the encoded Gibbs family and its limitation

For29's physical encoding, measure in the computational basis and keep the known ideal event. It has probability at least `1-eta>=0.99`; conditional data are exact ideal rows. Take `16n` physical copies from each source. Each supplies `4n` retained rows except with probability at most `exp(-n)`, by the binomial lower-tail bound. Reserve `2n` first-source rows for the pilot and another `2n` for its fresh batch; reserve `2n` second-source rows for its fresh batch. All retained row values are IID conditional on the fixed physical source and independent of retention indicators. After the pilot is processed, the unused fresh arrays remain independent of it.

The resulting physical cap is `32n` TOTAL copies, and the extra error is at most `2exp(-n)`. Spectator qubits can be ignored. The splitting indices are produced from measured labels and random bits, not encoded physical spins.

More generally the same ceiling applies to any proposed mass-only extension that retains this coordinate alphabet, the constant-mass signal promise, and a known exact conditional-row extraction with uniformly positive retention. If a new physical construction does not supply those conditions, this transfer cannot be asserted. Arbitrary tiny masses need not admit29's particular efficient Hamiltonian encoding; the statistical theorem does not assume that they do.

## 7. Consequence and attribution

The specific family29 has the sharper `O(B)` ceiling in29A. The present broader ceiling has an extra logarithmic factor but allows every common label distribution. It rules out improving the polynomial exponent simply by introducing more common label-mass scales while retaining the declared conditional-product alphabet and extraction contract. It does not rule out changing conditional laws, allowing different label marginals, or a genuinely noncommuting hard family. None of those changes currently inherits this proof or supplies a new P1 lower bound.

Random splitting of heavy probability bins is classical. The directly checked primary source is Diakonikolas and Kane, *A New Approach for Testing Properties of Discrete Distributions*, arXiv1601.05557v2, Definition2.4, Fact2.5 and Lemma2.6, PDF pages7--8: https://arxiv.org/pdf/1601.05557v2 . Those passages give sample-based split distributions and their expected squared-norm control. The logarithmic padding, paired-coordinate statistic and bounds above are supplied explicitly here; historical novelty of this specialization is not established.

The paired statistic is preserved in component27, Section7: https://github.com/Sodelin/Research-Commons/blob/0daba51d070c50bc10153a9272eab0e436484841/research/2026-10-16-g6-gibbs-certification/averaged-shared-counts-27/P1-AVERAGED-COUNTS-CANDIDATE-27.md .

Component29 and its exact physical limits: https://github.com/Sodelin/Research-Commons/blob/603e52474aa12a2b7f0131a02e6508249d9dc616/research/2026-10-16-g6-gibbs-certification/random-label-masses-29/README.md .

The original fixed-beta, coefficientwise-bounded, arbitrary-noncommuting optimal-copy problem remains open. This is a specialized upper-bound obstruction to one lower-bound strategy, not a full-class testing algorithm or Lean proof.
