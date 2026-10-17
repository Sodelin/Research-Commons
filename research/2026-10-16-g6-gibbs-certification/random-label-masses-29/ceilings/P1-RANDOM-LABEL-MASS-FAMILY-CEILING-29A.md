# The testing ceiling of the random-label-mass family

17 October 2026, 23:05 UTC. Author: dot (OpenAI), working with Nolan.

Status: hand-proof addendum submitted for review. This assesses the specific accepted family in component29. It is not an upper bound for general local Gibbs states, a novelty claim, or closure of P1.

## 1. Exact scope and conclusion

Use exactly component29's fixed `k>=5`, `beta>0`, `0<epsilon<=1/1024`, sufficiently large `s`, `r=k-1`, `D=binom(s,r)`, and

    alpha=512epsilon, ell=1/s, h=1/2, delta=alpha/s,
    mu=s/[1600alpha^(4/3)D^(1/3)], B=Dmu.

The known family description includes these deterministic parameters and its clone/data/reservoir encoding. Its unknown members are the mass types, coordinate types and signs. No unknown parameter is supplied to the tester.

Nulls have the exact equal coordinate probabilities of29. Alternatives are every latent draw in29's far event `F`: every label has at least `s/3` light coordinates and the heavy-mass label count `H` is at most `2B`. Thus `W>=B` always, and on an alternative `W<=3B`, with at least `D/2` signal labels. This is a pointwise family promise, not an average over its prior.

**Claim.** This declared family, including its actual encoded Gibbs states and the spectator padding of29, is testable with `O(B)` worst-case TOTAL copies at constant success probability. It therefore has a matching order to29's lower bound, with the construction parameters fixed. Its same two-mass mechanism cannot automatically reach the full original `O(N^k log N)` upper.

The proof uses the paired-bit statistic already supplied in component27, with a new count calculation for29's shared unknown label masses.

## 2. Statistic and pointwise means

For a first-source bit `X` and second-source bit `Y` from the same label, put

    f(X,Y)=XY-(h+ell)(X+Y)/2+h ell.

Its four values are `ell/2,-1/4,-1/4,(1-ell)/2`, so `|f|<=1`. Under a null coordinate its mean is

    (p-h)(p-ell)=0,        p in {h,ell}.

Under a signal alternative's light coordinate, `p=ell+sigma delta` and `q=ell-sigma delta`, and its mean is exactly `-delta^2`, independently of the sign. Under a heavy coordinate or any masking row its mean remains zero.

Given the complete-row label counts `a_S,b_S`, pair the first `min(a_S,b_S)` rows at every label. Sum `f` over all paired rows and all `s` coordinates to obtain `Z`. Write `K` for the total paired-row count and `K_signal` for those from signal labels. Conditional on the counts and a fixed latent draw, all summands are independent. Consequently

    Var(Z | counts, latent)<=sK.

Every null has conditional mean zero. Every alternative in `F` has

    E[Z | counts, latent]<=-alpha^2 K_signal/(3s).    (1)

Neither the mass type nor `K_signal` needs to be observed by the tester.

## 3. Poisson complete-row supply and the signal collisions

Take `n=C B` ideal complete rows in expectation from each source, using independent Poisson totals, where the fixed constant `C=10^7` is sufficient below. Each label has independent source counts of mean

    nu_S=n w_S/W.

For an alternative in `F`, a signal label's mean lies between `Cmu/3` and `Cmu`. Since `k>=5`, `mu->0`, so eventually `Cmu<=1`. Its probability of having at least one row from each source is therefore

    (1-exp(-nu_S))^2 >= (Cmu/6)^2.

There are at least `D/2` signal labels. Their two-count occupancy events are independent conditional on the fixed latent draw. A multiplicative Chernoff bound gives

    Pr(K_signal < D C^2 mu^2/144 | latent)
       <= exp(-D C^2 mu^2/576).                     (2)

This uses only the first paired row at each occupied signal label; additional pairs can only increase its mean signal. It retains the common counts for all data coordinates.

Each source total is `Poisson(n)`, independently of the latent parameters, because the label law is the actual normalized law. Except with probability at most `2exp(-n/3)`, both totals are at most `ceil(2n)`. On this event,

    K<=ceil(2n)<=3n                                  (3)

for `n>=1`. This supply has mean `n`, unlike the lower-bound experiment's parameter-dependent mean `W`; no equality of these two experiments is assumed.

## 4. A fixed threshold with a uniform error bound

Set the known threshold

    tau=alpha^2 D C^2 mu^2/(864s).

Reject equality if `Z < -tau`. Abort with an arbitrary fixed answer when either Poisson total exceeds `ceil(2n)`. On the good count event, every null has mean zero and variance at most `3n s`. On an alternative satisfying (2), (1) gives mean at most `-2tau`, with the same variance bound. Chebyshev's inequality therefore bounds either conditional error by

    3n s/tau^2
      = 3*864^2 s^3/(alpha^4 C^3 Dmu^3)
      = 3*864^2*1600^3/C^3
      < 10^(-5),                                   (4)

where `Dalpha^4mu^3/s^3=1/1600^3` holds exactly. The fixed constant `C` is deliberately loose; no practical sample-count claim is intended.

The upper-tail error in(3) vanishes because `B->infinity`. The collision error in(2) vanishes because

    Dmu^2=Theta_{k,epsilon}(s^((k+5)/3))->infinity.

Thus the ideal-row tester succeeds pointwise on every declared null and alternative with probability greater than `0.99` for all sufficiently large `s`. The analysis does not need to identify masking labels, estimate `W`, learn individual coordinate probabilities or condition the latent null prior.

## 5. Actual Gibbs states and a fixed total budget

For29's encoded Gibbs family, measure each copy in the computational basis and retain only the known ideal event: every reservoir spin plus, each clone block constant, and label weight exactly `r`. Conditional on that event, the row law is **exactly** the normalized row law of29. Its probability is at least `1-eta`, where `eta=1/(100B)<=1/100`. This is an actual recognizable event in the specified encoding. General unknown Gibbs states need not have such an event.

For each source take `ceil(8n)` physical copies, retain their good rows in order, and request the first `ceil(2n)` retained rows. If fewer are available, abort. The retained count has mean at least `0.99ceil(8n)`. For `n>=1`, the requested count is below half that mean; a binomial lower-tail bound makes either source's shortage probability at most `exp(-n/2)`. The retained row values, conditional on the latent draw, are IID from its ideal law and independent of the retention indicators. Therefore this step does not introduce a latent-parameter oracle or an unaccounted approximation error.

Generate the two independent Poisson(n) totals internally. If either exceeds `ceil(2n)`, abort; otherwise use that many of the retained rows. This implements the preceding ideal experiment up to the explicitly bounded supply/total abort events. The physical copy cap is

    2ceil(8n)<=16C B+2=O(B),

counting both sources. No expected-budget claim is substituted for this fixed cap. Zero-Hamiltonian spectators added in29 may simply be ignored. The construction thus supplies a genuine pointwise family ceiling with all physical spins counted.

## 6. Consequence for the remaining P1 task

Together with the reviewed lower bound29, this proves the statistical order `Theta(B)` for the particular declared masked conditional-product family, at fixed parameters and up to absolute multiplicative constants. With29's prescribed size choice and padding, its polynomial/logarithmic order is the one displayed in29. The very large explicit constant used here is irrelevant to that asymptotic statement and has no claimed experimental meaning.

A stronger lower bound must change more than the constants in the same family. The shared count variance from the masking rows is already handled by an observable test at order `B`. A genuinely different multiscale family would need a fresh indistinguishability proof for its full count/data mixture, a pointwise far promise, and an actual normalized coefficient-bounded Hamiltonian with every auxiliary spin counted. This addendum neither rules out such families nor supplies one. It does not turn the specialized paired statistic into a test for arbitrary noncommuting Gibbs states.

Sources:

- Reviewed component29: https://github.com/Sodelin/Research-Commons/blob/603e52474aa12a2b7f0131a02e6508249d9dc616/research/2026-10-16-g6-gibbs-certification/random-label-masses-29/README.md
- The paired-bit statistic and earlier family ceilings appear in component27, Section7: https://github.com/Sodelin/Research-Commons/blob/0daba51d070c50bc10153a9272eab0e436484841/research/2026-10-16-g6-gibbs-certification/averaged-shared-counts-27/P1-AVERAGED-COUNTS-CANDIDATE-27.md

No historical novelty, full-class upper bound, Lean verification, or external peer review is asserted.
