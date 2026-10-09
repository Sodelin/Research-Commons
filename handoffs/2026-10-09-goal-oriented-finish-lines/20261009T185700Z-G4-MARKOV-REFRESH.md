# G4 mathematical refresh: Markov embedding and positive factorization

2026-10-09 18:57 UTC, dot. Nolan explicitly selected this mathematical investigation for the existing G4 lane. The other lanes remain G5/G6/G7 formalization; practical solver integration remains separate. No extra research worker is created.

## Objective

Investigate exact finite factorization by the actual admitted source operations, and whether a source-faithful realization or all-rival obstruction can resolve the original G4 quantifiers. A fixed-cap matrix factorization, approximate limit, larger observation menu, or unrestricted stochastic operation is not sufficient. Preserve all accepted G4 results and prior failed routes.

## Primary starting point and transfer tests

Baake and Sumner, *Embedding of Markov matrices for d <= 4*, arXiv:2311.02596v2, Section 6, especially Theorem 6.17 citing Johansen: https://arxiv.org/html/2311.02596v2#S6 . The general statement gives approximation by finite Poisson-factor products, and exact finite products for interior generalized-embeddable matrices. It does not automatically resolve non-singular boundary points. Elementary Poisson factors also permit individual transitions which need not obey the exchangeable original-source merger/routing restrictions.

Required checks before transfer:

1. Every elementary factor has an exact implementation by admitted original-source operations, with the same shared parameter/register and observation contract.
2. No limiting zero/infinite duration, negative time, cancellation or hidden conditioning is introduced.
3. The realization cost and required source size have the correct dependence on observation depth. A bound for each fixed carrier dimension is not a uniform all-depth bound.
4. Equality is proved on the declared G4 output, and an obstruction applies to all admitted rivals rather than only a chosen architecture.

Positive realization theory provides a complementary warning: ordinary linear-system rank can underestimate positive realization dimension. The late-zero lower-bound mechanism in Nagy and Matolcsi's *A lower bound on the dimension of positive realizations* (27 November 2002 draft, https://real.mtak.hu/7969/1/lowerbound.pdf) requires an observable sequence with an exact zero and a positive tail. That sequence and its nonnegative realization are not yet supplied by our strict source model; this is a lead, not a transferred bound.

## Fourier comparison

The user supplied https://github.com/shea256/fourier-transform-below-nlogn . Its 9 October README proposes a conditional exact-complex-arithmetic transfer with delta=0.00067 and explicitly retains independent mathematical review and end-to-end formal verification as pending. Unrestricted coefficients and recursive network adapters differ from physical source operations. The related community integer-multiplication project is https://github.com/CrocSwap/integer-mult-bounds . Neither numerical certificate nor an arithmetic saving is treated as a G4 theorem.

The comparison is a source of construction and cost-accounting ideas. The selected mathematical refresh is restricted Markov factorization. No new master closure, novelty or practical speedup is claimed by this checkpoint.
