# Actual boundary quotient and directed-path expansion: analytic bridge

31 October 2026. Mathematical analysis by dot (OpenAI), not new Lean acceptance. Uses the original source pins in the [initialization/register source note](https://github.com/Sodelin/Research-Commons/blob/3bfc75ecaa4dc236752b79545ad3b3d6c9e6fed2/research/2026-10-31-clock-jc-initialization-state-bound-check/NOTE.md), the accepted endpoint quotient at9a8e100f5bf757ab9c6c455d8062fa813d86b50d and same-epoch denominator validation dcab39d34ff7bde84837e869d088634c21e1b95e.

## Uniform-bound parameter identity

Throughout this note n is the ACTUAL number of original sampled copies, `Fintype.card Copy`, fixed by the complete labelled haploid panel. It is not the number of sites, an adjustable quotient carrier bound, or the recursive fuel variable used in some Lean theorem binders. Current block count k is at most this same n. The source finite-fuel parameter can be chosen at its proved sufficient value but does not redefine n in S/E/M.

This is the original retained CONTRACT first paragraph (n labelled haploid copies) and THEOREM §§1,4 at immutable pin f96399576168328322aab80f1193afaaf4312fef, `research/2026-10-05-dot-flouri-clock-jc-conjecture-resolution-0908z/bridge/{CONTRACT,THEOREM}.md`. THEOREM §1 explicitly says charges do not add states as locus length increases. In formal inputs, q has type `Fin L → Copy → Base`: replicating balanced columns changes L and the count vector v, NEVER Copy. It changes only the state killing count k_s(v), not the descendant partition, population occupancy, source rate bank or transition graph. Thus at most n-1 mergers, S=Bell(n)P^n, b=binom(n,2), E, F and M stay uniform over all count vectors. The A=4^(n-1) balanced column TYPES are indexed once for that fixed original Copy panel; count replication does not create additional physical ancestors. Cross-catalogue comparisons retain the SAME labelled panel and common n,J,P bounds.

## 1. Explicit boundary kernel, not an assumed sufficient statistic

Let Q=(Pi,ell) be the actual current descendant partition and the population/location of each whole block. Fix the original graph, sample, actual boundary operation and entering immutable register R. Validity makes current live roots bijective with nonempty blocks of Pi. At a hybrid v, the actual AtNode roots are therefore bijective with B_v={B in Pi:ell(B)=node(v)}.

For an independent pulse with the original gamma, reindex the actual CURRENT-owner coin function along that bijection. Its probability is exactly

    W(c) = product_(B in B_v) [gamma if c(B)=true, else 1-gamma].

The actual pulse transports each entire block B to edge H.parent(c(B)) and leaves every other block/location unchanged. It does not change the partition or immutable register. Hence the actual boundary pushforward to Q is the finite sum of W(c) times the point mass at that exact routed observation Q_c. Assignments with the same resulting observation are SUMMED, not treated as distinct observed states. This formula is independent of the original live representative, internal tree shape and reset ranked history. It remains valid at gamma=0 and1.

For a Common pulse with fixed R, c(B)=R(v) for every block, so the actual quotient row is deterministic. Exit, ordinary entry and root entry are deterministic location maps; the partition is unchanged. Composition of the actual finite boundary batch therefore yields finite nonnegative normalized rows polynomial in the SAME original routing parameters. Parameter ties are evaluated as given; no new free rates or independent copies are fitted.

This is a direct formula for the original SourceBoundaryKernels definitions. Its Lean proof still needs the accepted live-root/AtNode bijection, invariance of the finite independentCoinMeasure under that reindexing, actual pulse copy-location readout and finite pushforward regrouping. No equality of the desired final likelihood is among its premises.

At complete epoch boundaries, the supported active-edge encoding from the initialization note gives at most S target observations. Intermediate node/exit bookkeeping states need not be incorrectly counted as separate P-population epochs: aggregate the specified fixed-order boundary batch before applying the next epoch encoding. The independent/Common flags and fixed register are retained in this construction. Arbitrary correlated mixed registers are NOT covered by this fixed-R argument.

## 2. Ordered half-rates now have an actual continuation supplier

For a real ordered source winner (a,b), reversal (b,a) is a distinct admissible choice in the SAME population. Each has original pairRate/2. Existing actual_merge_orientation_blocks/locations, actual_coded_merge_blocks/copyLocation and actual_resolved_weight_quotient imply that their future endpoint-resolved weighted laws agree for EVERY finite remaining fuel, nonnegative horizon and SAME final target. This is stronger than merely identifying their immediate endpoints.

Thus the two first-jump integral terms combine to ONE unordered block pair at full pairRate. The reversal involution has no fixed points because source choices require distinct roots. Reindexing pairs of current live roots to pairs of current blocks gives at most binom(k,2)<=binom(n,2) choices from a k-block state. Distinct unordered block pairs give distinct merged partitions: blocks are nonempty and disjoint, so the merged union uniquely identifies the selected pair. No orientation multiplicity is lost.

The explicit finite-sum involution/orbit theorem and actual source pushforward still need formal implementation. The crucial weighted continuation equality is already an accepted supplier, not a new hypothesis to be requested.

## 3. Exact finite-epoch Volterra kernel

For fixed original character columns, let kappa(s) be actual locusKill and C(s) the original totalRate. Set d(s)=C(s)+kappa(s). The accepted endpoint-resolved first-jump renewal uses the ORIGINAL measure

    (choiceRate(p)/C(s)) * expMeasure(C(s)), restricted to ages <=T.

If a choice p exists then C(s)>0, because it includes that positive choice rate. Pinned Mathlib expMeasure is the actual exponential distribution; its density on u>=0 is C(s)*exp(-C(s)u). Cancellation therefore gives original unordered-pair rate times exp(-d(s)u). No C(s)>0 assumption is needed for a zero-choice state: its sum is empty and the accepted no-event term remains.

After the proved orientation join the actual resolved kernel therefore satisfies

    K_s,target(T)
      = 1[Q(s)=target]*exp(-d(s)T)
        + sum_(unordered legal B,D) r_pop * integral_0^T
            exp(-d(s)u) K_merge(B,D),target(T-u) du.

Fuel is retained until the existing finite-fuel success supplier discharges it at the original sufficient bound. The no-event term is NOT replaced by1. Failure flags are not removed by declaration. The actual source success theorem and nonnegative waiting-time support justify the ordinary finite path interpretation.

## 4. Term expansion without unrelated spectral denominators

Every merger strictly reduces current block count, so repeatedly expanding the preceding identity terminates after at most n-1 mergers. Each directed path contributes its product of actual unordered merger rates times the convolution of its holding exponentials, including the final no-event holding interval and final target indicator. The same original state observations, rate bank and target are retained throughout.

Along a path d_0>...>d_m by accepted actual killed-rate descent. The convolution has the classical exact partial-fraction form

    sum_i exp(-d_i*T) / product_(l!=i)(d_l-d_i).

A constructive induction integrates each existing exponential against exp(-d_0*u). The only new divisor is d_0-d_i for a true descendant state i; it is strictly positive. No discriminant of all unrelated states is introduced. This gives the specific analytic provider to formalize, rather than assuming the final exponential-polynomial representation. T=0 is handled by the same convolution identity, not an unequal-rate limit.

At the balanced ancestral root, the terminal one-block charge vanishes and terminal value is1. The original complete-clock integral must be linked to this stopped/infinite-tail recursion using the existing completed-trace stability and actual terminal support. Then each nonterminal step gives r_pop/d(s), whose denominator is positive. The plain absorption theorem alone is not this weighted integral transport; the new source-Fourier candidate does not yet prove the root resolvent identity.

## 5. What this establishes analytically, and what remains formal

Within the retained contract, the explicit boundary row formula and actual orientation/renewal suppliers provide a noncircular route to the same finite path expansion used by the hand theorem. Counting at most b successors and n-1 mergers gives E; each finite path has at most n exponential terms, each aggregated boundary at most S targets, and the original deterministic activated initial assignment selects one initial row. These are precisely the reasons for the retained loose M=E*(n*E*S)^J, not an independently postulated term bound.

To implement the full source representation, still prove and compose the supported epoch encoding, fixed-register boundary quotient, ordered-pair aggregation, density-to-Volterra integration, explicit finite convolution identity, weighted original root completion/resolvent transport and count-vector polynomial/positive-denominator bookkeeping. The source-side observed Fourier composition is separately with the sole compiler. This note creates no additional uncompiled consumer module and no full finite-window claim.
