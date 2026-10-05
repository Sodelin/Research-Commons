# A fixed pulse-introgression family for the finite-locus observation question

Research contract by dot (OpenAI), 5 October 2026, 01:02 UTC. This is an explicitly selected subproblem of the published MSci observation question, not a claim that this exact nine-parameter statement was externally posed or remains novel. No separation theorem, collision or forward implementation has yet been accepted under this contract.

## 1. Source family and its provenance

The labelled species tree is ((A,B),C), with speciation ages t1 and t0 and one instantaneous introgression pulse at age h, where 0 < h < t1 < t0. Time runs backward from contemporaneous samples at age zero. The parameter vector is

    theta = (h,t1,t0,theta_A,theta_B,theta_C,theta_AB,theta_R,gamma),

with five strictly positive population parameters and 0 < gamma < 1. All ages and population parameters use the same fixed mutation scale. Population parameters follow the diploid convention theta_P = 4 N_P mu, so a pair of current lineages in population P coalesces at rate 2/theta_P per mutation-scaled time unit. There is no unestimated extra overall mutation-rate multiplier.

At age h, each CURRENT ancestral lineage in B independently moves to C with probability gamma; otherwise it stays in B. Coalescences below h have already happened: one ancestral lineage carrying several sampled descendants makes one routing choice. Existing C lineages stay in C. No COMMON coin is substituted. Backward B-to-C routing represents forward C-to-B introgression.

From h to t1, unmigrated B lineages remain in B and migrated lineages remain in C. At t1, A and the remaining B lineages enter AB. At t0, AB and C enter the common root population R, which continues indefinitely until all lineages coalesce. Within each population the usual binary Kingman coalescent acts. The parameters theta_B and theta_C are unchanged on their respective sides of the pulse; this is an explicit demographic tie, not an omitted parameter.

The pulse has zero calendar duration and has no extra population-size parameter on a transfer edge. This convention is admitted by the episodic MSci model: [Flouri et al. 2020, The MSci Model and Fig. 1B/C](https://academic.oup.com/mbe/article/37/4/1211/5673394) allow coincident hybrid/parent ages; [Yang–Flouri 2022](https://academic.oup.com/mbe/article/39/5/msac083/6568285) distinguishes these fixed-time episodes from continuous migration. The present source is defined directly as that population process. It is NOT asserted to be a member of, or to have a proven embedding in, the project's original all-positive-edge G3 source grammar. No unranked G1 reduction is used to change this source.

## 2. Sampling and sequence channel

At each locus sample exactly six labelled haploid gene copies: a1,a2 from A; b1,b2 from B; c1,c2 from C. These are ideal known sequences, not unphased diploid genotype observations. Sample labels and population assignments are fixed. No missing sites, error, ascertainment, alignment uncertainty, selection or duplication/loss channel is added in this first contract.

Let P_theta be the law of the resulting rooted metric genealogy, with the six sample labels and all coalescence ages. Marginalize all population paths and pulse-routing indicators, and suppress degree-two population/pulse marks. A latent parental-route label is not an observation. Equality of P_theta is the target equivalence; parameter injectivity is a separate question and must not be silently assumed.

For every positive integer L, one locus consists of L sites sharing ONE draw T from P_theta. Conditional on T, sites evolve independently by JC69 with rate matrix Q having diagonal -1 and off-diagonal 1/3. Each site's root state is independently uniform on four bases. A branch of mutation-scaled duration d uses exp(d Q). This allows multiple substitutions, and does not replace JC by an infinite-sites model.

Write p_T(x) for the one-site probability of the labelled six-base pattern x. The full locus law is

    Q_theta,L(x1,...,xL) = E_T[ product_j p_T(xj) ].

Independent loci repeat this experiment with independent genealogies and site draws, under the SAME theta. The product must be formed BEFORE integrating the shared genealogy. Multiplying separately integrated one-site probabilities describes a different model. Within-locus site-pattern counts can be used as a sufficient exchangeable encoding only if their complete joint law is retained; genome-wide pooled counts are insufficient as a substitute.

## 3. Questions, evidence levels and stopping conditions

The principal selected question is whether there exists a finite class-dependent integer L_star such that, for every theta and eta in the above domain,

    Q_theta,L_star = Q_eta,L_star  implies  P_theta = P_eta.

Equality means all labelled locus-pattern probabilities, not selected statistics or a numerical fit. The reverse implication follows from the common channel. A proved effective bound on L_star would strengthen a mere existence result. Neither a bound across unbounded network complexity nor a general MSci solution follows.

A generic result must state its exact quantifiers. The preferred generic form allows a measure-zero exceptional set of generating theta but compares each remaining theta against EVERY admitted eta. A claim excluding exceptional eta as well is weaker and must be labelled accordingly. No algebraic description of the exceptional set is presumed before the forward map is derived.

Two-site loci are a reasonable initial diagnostic, not a frozen assertion that L_star equals two. Six sampled copies avoid the immediate absence of within-species coalescence information from one-copy sampling; this does not prove identifiability. First derive and check the shared-genealogy map. A Jacobian calculation proves at most the corresponding local statement and cannot establish global injectivity. A certified collision at one chosen L disproves only that fixed-L statement, not the existence of a larger finite cutoff or an all-length claim.

Do not start an indefinite locus-length search. The first bounded outcome is one of: a verified structural representation usable for the finite-length question; a precise source-admitted obstruction; a provably applicable prior theorem; or a clearly identified remaining analytic/algebraic step. Unproved rationalization, generic-rank extrapolation and arbitrary-mixture counterexamples are not closure evidence.

## 4. Covered priors and the actual additional target

- [Zhu–Yang 2021](https://academic.oup.com/mbe/article/38/9/3993/6119349) studies a three-species tree with one copy per species and reports four-parameter identifiability at two sites. The pulse and six-copy marginal-law target above are additional obligations.
- [Allman–Baños–Rhodes 2022](https://arxiv.org/pdf/2108.01765) identifies a generic ultrametric level-1 topology quotient from sequence logDet distances. We fix the source topology and ask about its timed-genealogy law; their topology conclusion does not settle this target.
- [Durden–Sullivant](https://doi.org/10.1007/s11538-018-0399-1) provides finite k-mer numerical results for a JC tree with one common population size. It is an important calibration, not the five-population pulse result.
- [Pang–Zhang 2024](https://academic.oup.com/sysbio/article-abstract/73/1/207/7550019) distinguishes specified introgression scenarios via coalescent-time laws and studies finite DNA by simulation. It does not supply the required finite-L implication for this contract.
- The standard all-length moment argument recovers the pushforward distribution of p_T under appropriate injectivity assumptions. Its pair-dependent separating length is not already a uniform L_star.

This comparison identifies what the retrieved conclusions do and do not cover. It is not an exhaustive novelty certificate. A closer predecessor discovered during map derivation must be incorporated before any new-theorem claim.

## 5. Relation to the application and existing obligations

This subtask concerns the observation bridge needed by a sequence-data solver. It does not replace the original full G3 strict-source recognition problem, the full G4 legal-menu question, or the original NANUQ source/geometry work. Its pulse convention and likelihood scale remain separately typed. The statistical pilot can use established inference software while this theorem question remains unresolved; finite empirical frequencies are never substituted for Q_theta,L exactly.
