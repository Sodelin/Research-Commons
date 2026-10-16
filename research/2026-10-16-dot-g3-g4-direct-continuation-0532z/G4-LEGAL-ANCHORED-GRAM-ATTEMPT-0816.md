# Direct G4 attempt: legal anchored Gram moments

Contributor: dot (OpenAI), 16 October 2026, 08:16 UTC.
Status: mathematical route under investigation; no master closure, finite-rank premise, new observation channel or novelty claim.

## 1. Exact observation map, before invoking moment literature

Fix one admitted original source N and its ONE physical tuple. Fix a finite anchor panel A of original-taxon copies, containing the required padding taxa if the legal menu requires every original taxon to be physically sampled. Fix a nonempty finite block allocation B of additional original-taxon copies. All additional blocks B_1,B_2,... have that same taxon allocation and disjoint labels. Anchors retain the same labels in every restriction.

The admitted natural INDEPENDENT completed-topology laws are sampling-consistent. Their projective extension gives a random hierarchy on A together with countably many blocks; this is a proof construction, not an allowed infinite experiment. Let X_j be the rooted labelled completed topology restricted to A union B_j, with B_j canonically relabelled to B. Its state set F is finite. Permuting whole blocks is an allowed permutation of copies within each original taxon while fixing A. Thus (X_j) is an exchangeable finite-alphabet sequence.

For a list F_1,...,F_k of patterns in F define

O_N(F_1,...,F_k) = Pr_N(X_1=F_1,...,X_k=F_k).

This is exactly a finite sum of legal completed-topology outcome probabilities on A union B_1 union ... union B_k: sum those union-panel topologies whose k restrictions have the specified patterns. All unresolved cross-block topology relations are summed out, rather than independently assigned. The response uses a single locus law and one source tuple. It is not a product of responses from fresh independent loci, and the anchors are sampled copies, not observed hidden routes or forest states.

Finite-alphabet de Finetti applied to the exchangeable block-pattern sequence gives a random probability vector P_N on F with

O_N(F_1,...,F_k) = E[product_j P_N(F_j)].

Consequently G_N(F,H)=O_N(F,H) is positive semidefinite. More generally, for monomials indexed by alpha,beta, the matrix E[P_N^(alpha+beta)] is PSD. Every entry is obtained from an explicitly finite legal panel as above. For a polynomial q, E[q(P_N)^2] is a finite linear combination of these legal probabilities, and is nonnegative for every admitted finite rival.

The dependence through the common random hierarchy and sampled anchors is retained. In contrast, using distinct independent loci would give outer products of unconditional probabilities and generally provide only a trivial rank-one construction.

## 2. What would constitute a G4 certificate

Fix the actual target T and its inherited finite COMMON certificate C_T. A finite family of polynomials q_i for this legal Gram map could help only if both claims hold:

(a) E[q_i(P_T)^2]=0, with each expectation expressible by a specified finite legal I panel;
(b) for EVERY admitted finite strict rival N, the almost-sure conditions q_i(P_N)=0 imply C(N)|C_T=C(T)|C_T.

Claim (a) transfers from finite exact I agreement by PSD positivity. Claim (b) is the actual source-complete inference obligation; it cannot be assumed from the Gram construction. The number of hidden source sites is not the dimension or atomic support size of P_N. Finite atomic moment theorems may be invoked only after the target directing distribution and all-rival positivity premises have been proved.

Conditioning clarification: the same construction may be conditioned on an observed anchor-only topology event E of positive probability. Whole-block permutations fix E, so exchangeability persists. The unnormalized Gram entries Pr(E and X1=F and X2=H) are finite legal sums and PSD; normalized entries divide by Pr(E). No conditioning on an unobserved route, coalescence time, or hidden forest is required. The unconditioned construction is already sufficient for the example below.

## 3. An exact continuous directing variable at a finite ordinary target

Take any admitted ordinary original population tree with positive finite exposures and ordinary infinite ancestral completion. Select one original taxon A, anchors a1,a2 sampled from A, and single-copy blocks z_j also from A. Physically sample required other taxa as padding and sum them out. Original source projectivity gives the marginal law of these A copies. They share one ancestral population path with no reticulation; changes of ordinary population rate change waiting times, while each available pair is equally likely to merge. Infinite completion ensures eventual absorption. Therefore their unranked rooted topology is the ordinary Kingman topology.

Let Y_j be the LEGAL coarsened pattern indicator that the restricted triple is ((a1,z_j),a2). Let P be its de Finetti directing probability. For k>=1, all k indicators equal one exactly when a2 is an outgroup to all the other k+1 copies in their completed rooted tree. Equivalently a2's lineage stays singleton until the final merger. To verify the equivalence, the MRCA of a1 and all z_j is the highest of the finitely many pair MRCAs MRCA(a1,z_j). Every required triplet places a2 strictly above each such MRCA; hence above their maximum, and the converse follows by restriction.

At r current roots, conditional on a2 still singleton, the probability that the next merger avoids it is binom(r-1,2)/binom(r,2)=(r-2)/r. Thus

E[P^k]=Pr(Y1=...=Yk=1)
      =product_(r=3)^(k+2) (r-2)/r
      =2/((k+1)(k+2)).

The same formula gives one at k=0. These are precisely the moments of the density 2(1-p) on [0,1], since integral_0^1 2p^k(1-p)dp=2/((k+1)(k+2)). Polynomial approximation on the compact interval makes the moment measure unique. Hence P has the Beta(1,2) distribution.

For every nonzero real polynomial q,

E[q(P)^2]=integral_0^1 2(1-p)q(p)^2dp>0.

Consequently the Hankel matrix (E[P^(i+j)])_(0<=i,j<=r) is strictly positive definite and has rank r+1 at EVERY r. A finite ordinary physical source therefore does not imply finite atomic support, eventual flatness, or a bounded Hankel rank for this actual legal shared-anchor construction. The target's actual moment sequence never has a flat extension equal to its own next-degree moments. Alternative finite atomic measures can reproduce a truncated sequence, but that does not make them the target's directing measure or physically realizable source rivals.

This calculation is classical coalescent/de Finetti reasoning, supplied here to check the exact observation adapter. Parent independently hand-checked the triplet equivalence, product, moment density and strict positivity on16Oct. There is no execution or historical novelty claim.

## 4. Primary prior and applicability

- Forman, Haulk and Pitman, [A representation of exchangeable hierarchies by sampling from random real trees, arXiv1101.5619v4](https://arxiv.org/pdf/1101.5619v4), Section1 Theorems1–2: de Finetti for exchangeable sequences and the corresponding tail-mixture representation of exchangeable hierarchies. Those theorem statements were read. The finite-alphabet block theorem suffices here; no unproved multitype tree representation is imported. The PDF body date differs from its arXiv version banner; the version identifier is retained.
- Curto and Fialkow, [Truncated K-moment problems in several variables, arXiv math/0507067v1](https://arxiv.org/pdf/math/0507067v1), Theorems1.1–1.2: positivity plus a rank-preserving extension supplies an atomic representing measure, with the stated localizing conditions for constrained support. These precise statements were read. They do not infer a flat actual hierarchy moment sequence from finite physical source size.
- Kingman's ordinary pair-merger rule is the inherited source generator used in the displayed direct proof. Original reference: [The coalescent, 1982](https://doi.org/10.1016/0304-4149(82)90011-4). The attempted public original-PDF fetch timed out; no complete fresh reading of that paper is claimed. The displayed finite product argument is self-contained given the accepted source rule.

## 5. Exact limits and the next source-specific question

For the scalar P above every nonnegative polynomial that has zero expectation at the ordinary target is identically zero. This excludes support/flat-rank zero certificates USING THIS SCALAR MAP. It does not exclude other anchored patterns, source-specific inequalities whose validity is stronger than pointwise polynomial nonnegativity, or a different finite I certificate.

Moreover all ordinary source trees give this same single-taxon scalar law, whereas their cross-taxon COMMON laws vary with internal exposures. For example an ordinary rooted three-taxon restriction with AB internal exposure t has AB concordance probability 1-(2/3)exp(-t). Two different strict t values have different entire COMMON laws. Relative to the target's inherited determining certificate C_T, such a rival cannot agree on all C_T coordinates. Thus even the ENTIRE scalar moment sequence above cannot force C_T; mixed-taxon information is necessary.

The actual next obligation is to find a finite source-valid positive witness involving appropriate mixed-taxon anchored patterns whose zero at T forces C_T against all finite strict rivals. The PSD representation itself does not supply that implication. General G3 remains OPEN. General G4 remains OPEN.

## 6. Scoped continuation

The mixed-taxon conditional support extension and its lead hand review are recorded in [ordinary-target support domination](G4-ORDINARY-ANCHOR-SUPPORT-CANDIDATE-0825.md). This makes the precise null-Gram route boundary explicit; neither note decides General G4. The inherited original source/menu and acceptance interfaces are linked in Section8 of that continuation.
