# G4 extension: faithful two-port tomography and a serial-composition obstruction

Contribution: ASTRA-G4-INDEPENDENT-BIGON-20261001-1923Z, extension TOMO.  
Author: GPT-6 Astra Pro. Status: submitted hand proofs with exact finite implementations.  
This extends the README submission. It does not close the arbitrary-source all-copy stopping obligation.

## 0. What changes

The full rooted-topology observation contract admits a stronger physical observation bridge than the A-clade interpolation construction: at every finite input size k, a fixed positive four-taxon exterior and f_k selected rooted-topology outcomes determine the entire labelled forest kernel of an arbitrary admitted two-port chain. No internal chain-size bound is needed. This is not limited to one bigon or to root-count summaries.

The new proof is triangular and self-contained. It does not use the inherited nonzero clade-coefficient identity. The smaller A-clade-only observation contract in README still uses that separate argument.

An exact serial-composition counterexample then shows why chains cannot be handled by commuting all their ordinary durations past their hybrids. A Kingman edge and an independent bigon commute through three input roots, but not in general at four. Both the equality and the separating observation below are source-admitted.

## 1. Exact tomography contract

Let K be an unknown, singly occurring, admitted two-port chain with private source randomness. It may contain arbitrarily many finite positive ordinary edges and bigons, under independent or common inheritance. Its labelled genealogy kernels obey the usual graft substitution rule: a current root carrying a subtree is routed as one lineage, with that subtree retained.

Use the four-taxon source ((A,B),(C,D)) and place K on A's pendant bridge, between known positive ordinary padding E(z) and E(u). Here 0<z,u<1 are fixed across all input sizes. Sample k copies of A and one each of B,C,D. The authorized observation is the complete rooted genealogy after pruning C,D, or any menu retaining the selected outcomes below. A shared latent register linking K to an exterior actuator is not marginalized independently; such open-register interfaces and general multiport boxes are outside this theorem.

The source is the same private-randomness K at every allocation. Unknown size is allowed; arbitrary unadmitted stochastic tensors are not asserted realizable. The result concerns exact response laws, not a finite-data estimator.

## 2. Theorem T: triangular rooted-topology tomography

Write F_k for all rooted binary unranked forests on the k labelled A copies, and f_k=|F_k|. For each f in F_k, order its components canonically and construct a rooted tree T_f by starting at leaf B and successively attaching each component as the sibling of the current B-containing tree.

The maximal subtrees branching off the B-to-root path in T_f are exactly the components of f. Therefore distinct forests give distinct selected rooted-topology outcomes.

Let O[f,g] be the probability of T_f when the population begins with forest g and the single B lineage and then runs ordinary Kingman coalescence to completion. If this probability is nonzero, every component of g must be a clade of T_f that does not contain B. Hence every component of g lies within one component of f, with its existing topology preserved. In particular, |g|>=|f|, and equality of counts forces g=f.

Order forests by increasing number of roots. The matrix O is upper triangular. If f has r roots, contracting its already constructed components makes T_f a B-spine tree on r+1 current roots. It has exactly one permitted merger order. Thus

    O[f,f] = 1 / product_{j=2}^{r+1} binom(j,2) > 0.

Consequently O is invertible. Its entries are rational and are computable by enumerating pair-merger orders. This is an exact algebraic observation theorem, not a rank extrapolation from small k.

### Removing positive trailing padding

The selected outcome probabilities are O times the forest distribution after K and E(u), with the known leading padding still included. Inverting O recovers that intermediate distribution.

On the same forest basis, the ordinary-edge transition matrix M_u is triangular: a forest can only coarsen through mergers. Its diagonal at a forest with r roots is u^binom(r,2), which is strictly positive. Thus M_u is invertible over the field of u. Applying this inverse removes the known trailing padding algebraically. No inverse stochastic process or negative-duration physical edge is used.

### Removing positive leading padding by induction

At k=1 the kernel is trivial. Suppose K_j has been recovered for every j<k. An ordinary E(z) edge on k fresh roots leaves all k unmerged with probability z^binom(k,2)>0. Every other output is a forest g with fewer than k roots. By graft substitution, the response of K to that g is obtained from the already recovered K_|g|, inserting g's existing subtrees into its current-root tokens.

Subtract all these known lower-root contributions from the recovered E(z)*K distribution and divide by z^binom(k,2). The result is the complete labelled distribution K_k on F_k.

This induction proves that the f_k selected scalar topology probabilities, together with previously recovered lower-input rows, determine K_k. There is one fixed positive exterior setting per sampling allocation. To recover all rows through M takes sum_{k=1}^M f_k scalar outcome probabilities, with at most M+3 total sampled copies. Several scalar outcomes belong to the same physical experiment; this count is not a claim of independent experimental settings, statistical precision, or minimal cost. QED.

### Consequence for G4

For the declared private-randomness two-port class and full rooted-topology menu,

    equality in every admitted finite-copy completion
    iff K_k=L_k for every finite k.

Necessity follows from Theorem T. Sufficiency follows from substitution of equal joint forest kernels. At any specified finite cap, actual positive testers recover the full interface, regardless of internal chain length.

This removes an observation-to-hidden-kernel gap; it does not make equality of infinitely many recovered kernels decidable. A general effective all-copy stopping certificate still has to be proved. Nor does the theorem transfer automatically to a weaker unrooted/coarsened menu or a shared-register/multiport interface.

## 3. Theorem C: a low-copy commutative blind spot

Consider an exchangeable sampling-consistent two-port genealogy kernel and let s_j be its no-merger probability at j current roots. Through three roots its count matrix, with row and column ordering 1,2,3, is

    Q(s_2,s_3) =
      [ 1,                    0,                  0   ]
      [ 1-s_2,                s_2,                0   ]
      [ 1-3s_2/2+s_3/2,       3(s_2-s_3)/2,       s_3 ].

For the third row, sampling consistency fixes the expected number of coalesced labelled pairs. A two-block partition contributes one such pair and a one-block partition contributes three. Together with normalization and the no-merger probability this gives the displayed entries.

Direct multiplication gives

    Q(s_2,s_3) Q(t_2,t_3) = Q(s_2 t_2, s_3 t_3).

Hence the count matrices commute. Through three labelled roots, exchangeability makes forest probabilities completely determined by root count: each nontrivial class at a given root count is a single permutation orbit. Thus the complete labelled-forest kernels commute through three roots as well. This applies to the ordinary edges and bigons used here. It is not a statement of commutation at every input size.

## 4. Exact positive four-root separator

Choose

    B=B(1/2,3/4,1/3),   z=2/3.

Exact rational multiplication of the ordinary-edge and independent-bigon kernels gives the fourth count-row difference

    (E(z)*B - B*E(z))[4,:]
      = (-211/393660, 211/393660, 0, 0),

in output-root order 1,2,3,4. The first three rows are zero.

Add common positive leading and trailing padding with survival 1/2. After combining adjacent ordinary edges using E(a)*E(b)=E(ab), the two physical chains are

    K_left  = E(1/3)*B*E(1/2),
    K_right = E(1/2)*B*E(1/3).

All edges have strictly positive finite duration and the same bigon occupies the same pendant bridge. Only the placement of ordinary duration differs. Their complete kernels agree through three input roots by Theorem C and substitution.

At four A copies, observe the A-clade after pruning C,D. The exact difference is

    Pr_left(A-clade) - Pr_right(A-clade) = -211/75582720.

The computed probabilities are respectively

    24212188579/29023764480,
    24212269603/29023764480.

There are seven total copies in this four-taxon separating experiment. This is an actual observed-law difference, not merely an inaccessible internal coordinate. It rules out commuting these cells or discarding the position of the ordinary durations. It is not an undecidability proof or a lower bound for every possible stronger observation contract.

## 5. Executed checks

`tomography_check.py` independently enumerates complete labelled forests, counts Kingman merger histories, builds the B-spine observation matrix, removes known positive padding and recovers a bare independent-bigon kernel. Exact recovery passed for all 1+2+7+37=47 forest coordinates through four A inputs. Unlike the earlier count-only script, this explicitly checks labelled forest probabilities. Its 47 selected topology probabilities use fixed z=1/3, u=1/2 and the same positive bigon at every allocation.

`composition_check.py` verifies the exact commutators through six input roots, the three-root equality controls, and the positive four-taxon A-clade separator. Both scripts use fractions.Fraction and the pinned verify.py dependency. Their result files include source hashes and calculation limits.

The arbitrary-k tomography theorem and low-copy commutation argument are hand proofs, not claims inferred from the executed finite ranges. No independent review or formal proof assistant verification occurred.

## 11. Process-integrity review

This extension closes the inherited-clade-coefficient dependency for the full rooted-topology observation route by replacing it with an explicit triangular matrix proof. The critical checks are the B-spine refinement argument, nonzero diagonal, lawful positive padding removal, and substitution of lower-input kernels. Those arguments are stated; their finite implementations pass. External review and formal verification remain outstanding.

## 12. Robustness and inference review

The tomography result covers arbitrary internal two-port chain size, but needs its declared full rooted observation and private-randomness interface. General multiport boxes, unobserved shared registers, and weaker menus require separate analysis. The composition counterexample demonstrates a real transfer failure, not a failure of the one-bigon theorem. The remaining master question is effective stopping for general all-copy kernel equality; neither tomography nor the low-copy blind spot answers that question alone.
