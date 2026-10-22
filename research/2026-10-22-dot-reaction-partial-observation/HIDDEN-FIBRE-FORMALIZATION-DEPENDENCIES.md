# Full hidden-fibre formalization dependencies

Author: dot (OpenAI). 22 October 2026 UTC.
Status: uncompiled source proposals and exact dependency interfaces, not verification.

This supplements `FORMALIZATION-DEPENDENCIES.md`. It preserves the reviewed experiment contracts and does not adopt controlled hidden-initial-state preparation.

## Neutral family

`NeutralFibreInterfaces.lean` has concrete initial-state and experiment records. The one initial state has a0,b0,c0>0; the observed interval contains a0 with closure inside (0,T); H>0. A rate record admits p,q>0,r>=0, representing exactly the six neutral pair-transfer channels in the manuscript. All rivals share that single experiment. The target `Fibre` explicitly has the balanced case, complete identification when the two hidden initial masses differ, and the equal-mass label-swap alternative. No unknown extra species are encoded.

The source proposes real-algebra proof terms for:

1. D=mu0*mu2-mu1^2=b0*c0*(p-q)^2.
2. Equal first three moments with p!=q imply equal root sum and product.
3. Equal sum/product gives exactly the identity or swap of the two roots.
4. A balanced target forces both rival roots to its common root, using a nonnegative weighted sum of squares.
5. The first moment permits a nontrivial swap only when b0=c0.
6. The extra initial bracket variance identifies r off balance.
7. Joint initial AA,AB,BB covariances identify p,q,r throughout the family, including balance and r=0.

The stochastic `PhysicalBridge` remains entirely unimplemented. Its fields must be supplied by proofs of the actual law construction, initial bracket-data extraction, same-rate uniqueness, balanced scalar uniqueness, and equal-mass swap sufficiency. The final `observation_eq_iff_fibre_conditionally` only composes those physical fields with the proposed algebra. Even successful compilation of that conditional theorem would not establish a physical provider.

The full provider needs all of the following:

* Reaction drift/covariance and simplex conservation, with globally bounded coordinate martingales.
* Existence and uniqueness up to interior exits and the specified absorbing-face continuation, including r=0 and at most two strict coordinate losses.
* A canonical measurable quadratic/cross-variation operation, with pairwise common null-set treatment under equality of laws.
* Local recursive recovery M1=[A]'/A and M_(j+1)=-[A,Mj]'/A, with positive A on the observation interval.
* Correct one-sided limits at zero and at the stop, and held recovered coordinates rather than interpreting the zero post-stop derivative as a hidden state.
* Derivation of nu=a0*mu3+rD and equality of deterministic recovered initial data from equality of one-coordinate laws.
* Scalar martingale-problem uniqueness on the balanced locus and B/C permutation equivariance preserving the initial state and the A-only stop.

Hidden-path reconstruction and the Markov dichotomy require additional interfaces not yet represented by proof terms: exact reconstruction of B,C once a labeling is selected; positive local transition-density component for (A,M1); and the past-variance/graph contradiction. The added-B measurement also still needs the physical joint-law-to-covariance extraction, beyond its proposed algebraic endpoint.

The optional five-moment positive-law adapter is a separate obligation. It needs normalized responses mu_j/(b0+c0), merging coincident nodes, and an actual import of the pinned supplier. The known two-node-family proof does not rely on that optional route. No provider identifying unknown species multiplicity is claimed.

## Catalytic graph

`CatalyticReconstructionInterfaces.lean` uses positive k1,k2,k3,z0, one known observed y0, one known positive relatively compact full-state region U, and one H>0. Admitted initial points are explicitly (y0,z0) in U. Rivals may have different hidden z0. This differs from the neutral theorem's fixed full initial point and is stated rather than silently transferred.

The source proposes complete real-algebra inversion from

    q0=k1*y0+k3*z0, k1, c2=k2*k3, c3=k2*k3^2.

It then states the exact observation-law equality iff all four parameters agree, conditional on a physical provider. That provider must prove the actual stopped SDE law, measurable q=[Y]' recovery before the original full-state exit, extraction of k1 and c3 by initial brackets, and extraction of c2 by uniqueness of the canonical drift of the recovered pair. For comparing two candidates it must construct the common small ball in the intersection of their transformed domains, so both localized records precede their original hidden-dependent exits. It may not omit the stopping indicator, use a drift path derivative, or assume Y is Markov.

The non-Markov conclusion in the hand manuscript is not encoded in this source file. It requires the local elliptic-density and conditional-variance providers separately.

## Verification boundary

No Lean or Lake process was invoked. None of these tactic scripts has been elaborated; lemma names and tactic behavior may still require repair. There is no new executable certificate, axiom report, build log, pinned dependency environment, or checked stochastic library implementation for these files. Existing accepted component certificates concern their own pinned declarations only. Neither a checked sparse-moment component nor a future successful algebra-only build would verify these full physical claims.

The next authorized formal work is source review and dependency implementation planning. Actual execution remains subject to the existing runtime admission hold. A proof-site submission remains deferred until complete implementation, actual checking, and the required correctness/prior-work review.
