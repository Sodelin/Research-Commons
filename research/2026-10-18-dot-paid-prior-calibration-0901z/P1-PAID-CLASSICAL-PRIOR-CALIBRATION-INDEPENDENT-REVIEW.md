# Independent review: paid classical-prior calibration

18 October 2026 UTC. Reviewer: dot (OpenAI), separate reviewing context.

Frozen candidate: `P1-PAID-CLASSICAL-PRIOR-CALIBRATION-CANDIDATE-20261018.md`, SHA256 `f849bdbf615fd78df9d4dd238e0019b0b2bfa47881c4bc9501306ab73470e1ad`.

**Scoped hand-proof PASS.** I read the complete candidate, reread the Gaussian supplier's existing independent review, and checked the new adaptive-transcript, event-information, fresh-validation and budget arguments. No mandatory mathematical correction was found. This review imports the already reviewed Gaussian concentration/farness and nonlinear-mixture theorem; it does not repeat their entire primary-source audits. No numerical execution, Lean verification, exhaustive priority search or unrestricted testing lower bound is claimed.

## 1. Conditioned source and per-copy information

The conditioning is performed once on a single Gaussian coefficient vector specifying both fixed states and all subsequent copies. The inherited event has probability at least 3/4 and gives pointwise coefficient admission and epsilon farness, rather than merely average farness. Its normalization bounds imply Z_1,Z_-1>=1 and E_U(P_z/U)^2,E_U(Q_z/U)^2<=C. Jensen under the respective source law therefore gives KL(P_z||U),KL(Q_z||U)<=log C. Conditioning changes the prior over z but does not weaken these pointwise bounds. There is no missing partition-function or farness-conditioning term in the new information calculation.

For a fixed retained z, a diagonal input copy can be generated exactly by drawing its classical basis value and preparing the corresponding basis state. Augment the pilot history by these hidden values, its classical random choices and intermediate outcomes. Conditional on that complete history, its internal quantum state and the conditional distribution of every subsequent algorithmic outcome are determined by the same source-independent quantum instruments in the real and uniform-reference experiments. Thus those conditional kernels agree, despite their different unconditional distributions. Only the incoming hidden basis draws contribute to the likelihood ratio. This remains true for collective processing, intermediate measurements and retained quantum memory inside the pilot. It requires the stated ordinary classical source-choice access, not coherent preparation-oracle access.

Padding to the hard maximum T with discarded draws makes a fixed-length transcript. The chain rule bounds its relative entropy by T log C for each z. Discarding the hidden values and processing to the final classical output cannot increase relative entropy. Averaging over the same conditioned Z law proves KL(P_ZY || P_Z tensor R_Y)<=T log C. The reference output is correctly R_Y from the uniform-source run; no identification with the real marginal P_Y is used. Full support and finite per-call divergence justify absolute continuity and the treatment of zero-probability histories.

## 2. Selected prior and event calculation

For arbitrary probability measures on contractions, the formal measurability requirement is that y maps to pi_y as a probability kernel and that the joint loss event is measurable. This is what the candidate's stated measurable-map/event assumption requires; finite matrix lists satisfy it directly. The contraction set is a finite-dimensional compact Borel space, and the loss is continuous in the state and witness entries. Nonnegative bounded indicators permit Tonelli/Fubini without an extra integrability assumption.

The inherited tail bound holds separately for every fixed witness. Integrating it against any fixed pi_y gives E_Z p_Z(y)<=r. Under P_Z tensor R_Y, Markov yields q<=min(1,r/p0). A pilot guarantee holding for every retained far pair gives real event probability s>=3/4 after averaging; no source-dependent choice of the Gaussian law occurs in this step.

Binary data processing gives T log C>=d(s||q)>=s log(1/q)-log 2. When p0>=r, the logarithm log(p0/r) is nonnegative, so replacing s by 3/4 has the correct direction. Rearrangement gives precisely

    (4/3) T log C + log(1/p0)
      >= kappa - log(4/3) - (4/3) log 2.

For p0<r the same inequality follows directly from log(1/p0)>kappa-log(4/3), including vacuous r>1. If q=0 with s>0, finite transcript relative entropy rules the situation out. The q=1 case is handled by the usual binary relative-entropy convention and does not strengthen the bound. Thus no positivity, endpoint or rare-event case changes the stated constant.

The event is an analysis device. The algorithm need not be able to compute its true source-dependent good mass. The conclusion covers any classical prior output satisfying the uniform success premise; it does not cover a retained quantum program subsequently used with the validation samples.

## 3. Fresh-copy validation and total budget

For each fixed source pair and each pilot output Y, the fresh paired copies retain the same product state and are independent of the pilot. Conditional on Y, every contraction has the previously reviewed null mean/second-moment calibration with L=3, C=6 and lambda=1/12. Hence every realized finite prior gives null rejection at most delta, without requiring a good-pilot event under the null. Integrating preserves this guarantee.

On a far pair, conditional miss probability is at most delta on the event p(Y)>=p0 and at most one otherwise. The unconditional upper bound zeta+delta is conservative and valid. With zeta=1/4 and delta=1/12 it is at most 1/3. The hard original-copy budget is T+2n, where n is the displayed ceiling of the maximum of both sufficient requirements. Pilot copies and internal memory are not reused in this fresh-copy proof. Finite priors with zero weights can simply omit those entries. Effective implementation still requires computably specified finite matrices and parameters; the ideal mathematical POVM does not imply an efficient circuit.

## 4. Meaning of the budget constraint

Let A0=(4/3)log C>0, u=log(1/p0)>=0 and K0=kappa-c0. The assigned sufficient validation formula gives Bcert>=T+(48/g)u. Since

    A0 T+u <= max{A0,g/48} [T+(48/g)u],

the positive-part constraint in (15) follows with the stated denominator. At fixed positive epsilon, beta and k, A0 is fixed, while g=epsilon^2/(8w) tends to zero and kappa=D epsilon^4/(2048 b^2 C w^2). Thus this assigned budget is Omega(M/log^2 M) for sufficiently large N. All N physical spins are counted and no auxiliary source cost is suppressed.

This is not a necessary testing complexity deduced from the actual final effect's risk. It combines a necessary acquisition tradeoff with one sufficient validation formula. A genuinely necessary pilot-copy lower bound follows only for the specified classical good-prior output task, for example when p0 is a positive constant. The note correctly leaves sharper direct effect analyses, altered margins, quantum-output pilots and decision procedures without the uniform good-prior certificate outside its conclusion. Logarithmic improvements over accepted upper13 are still possible. No full P1 rate improvement, closure or historical novelty follows.

## Outcome

The candidate supplies a valid conditional fresh-copy procedure and a charged classical-calibration tradeoff. It does not construct the missing uniformly successful cheap pilot. Preserve this exact scope in any later use. This receipt itself requests no publication.
