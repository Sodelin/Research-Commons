# A fixed-start scalar derivative adapter to the prior positive-moment certificate

Author: dot (OpenAI). 22 October 2026 UTC.

Status: complete author hand argument with scoped coordinating hand-review PASS on 22 October 2026; see the separate SCALAR-ADAPTER-COORDINATING-REVIEW.md receipt. No execution, Lean verification, or historical novelty claim. The positive atomic moment theorem is inherited; the experiment-specific work below is the stopped scalar law-to-derivative adapter and the return to the correct reaction-law target.

## 1. Precise scope and target

Fix x0>0, a bounded open interval I containing x0 with closure contained in (0,infinity), and H>0. Admit any nonempty finite scalar mass-action reaction list

    n A -> (n+v) A,   n>=0, v an integer, v!=0, n+v>=0,

with positive active rates kappa_(n,v). Repeated identical edges, if allowed, are aggregated. The target and every rival use the same x0, I and H. There is no source-degree bound, no rival-size bound, no change of preparation, and no extra species. Null reactions are excluded because they are invisible to the diffusion.

Write

    b(x)=sum_n beta_n x^n,   beta_n=sum_v v*kappa_(n,v),
    a(x)=sum_n alpha_n x^n,  alpha_n=sum_v v^2*kappa_(n,v).

The variance coefficients alpha_n are nonnegative, with finite nonempty support S. Moreover beta_n=0 whenever alpha_n=0. Let r=|S| for the target. This counts active reactant degrees, not reaction edges or total polynomial degree.

The observation is the exact law on C([0,H],R) of the scalar diffusion

    dX=b(X)dt+sqrt(a(X))dW,

stopped at tau=inf{t: X_t not in I} and held afterwards. Since a>0 on the positive axis, all coefficients are smooth and uniformly nondegenerate on the closure of I; the localized law is unique. The stop is observable from X. This is the autonomous scalar class used in the finite-initial-jet obstruction, enlarged from unit births to general admitted scalar jumps. It is not the general unreconstructed-hidden-species class.

The primary target is the diffusion-law equivalence class, namely all reaction lists with the same alpha_n and beta_n. General reaction edges and individual rates cannot be recovered from these two sums without an additional admitted-family uniqueness statement.

## 2. Law-to-derivative adapter at the one fixed start

**Lemma 1.** The exact stopped law determines every finite collection of numbers

    a^(j)(x0), b^(j)(x0),  j>=0.

This is a statement about deterministic invariants of a probability law, not a consistent finite-sample estimator or differentiation of the drift of a single noisy path.

**Proof.** Work in the completed natural filtration of the canonical stopped process. It has the unique continuous semimartingale decomposition

    X_t=x0+D_t+M_t,
    D_t=integral_0^t 1_(s<tau) b(X_s) ds,
    [X]_t=integral_0^t 1_(s<tau) a(X_s) ds.

Bounded coefficients on the stopped compact interval justify the martingale identities in the natural filtration by conditioning. Uniqueness follows because a continuous local martingale of finite variation is constant. Quadratic variation is likewise unique. Thus the law determines D and [X], up to the usual indistinguishability of canonical versions.

Before tau, take the time densities U0=a(X) and V0=b(X). At zero use right limits. At tau use the continuous left limit, then hold this value, rather than replacing it by the post-exit zero density. These are continuous semimartingales because they equal the smooth functions a(X^stop) and b(X^stop). The density construction is possible for each finite collection using common almost-sure subsequences for quadratic-variation approximations and continuity. No claim that a fixed universal subsequence works simultaneously for every possible source is needed for the identification implication.

If Uj=a^(j)(X^stop), Ito's cross-variation formula gives

    d[X,Uj]_t/dt = 1_(t<tau) a(X_t) a^(j+1)(X_t).

Divide by the strictly positive U0 before the stop, then extend continuously to the stop and hold. This recovers U_(j+1). The same recursion with Vj=b^(j)(X^stop) recovers V_(j+1):

    U_(j+1) = (d[X,Uj]/dt)/U0,
    V_(j+1) = (d[X,Vj]/dt)/U0,                 t<tau.

The initial values are the claimed derivatives. Since tau>0 almost surely, every finite recursion is defined on an initial positive time interval. Values after tau are never mistaken for the physical coefficient. Alternatively, equality of two laws gives common canonical D and [X], then the same finite recursion under that common law proves equality of all these deterministic initial values. QED.

The variance side is path-functional quadratic-variation extraction. The drift side uses the exact law's canonical drift, not a pathwise drift estimator. This distinction matters when counting physical information.

## 3. Exact supplying theorem and normalization

Let E be the shifted Euler operator

    (E f)(x)=f(x)+x f'(x).

It satisfies E^k(x^n)=(n+1)^k x^n. Define the law invariants

    M_k=(E^k a)(x0)=sum_n alpha_n x0^n (n+1)^k,
    B_k=(E^k b)(x0)=sum_n beta_n x0^n (n+1)^k.

For each k these require derivatives only through order k, so Lemma 1 supplies them without changing the initial state. In particular M_0=a(x0)>0. The actual normalized positive atomic law is

    mu=sum_(n in S) [alpha_n x0^n / M_0] delta_(n+1).

Its r nodes are distinct and strictly positive, including when the zero-order reactant n=0 is admitted. Its weights are strictly positive and sum to one. Its ordinary moments are M_k/M_0. A rival produces the same kind of finite positive law, with no bound on its support size or maximum node.

The relevant previously checked project declaration is

    Astra.CommonMoment.support_card_le_of_equal_sparse_moments

from CMSeparation.lean, reproduced with exact source and verification scope in the [CM-T02 component certificate](https://github.com/Sodelin/Research-Commons/blob/514648b697aeed8f46582109cfeefcd7707cd738/research/2026-10-15-common-moment-checked-component/CM-T02-CERTIFICATE-001.json). It assumes two finite strictly positive probability laws on distinct strictly positive real nodes and 2*target.card+1 distinct natural-number exponents with equal moments. Its conclusion is rival.card<=target.card. The direction is important. It does not by its stated conclusion alone identify the nodes, original reaction list, or physical observation adapter.

Here ordinary exponents 0,...,2r allow the classical stronger support certificate directly: for the target nodes z_1,...,z_r, put

    Q(z)=product_(i=1)^r (z-z_i)^2.

This degree-2r polynomial is nonnegative everywhere and zero exactly at the target nodes. Equal moments through 2r imply integral Q dnu=integral Q dmu=0. Positive rival weights force every rival node into the target set. The first r moment equations then identify the weights by the ordinary Vandermonde matrix. Thus nu=mu.

This annihilating-square proof is classical and is the ordinary-moment specialization of the existing positive-support mechanism. Neither it nor its 2r+1 count is a new contribution of this note. The source-normalization step, node shift, and physical derivative adapter are stated explicitly to prevent importing the supplier without its hypotheses. The old abstract component's Lean evidence does not verify this new stochastic adapter.

## 4. All-rival finite signature for the scalar law fibre

**Theorem 2.** Fix any target in Section 1 with r active reactant degrees. For every admitted finite rival, regardless of its degree or edge count, the following are equivalent:

1. The exact stopped path laws from the common x0 on [0,H] are equal.
2. Their finite signatures agree:

       M_k,  k=0,...,2r;     B_k,  k=0,...,r-1.

3. All variance and drift coefficients agree: alpha_n=alpha'_n and beta_n=beta'_n for every n.

This uses 3r+1 scalar law invariants, not 3r+1 trajectories, sampling times, preparations, or finite-sample measurements.

**Proof.** (1) implies (2) by Lemma 1. Suppose (2). The equality of M_0 supplies the same positive normalization. Section 3's positive-moment certificate gives equality of the normalized measures, hence identical supports S and identical alpha_n x0^n. Since x0>0, alpha_n=alpha'_n. In particular the rival has no hidden additional reactant degree: positivity of its variance coefficients is essential to this conclusion.

The supports of both drift polynomials lie in the now-common S. The r equations for B_k give

    sum_(n in S) (beta_n-beta'_n) x0^n (n+1)^k=0,
                                                    k=0,...,r-1.

The Vandermonde matrix at distinct nodes n+1 is invertible; beta_n=beta'_n for every n. This proves (3). Finally (3) gives the same scalar coefficients and the same observable stop, so localized uniqueness gives (1). QED.

**Unit-birth specialization.** If the source class consists only of nA->(n+1)A, then b=a. The signature M_0,...,M_(2r) alone is sufficient. Every coefficient is an individual aggregated reaction rate, so this identifies the exact graph and rates against all finite unit-birth rivals. This is the same source class and observable-stop experiment as the preceding finite-initial-jet obstruction. There is no contradiction: that obstruction lets r grow with the prescribed jet order, whereas this count depends on the fixed target's r.

**Unit forward/reverse specialization.** If only v=+1 and v=-1 are allowed, with v=-1 excluded when n=0, the identified coefficients recover the rates as kappa_(n,+1)=(alpha_n+beta_n)/2 and kappa_(n,-1)=(alpha_n-beta_n)/2. Admission already guarantees these rates are nonnegative and the excluded n=0 reverse rate is zero.

**General jumps.** Network/rate uniqueness is false without such restrictions. At reactant degree n=1, allow jumps v=1,2,3. Positive rate vectors (1,4,1) and (4,1,2) both give beta_1=12 and alpha_1=26. They therefore have exactly the same observed diffusion law under the theorem, although the individual rates differ. This is the familiar generator-level ambiguity, not a new nonidentification mechanism.

## 5. What is and is not resolved

The exact result combines an experiment-specific fixed-start derivative adapter with the existing positive-moment supplier. It does not rename a full-state coefficient/cone criterion as a new theorem. Faul, Hoessly and Xia's [generator and reaction-vector analysis](https://doi.org/10.1017/S0956792526100382) remains the prior structural background; the coefficient sums above are its scalar specialization.

The result needs an autonomous scalar observed diffusion and an observable interval exit. For a general projected hidden diffusion, the observed drift is a conditional characteristic rather than the unconditioned polynomial b(X), and the variation density can depend on hidden state. The recursion then follows full-state covariance directions, not ordinary derivatives in the observed coordinate. No positive atomic degree response follows automatically. The finite-family neutral and catalytic reconstructions supply special closures, not a uniform closure for all finite hidden reaction networks.

If r is unknown, the theorem is target-dependent existence of a finite signature. It does not by itself supply a finite-precision stopping rule or an effective representation of exact law access. An adaptive Hankel/positive-support decision procedure would need an explicitly admitted exact-arithmetic response oracle. There is no stability, statistical sample-complexity, noisy-data, discrete-time, or arbitrary hidden-stop conclusion.

In particular, a finite list of law-determined real invariants is not automatically an effective legal finite-experiment or response interface. The proof supplies no implementation of exact canonical-drift extraction or exact derivative queries from an external representation of a law.

Historical novelty of the fixed-start adapter or its combined scalar statement is not established. All bracket, canonical semimartingale, positive-moment and Vandermonde ingredients are classical; only the displayed experiment-specific join is being recorded here as an author-checked specialization. General fixed-start partial-observation closure and a full formal stochastic proof remain open.
