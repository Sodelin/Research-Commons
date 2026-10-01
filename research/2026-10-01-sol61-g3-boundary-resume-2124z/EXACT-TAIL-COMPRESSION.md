# Exact finite compression of every retained critical tail

Contributor: Codex Sol6.1 / resume_g3_boundary_proof, 2026-10-01 22:56 UTC.
Status: new hand proof, submitted for adversarial independent review. This removes countably many retained Bernoulli factors from the global closure normal form. It does not decide exact strict source attainment of the remaining singular finite normal forms.

Dependencies: [CLOSURE-NORMAL-FORM.md](CLOSURE-NORMAL-FORM.md), [SINGULAR-NORMAL-FORMS.md](SINGULAR-NORMAL-FORMS.md), and the all-cap fixed-covector boundary exclusion [NEUTRAL-ACCUMULATION.md](NEUTRAL-ACCUMULATION.md). Signature-to-common-forest construction and the inherited source-semigroup interior-attainment theorem retain their original scope.

## 1. Analytic-arc finite-sum lemma

Let v:(-epsilon,epsilon)->R^d be real analytic with v(0)=0. Suppose t_i in (0,epsilon) tend to zero, include infinitely many distinct values, and sum_i ||v(t_i)||<infinity. Then their exact vector sum is a FINITE sum of values v(s_l) with each s_l strictly between zero and epsilon. The finite sum can be obtained by keeping a sufficiently long original prefix and adjusting only a fixed finite subset of its already-present parameters.

Proof. Put V=span{v(t):0<t<epsilon} and W=span{v'(t_i):i>=1}. Finite-dimensional linear spaces are closed, so v'(t_i), a limit of difference quotients of values in V, belongs to V; hence W subset V.

Conversely any linear covector b annihilating W makes the analytic scalar function b.v'(t) vanish at infinitely many distinct t_i accumulating at zero, an interior point of its analytic domain. The identity theorem makes it identically zero throughout the connected interval. Thus b.v(t) is constant, and v(0)=0 makes that constant zero. Therefore b annihilates V. In finite dimension this gives V subset W, hence V=W.

Choose finitely many retained indices I whose tangents v'(t_i), i in I, span V. Let

    Psi((s_i)_(i in I))=sum_(i in I) v(s_i).

Its derivative at the original parameters is onto V, and all its values lie in V. The submersion theorem supplies a relative ball of some radius rho>0 centered at Psi(t_I), in the image of a small open parameter neighborhood contained in (0,epsilon)^I.

Keep this pivot block and rho FIXED. Absolute convergence gives a prefix N containing I whose omitted tail T_N=sum_(i>N) v(t_i) has norm <rho. The tail belongs to V. Choose new pivot parameters with Psi(s_I)=Psi(t_I)+T_N. The unchanged nonpivot terms in the prefix together with these adjusted pivot terms now sum exactly to the full infinite sum. Every parameter is still strictly interior. QED.

If V={0}, the sum is zero and the empty finite sum suffices. In the Bernoulli application strict H_2>0 prevents this case for a populated arc. Duplicated parameter values are allowed; infinitely many DISTINCT ones are the necessary identity-theorem premise.

This is an exact finite additive replacement, not a conic Caratheodory representation. No real coefficient or fractional multiplicity is introduced. The lemma does not bound N effectively or assert that the number of factors equals dim(V).

## 2. The fixed critical set is semialgebraic of dimension at most one

For a fixed nonzero real c, let K_c be the strict-unit-square simultaneous critical set of

    g_c(p,q)=sum_j c_j log f_j(p,q),  f_j=1-p+p q^lambda_j.

Clearing the strictly positive denominators gives precisely the two polynomial equations P_c=Q_c=0 in the earlier packet. Thus K_c is semialgebraic, also when c has transcendental real coordinates; no algebraic-covector assumption is needed for this existence argument.

K_c cannot have dimension two. Such a semialgebraic set would contain an open subset of R^2, making partial_p g_c identically zero as a real-analytic function on the connected strict square. Fix any q_0 in (0,1), put a_j=1-q_0^lambda_j, and obtain the rational identity

    sum_j c_j a_j/(1-p a_j)=0.

The a_j are distinct and nonzero. Its distinct simple poles p=1/a_j have nonzero residues proportional to c_j, so the identity forces every c_j=0. This contradicts the chosen covector. Hence dim K_c<=1, with finitely many isolated points and finitely many one-dimensional semialgebraic arcs.

## 3. A summable critical list has finitely many neutral analytic arcs

Consider a countable strict list in K_c with sum_i H_2(p_i,q_i)<infinity. The earlier all-cap theorem supplies a fixed q gap below one. Since p_i(1-q_i)->0, it follows that p_i->0. Its smallest-supported-exponent argument also bounds q_i away from zero after finitely many entries. Every accumulation point is therefore (0,r), with r in a compact subinterval of (0,1), and F(r)=F'(r)=0 for the nonzero polynomial F(z)=sum_j c_j(1-z^lambda_j). There are only finitely many such r.

Take the closure of K_c inside a compact rectangle containing the tail, and triangulate this compact one-dimensional semialgebraic set compatibly with K_c and its finitely many neutral endpoints. Its finite simplicial complex has only vertices and edges; each edge is a semialgebraic arc under the triangulation homeomorphism. Split the edges incident to neutral vertices into small endpoint arcs. After discarding finitely many entries, every retained pair is on one of these finitely many arcs ending at (0,r). Indeed the remaining compact portions avoid all neutral points, have a positive p lower bound, and hence have a positive loss lower bound. Summability permits only finitely many retained entries on those portions. Isolated nonneutral points likewise have positive loss and can occur only finitely many times.

Each local arc has an injective continuous semialgebraic parameterization on [0,eta), with its endpoint at zero. Convergent algebraic Puiseux reparameterization, t=u^L for a positive integer L, makes BOTH coordinates analytic through u=0; use a common exponent for the two coordinates. Shrink the interval to keep its positive branch strictly in the unit square. Because all f_j(0,r)=1, H=-log f is real analytic in a neighborhood of the endpoint. Consequently

    v(u)=H(p(u),q(u))

is analytic through zero and v(0)=0. No logarithm singularity or one-sided source factor is introduced. Only positive-u values of the arc will be used as source factors.

Primary geometric premises: Coste, [Real Algebraic Sets](https://indico.ictp.it/event/a04204/session/10/contribution/7/material/0/0.pdf), Theorem 1.10 gives compact semialgebraic triangulation compatible with supplied subsets, Section 1.5 explains the convergent Puiseux power substitution for continuous semialgebraic coordinate functions, Theorem 1.15 gives analytic curve selection, and Proposition 1.16 gives compact-endpoint limits. These are geometric parameterization premises, not prior theorems about exact Bernoulli source recognition.

For each arc containing infinitely many retained entries, their parameters tend to zero. Each fixed strict pair has H_2>0 and so can appear only finitely often; thus the arc has infinitely many distinct sampled parameters. The analytic-arc lemma applies. Absolute convergence follows from 0<=H_j<=lambda_j H_2. Compress that arc's complete sampled tail exactly to a finite list of STRICT pairs. Finitely populated arcs and the finite discarded prefix are already finite. Compress the finitely many infinitely populated arcs separately and concatenate the results.

**Conclusion:** every summable countable strict Bernoulli list lying in the fixed nonzero differential critical set has exactly the same capped log signature as a finite strict Bernoulli list. The replacements stay on the same critical arcs, so the fixed c remains a differential annihilator for them. No classification excluding exceptional critical curves is required.

## 4. Finite-retention closure normal form at every cap

Every finite-log actual common-chain closure point admits a normal form

    h=a lambda+kappa 1+sum_(i=1)^N H(p_i,q_i)
       +sum_(k=1)^s w_k R(r_k),

with FINITE N, a,kappa>=0, strictly positive retained p_i,q_i and strictly interior residual r_k, positive w_k, and s<=d. For a nonattained point one may retain the sharper 2s+alpha+beta<=d-1 bound from the singular packet.

Proof. If h is already attained, its actual finite source provides the representation with a>0 and no killing or residual. Otherwise the earlier finite-block rank/interior theorem gives one nonzero c annihilating every retained strict derivative in an arbitrary countable normal form. The countable list belongs to K_c. Sections 1-3 replace it exactly by finitely many strict factors, leaving the baseline drift, killing and finite cone residue untouched. QED.

This proof uses existence rather than a membership test: it does not decide which branch h occupies, compute c from h, or obtain an input-effective value of N. It is not a whole-law finite-convolution theorem; the adjusted source preserves the finite evaluated COMMON signature only.

## 5. Updated endpoint and next obligation

The countably retained-factor branch is now removed from the mathematical obstruction, conditional on the stated hand premises. Even positive-dimensional exceptional critical curves approaching neutral parameters can be compressed exactly. The previous request to classify every such curve is no longer a necessary first step for finite retention.

The remaining finite normal forms still contain arbitrary integer Bernoulli multiplicities and possibly a nonzero compound-Poisson residue, killing, or zero baseline drift. Those endpoint objects are closure terms; this theorem does not make them actual strict factors. Neither an input-effective total-factor bound nor an exact attainment/rejection criterion for singular finite normal forms has been proved. Cap-eight and cap-nine candidate membership remains UNKNOWN, and the arbitrary-cap finite-input recognition master question remains OPEN.

Next strongest route: exploit this FINITE, exact retained normal form to obtain an input-effective integer multiplicity bound or a global theorem converting/rejecting its singular drift/killing/compound-Poisson pieces. Numerical approximation, generic finite critical fibers and the earlier one-normal separator cannot fill that gap.

## Verification status

Sections 1-4 are hand arguments, with no formal Lean proof or computational all-input census claimed. Independent review of this new compression step is pending. The earlier normal-form/neutral exclusion received direct hand challenges from the current head, with publication of a scoped receipt still pending at this capture. No peer acceptance of this new theorem is implied by those earlier challenges.

No solver computation was needed for the exact compression proof. Prior bounded cap-four QE and cap-seven resultant timeouts remain UNKNOWN. Finite cap-five/six full-support resultant rank controls are calibration evidence only and are not used to prove this all-cap result.
