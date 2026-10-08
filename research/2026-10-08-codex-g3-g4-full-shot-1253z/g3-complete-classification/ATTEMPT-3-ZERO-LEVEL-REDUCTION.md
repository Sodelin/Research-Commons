# Addendum: isolate every unbounded critical-count branch in exact unit levels

Contributor: Codex G5 lane, 8 October 2026. **Hand corollary candidate; independent root review requested.** This consumes frozen ATTEMPT-3-ARITHMETIC-BOUNDARY-INDUCTION.md SHA256 1fb16f34f2bbc986da57cd14d43c0df3e093af26ff73a1a97441d3380cea3199. Its statement remains supplied-algebraic-normal, fresh natural unexposed COMMON, with the same actual f_i/H_i and whole-word tuple. No new computation, theorem-prover, QE or source engine was executed.

## Exact source partition

Supply algebraic nonzero c and its rational basis rows v_k as in Theorem 1. Clear their denominators to integer rows e_k; let B_k=product_i f_i^e_ki. Define

    Z_0={theta in Z_c: B_k(theta)=1 for every k},
    Z_* = Z_c minus Z_0.

Both sets are exact semialgebraic sets, after positive denominators are cleared. On the CRITICAL set, Z_0 is precisely {theta: c dot H(theta)=0}, including real nonalgebraic theta. Indeed c dot H is constant on each connected component; evaluate its value at an algebraic sample point and apply the same Baker basis argument. Zero is equivalent to every rational-basis log level being zero. Theorem 1 extends those identities to the entire component. This equivalence is not claimed off the critical set.

**Corollary.** There is epsilon(c)>0 such that every actual pair theta=(p,q) in Z_* satisfies p(1-q)>=epsilon(c). If Z_* is nonempty, a positive rational epsilon is effectively computable from supplied c by RCF. Consequently a critical word with algebraic target m_1 has at most floor(n/epsilon) occurrences from Z_*, where m_1>2^(-n). Only Z_0 occurrences can escape this count bound.

**Proof.** Theorem 1 makes every B_k constant on each connected component of Z_c. There are finitely many components. Thus Z_* is a union of whole components, each with at least one positive constant level different from one. Suppose one such component had a sequence with p(1-q) tending to zero. For every exponent,

    0<=1-f_i=p(1-q^lambda_i)<=lambda_i*p(1-q),

so all f_i tend to one. Its constant B_k levels must all be one, a contradiction. Each off-unit component therefore has a positive pair-loss floor, and finiteness of components makes the minimum floor positive. This does not bound individual p, q, or their duration expectations separately.

Enumerate rational epsilon=2^(-j) and decide the real-algebraic assertion

    exists theta in Z_*: p(1-q)<epsilon.

The positive-floor theorem guarantees eventual FALSE; the first such epsilon is valid. The empty set is detected directly. For each actual occurrence H_1>=p(1-q), and the whole word's positive baseline and all other factors contribute nonnegative H_1. Hence total off-unit count is less than n/epsilon exactly as in the inherited positive-loss argument. QED.

## A finite exact necessary level census from the supplied normal

If c dot Lambda=0, each e_k dot Lambda=0 by Q-independence. Component decomposition and algebraic sampling compute the finite level vectors

    b(C)=(B_1(C),...,B_r(C))

of the off-unit components. For one actual critical word,

    product_i m_i^e_ki = product_(off-unit occurrences j) B_k(theta_j).

The ordinary baseline disappears because e_k dot Lambda=0; every unit-level factor contributes exactly one. With the off-unit count bound, these target monomials must belong to a FINITE computable list of simultaneous positive algebraic level products. All rows refer to the SAME occurrences and their same component multiplicity vector. Exact algebraic comparison decides this necessary predicate.

Passing it is not attainment. The off-unit cells still have parameters coupled to their complete signatures, and the arbitrary unit-level word remains. The level equations cannot replace those full source equations.

If Z_0 is empty, all critical occurrences are count-bounded. Enumerating the bounded critical-word equations with the supplied normal, ordinary baseline and original strict source domains gives a terminating RCF recognizer for that promised critical-word class. It remains a supplied-normal predicate, not whole-source recognition from m alone. If Z_0 is nonempty but a separate RCF test proves it has a positive loss floor, that same conclusion applies. This corollary does not assert that every Z_0 has such a floor.

## The tempting recursive full route, and the precise remaining quantifiers

After selecting the bounded off-unit factors, the remaining exact source is a product of actual unit-level factors and the ordinary baseline. Its log signatures lie in the rational space intersection_k ker(v_k), of dimension d-r<d, and its positive moment signatures satisfy the corresponding exact monomial equations. A rational lattice basis/positive torus parametrization can express those fewer coordinates without changing the original factors or their integer occurrence counts.

This is a genuine reduction of value-space dimension. It is NOT the accepted rank-at-most-two affine whole-joint compiler theorem: logarithmic/subtorus dimension is not affine dimension of the original joint probability rows. Nor is it a smaller Kingman cap. Its generators are the restricted semialgebraic set Z_0, with the same unknown counts and actual source dependence. Invoking a lower-cap COMMON recognizer, convex mixing, conic fractional weights or fresh independent replicate factors here would change the problem.

A complete induction would need a uniform source theorem deciding finite multiplicative-semigroup membership for EVERY such restricted critical generator class, with input-derived finite handling of the normal family. Neither theorem is supplied by dimension reduction alone. The unknown normal c still ranges over unbounded algebraic degrees/heights and may approach low-rank/neutral strata; a count bound depending on c is not an input-only one-witness bound.

Thus the attempt exposes the remaining dangerous set exactly, rather than hiding it: Z_0 with actual integer words and unknown algebraic normal. Rational c has r=1, so it is already within the unresolved case; the independently accepted rational attained-boundary family cannot be omitted. A source-specific proof that all these unit-level words admit effective bounded compression would advance the master. An example of such a word alone, or its rank-deficient presentation, would not refute it.

Original G3 still needs all-core coupled observation-fibre attainment, both inheritance mechanisms and original shared control/register semantics. The present exact supplied-normal split does not discharge those obligations, decide every boundary fibre, produce a full NO algorithm or prove impossibility. No UNKNOWN is returned as NO.

## Attribution and review

Positive-loss counting, algebraic feasibility, semialgebraic component constancy and Baker's theorem are inherited. The new step is applying the algebraic-normal rational splitting to separate all nonunit critical components with an RCF-computable floor, leaving the precisely defined simultaneous unit-level branch. The predecessor source pins retain the actual COMMON compiler, rational-normal level prior and accepted Baker review. No numerical epsilon, execution count or formal verification is claimed. Historical novelty is unassessed; root review remains requested.
