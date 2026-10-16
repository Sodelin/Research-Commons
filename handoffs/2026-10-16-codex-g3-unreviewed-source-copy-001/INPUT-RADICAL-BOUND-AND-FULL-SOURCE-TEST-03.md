# Input-derived radical bounds and the full-source test

15 October 2026. Private mathematical continuation by Codex. This is an unreviewed hand derivation and a tested proof strategy, not a complete G3 recognizer, an independent acceptance, a computation, or a formal proof. No source, solver, numerical checker, RCF procedure, compiler, or parameter search was executed. No external publication is selected. Earlier sources and private handoff 02 remain unchanged.

## 1. Original destination and the attempted implication

The destination remains terminating exact recognition of the original finite rational/effectively algebraic JOINT input in the admitted unknown-size positive source class. A witness must use one original graph, original-ID assignment and physical parameter bank across the complete retained menu, with its actual COMMON/INDEPENDENT semantics, chronology and register. No closure point, independently fitted rows, imposed finite architecture, or supplied normal substitutes for that obligation.

This attempt attacks the terminal integer-power problem by asking whether algebraic INPUT coordinates bound a repeated physical block's multiplicity. It produces an actual input-derived bound for a precisely specified branch. It then tests the proposed extension against a source-faithful full-coordinate construction. The extension to the master does not follow.

The two distinct outcomes are:

1. A computable finite multiplicity bound for a repeated one-type COMMON branch whenever a decidable polynomial-identity test succeeds. The input may be effectively real-algebraic, not just rational. For rational input a direct prime-valuation bound is available.
2. Three freely retuned strict COMMON cell types already have a full-dimensional six-coordinate image. Moreover, a fixed rational complete profile has presentations with an arbitrarily long repeated weak tail and a retuned three-cell head. These facts identify why the polynomial/root argument cannot simply be promoted to arbitrary source words. The latter is NOT an unbounded-minimum-count example: the same profile has a short head-only witness.

## 2. Source interface and pins

Use cap seven, with the six distinct positive integer grades

    Lambda = (1,3,6,10,15,21).

For a normalized strict natural COMMON cell put

    f_lambda(p,q) = 1-p+p*q^lambda,
    D_lambda(q) = 1-q^lambda,
    0<p,q<1.

The entire private-word kernel is encoded by the SAME six moments

    m_lambda = A^lambda * product_j f_lambda(p_j,q_j),  0<A<1.

This is the inherited actual COMMON source reduction. For N cells, the literal strict word

    E(b) [B_COMMON(b*q_j,b,p_j) E(b)]_(j=1,...,N),
    b = A^(1/(2*N+1)),

has exactly that baseline A and those factors. Every duration is strictly positive and finite and every inheritance probability is interior. All six coordinates refer to one pushforward law, not six selected measures.

Relevant preserved providers:

- Original exact criterion: Commons@eb284f41d13fff2602de4e98411fb15e5891f9e8, research/2026-09-30-g3-exact-source/EXACT-CRITERION.md, SHA256 3528692b34948807ad942be5ceaf02cea40a78dcdc7e5c7a963557cf224f4330.
- Original calibrated source proof: research/2026-10-06-dot-g3-calibrated-original-recognition-1422z/WORKING-PROOF-R2.md. Its accepted original SHA256 is 185b4c098a6255346b584e3e0298ab92c822f7caa65fa30dbd80ee4dfab3569c; the actually read local/public contributor-line projection is 13362 bytes, SHA256 c9b9c20a7878e1d1eb818ab827a6ea81089b5762eaeff8bdf4a3521ce0e8d3f6. PUBLIC-PROJECTION-PROVENANCE.json records that distinction. The unchanged independent review is SHA256 994fe7839cb793b43152d1aa7a2c29f8cee01a711cc5474f0ed47d07c41904b9. Its eight-row map is Phi(m)=(F(m),2/3,25/48).
- CALIBRATED-WITNESS-SIZE-COROLLARY.md in that directory: the actually read 5354-byte contributor-line projection has SHA256 8f9f1d89deda470d3990470da2bad0a3cb29b0bf40c5b2fc9f2ef0bf4d6226d2; provenance links its accepted original SHA256 3b7dac5200bfe00477a994fd7ed37870467e3cee5b4ce3859dd19b9fcfb0651c. The accepted extraction/embedding gives equality of minimum word hybrid count and minimum TOTAL original COMMON hybrid count on that calibrated profile. It does not extend to arbitrary original input or INDEPENDENT rivals.
- The prior full arithmetic attempt, research/2026-10-08-dot-g3-input-arithmetic-attempt-1627z/INPUT-ARITHMETIC-AND-JOINT-HEAD-ELIMINATION-ATTEMPT.md, actually read 15127 bytes, SHA256 0e1b264a50e509f8881984fc4498d6d46fc40c5024c76b76f26a8ee74b262036, already retains nonunit heads and records why input relations do not become independent hidden-slot relations. Its pair-only cancellation and variable-specialization examples are preserved, not claimed anew.
- The fixed-real-normal floor, UNIT-CRITICAL-PUISEUX.md, SHA256 c94a4d25f50b49c071cbd92a675dfe1b22edb5e8a13ccc28b5409bd3f9ed0332, remains a supplied-normal provider. This note does not assume it supplies an input-derived all-rival normal.
- Earlier moving-normal source a2e1b3c7f358f4d663dd8bbfc33f372fd4ea6d0f / WEAK-CRITICAL-NORMAL-COMPACTIFICATION.md remains at its Root-relayed scoped HAND PASS. The private successor 02 is not independently accepted here.

## 3. Classical positive-radical input

Richard Carr and Cormac O'Sullivan, On the Linear Independence of Roots, arXiv:math/0703522v2, Theorem 1.1:

https://arxiv.org/pdf/math/0703522v2

The relevant statement and its proof in sections 1-2 were actually read for this attempt. The applicable consequence is classical: in a real field extension, finitely many radicals whose positive integer powers lie in the base field are linearly independent over that base field if every distinct pair is independent. The one- and two-element cases are immediate. The theorem works over a real number field, not only over Q. Its authorship and earlier Besicovitch/Mordell lineage are retained; no new radical-independence theorem is claimed.

We use it with a fixed effective number field K contained in R. If beta_j are distinct positive elements of K and n is such that

    (beta_i/beta_j)^(1/n) is not in K  for every i != j,

then the positive numbers beta_j^(1/n) are K-linearly independent. Positivity specifies the root and avoids root-of-unity substitutions.

### 3.1 Effective bound on radical denominators

For every positive effectively algebraic delta != 1 in a fixed effective real number field K, there is a computable N(K,delta) such that

    n>N(K,delta)  =>  delta^(1/n) is not in K.          (R)

Here is an explicit effective argument using classical absolute logarithmic height, Northcott finiteness and Kronecker's height-zero criterion, rather than assuming a unit-group oracle.

Let D=[K:Q]. One can compute a rational epsilon_D>0 such that every positive real algebraic alpha != 1 of degree at most D has

    h(alpha) >= epsilon_D.

Indeed, if h(alpha)<1 and the primitive minimal polynomial has degree d<=D, its coefficients have absolute values at most 2^d exp(d*h(alpha)) < 6^D. Enumerate the finitely many NONZERO integer polynomials of degree at most D with that coefficient bound. Isolate their positive real algebraic roots, discard 0 and 1, and choose a positive rational below 1 and below all their positive heights. Each remaining root has positive height: a positive real root of unity is 1, and Kronecker supplies the height-zero characterization. Algebraic height is computable, and a certified strictly positive computable real admits an effective positive rational lower bound. No zero test for polynomial expressions in logarithms is needed for this finite construction. Numbers of height at least 1 already satisfy the chosen lower bound.

Choose a rational H>h(delta) and an integer N>H/epsilon_D. If alpha=delta^(1/n) were in K for n>N, then alpha>0, alpha!=1, deg(alpha)<=D and

    h(alpha)=h(delta)/n < epsilon_D,

a contradiction. This proves (R) constructively. These are standard height facts used with their actual finite-degree hypothesis, not new height theory.

For rational delta, a sharper elementary bound needs no height machinery. Write v_l(delta) for its finitely supported prime-valuation vector. If delta^(1/n) is rational, every v_l(delta) is divisible by n. Therefore

    n > max_l |v_l(delta)|

excludes rationality whenever delta!=1.

## 4. An effective reciprocal-power obstruction for algebraic input

Let m=(m_1,...,m_d) be positive effectively real-algebraic input and let P in Q[z_1,...,z_d] be a specified polynomial. Work in K=Q(m_1,...,m_d), represented effectively by an algebraic primitive element and isolating data.

Expand P as sum_alpha a_alpha*z^alpha. Group its monomials by the exact positive algebraic value

    beta=m^alpha.

Algebraic equality and the sums of the rational a_alpha are decidable. After discarding groups with zero coefficient, write

    P(m^s)=sum_(j=1)^J c_j*beta_j^s,                 (E)

where the beta_j are distinct positive elements of K and c_j are nonzero rational numbers. Real powers here use the unique positive values; no new observations are introduced.

If J=0, this is identically zero for every real s. Conversely, distinct real exponentials are linearly independent as functions of s, so this grouping test exactly decides whether the displayed one-parameter function is identically zero. This converse is an elementary Vandermonde/derivative fact; it is not an oracle for arbitrary logarithmic-polynomial identities.

If J=1, P(m^(1/n)) is nonzero for every positive integer n. If J>=2, choose

    N=max_(i != j) N(K,beta_i/beta_j).

For n>N, section 3 makes the terms beta_j^(1/n) linearly independent over K. Since the coefficients c_j lie in K and are nonzero,

    P(m^(1/n)) != 0 for every n>N.                  (B)

Thus every solution of P(m^(1/n))=0 has an INPUT-COMPUTABLE bound on n unless the grouping test certifies the function is identically zero.

For RATIONAL input, K=Q and an explicit valid bound is

    N=max_(i != j, primes l) |v_l(beta_i)-v_l(beta_j)|.

The distinctness of the beta_j ensures a nonzero valuation difference for each pair. For n>N it cannot be a multiple of n. This is a finite exact factorization/valuation algorithm on the supplied rational input; it does not constrain the prime support of individual unknown source factors.

This theorem is about equality at the positive reciprocal-integer powers of ONE specified algebraic vector. It does not infer the sign of a general exponential polynomial near zero and does not eliminate arbitrary real exponents or integer vectors with independently varying bases.

## 5. Actual repeated-type COMMON branch

Define the strict one-cell moment image

    B={ (b^lambda*f_lambda(p,q))_lambda : 0<b,p,q<1 }.

Its Zariski closure V is defined effectively over Q. For example compute the elimination ideal

    I = < z_lambda-b^lambda*(1-p+p*q^lambda) : lambda in Lambda >
           intersect Q[z_lambda : lambda in Lambda].

A Groebner elimination algorithm supplies a finite generating set. No such algorithm was run here. Since there are six outputs and only three parameters, dim(V)<=3 and I contains a nonzero polynomial.

The repeated-type branch for supplied m is

    exists n>=1, 0<A,p,q<1:
      m_lambda=A^lambda*f_lambda(p,q)^n for every lambda.       (T)

For each fixed n this is a genuine same-parameter polynomial feasibility problem, and

    (T at n)  iff  m^(1/n) belongs to B.              (T-root)

In the forward direction b=A^(1/n); in the reverse direction A=b^n. The literal source word in section 2 realizes it. Strictness and the ordinary baseline are both retained.

Apply the grouping test of section 4 to the finite generators of I.

- If at least one generator gives J>=1, (B) supplies a finite bound N for EVERY repeated-type presentation of this particular input. Testing n=1,...,max(1,N) by fixed-n RCF decides (T). When J=1 the branch is excluded immediately by that polynomial. A returned witness uses one physical type repeated n times; a negative result excludes only that declared branch.
- If all generators give J=0, the curve m^s lies in V for every real s. This is an exactly detected exceptional alternative, not a YES or NO. Strict positive one-cell feasibility, the baseline, and the reciprocal-integer restriction still need to be checked; algebraic closure is not attainment.

An easily stated sufficient condition for the first case is multiplicative rank(m)>3. The algebraic torus generated by the positive curve m^s then has dimension greater than 3, so it cannot lie inside V. Equivalently, the integer multiplicative relations among m determine its toric ideal, and at least one generator of I must fail the identity grouping test. No algebraic independence of logarithms is assumed. Effective multiplicative-relation machinery could detect this sufficient condition, but it is unnecessary: the finite grouping test itself decides whether some generator is usable.

This is an input-derived finite bound, not a supplied-normal bound. Its exact limitations matter: (T) is one-type natural COMMON, not all source words; the data m are the complete slot coordinates, not arbitrary observed rows. A general original input instead imposes F_core(theta,slots)=y on one coupled fibre. The earlier arithmetic attempt explains why one cannot silently replace those unknown slots by y or fit each separately.

## 6. Full-dimensional strict head: the extension test

An unrestricted proposed next step was to apply a common finite collection of such polynomial obstructions to every finite-type head. Already THREE independently retunable strict COMMON types defeat that algebraic-dependence premise at these six coordinates. This test deliberately uses a full-rank head. It is not a counterexample within a coherently constrained singular/critical-head branch and does not refute a strategy that proves the needed smaller algebraic varieties on those branches. Such a restriction must be retained and justified, not dropped during elimination.

Fix A=1/2 and three distinct rational ratios, for example

    r_1=1/4, r_2=1/2, r_3=3/4.

Consider the polynomial six-output map

    G_lambda(theta)=A^lambda*product_(j=1)^3 f_lambda(p_j,q_j),
    theta=(p_1,q_1,p_2,q_2,p_3,q_3).

### 6.1 Exact rank certificate without a numerical determinant

The six columns D(r_j),D'(r_j), j=1,2,3, are linearly independent.

Otherwise a nonzero row c annihilates all of them. The nonzero polynomial

    Q_c(t)=sum_lambda c_lambda*(1-t^lambda)

then has a double root at each of the three distinct positive r_j and also a root at 1. These give at least seven positive roots counted with multiplicity. Q_c has at most seven nonzero monomials, including its possible constant term, hence Descartes' rule bounds its positive roots by six. If the constant term vanishes the bound only decreases. This contradiction proves the rank assertion. This uses classical Descartes/root-count mathematics already present in the CM sources; it is not a new root theorem.

For the logarithm of G, its derivative columns, after dividing the q_j column by p_j and ignoring nonzero signs, are

    D(q_j)/f(p_j,q_j),  D'(q_j)/f(p_j,q_j).

At q_j=r_j and p_j all tending to zero these tend to the six independent columns just proved. One can specify a rational p_0 without executing a search. Let M_0 be that rational six-by-six matrix, set

    B_0=max(1, ||M_0^(-1)||_infinity),
    p_0=1/(1024*B_0).

Here the norm is the induced maximum row-sum norm; the formula defines an exact rational, not a decimal approximation. For 0<p<=1/2, every entry of the scaled derivative matrix differs from M_0 by at most 42*p: |D|<=1, |D'|<=21, and |1/(1-p*D)-1|<=2*p. Its matrix norm difference is at most 252*p. Thus

    ||M_0^(-1)*(M(p_0)-M_0)||_infinity <=252/1024<1,

so M(p_0) is invertible. The actual unscaled q columns have extra nonzero factors p_0, and passing between G and log G multiplies by an invertible positive diagonal matrix. Therefore the actual strict Jacobian of G at

    theta_0=(p_0,r_1,p_0,r_2,p_0,r_3)

is invertible. All matrix operations in the definition of p_0 are rational; they were not executed here. The exact formula fixes a rational target rather than leaving an unspecified sufficiently-small-parameter premise. The actual output

    m^*=G(theta_0)

is positive rational. The inverse-function theorem gives a neighborhood O of m^* in the strict image of this same three-cell chart. In particular m^* is in the interior of the ordinary six-coordinate moment body: O already consists of actual positive finite-law moments. Thus the strict moment-body admission premise of the calibrated source construction is met, not silently discarded.

Consequently its six-coordinate image contains an open subset of R^6. Its Zariski closure is ALL of affine six-space: there is no nonzero polynomial that vanishes on all strict three-type profiles. This is a concrete failure of the polynomial-identity premise, not merely a warning about an unspecified larger architecture.

### 6.2 One fixed rational complete input, arbitrarily many repeated weak factors

Fix that same rational m^* and choose any rational r_* in (0,1). For each integer n>=1 let

    g_(n,lambda)(epsilon)=f_lambda(epsilon,r_*)^n.

As epsilon decreases to zero, m^*/g_n(epsilon) tends to m^*. Since O is open, one can choose a strictly positive RATIONAL epsilon_n<1/(n+1) such that

    m^*/g_n(epsilon_n) belongs to O.

It therefore has a strict three-cell head theta_n satisfying the exact simultaneous equations

    A^lambda*product_(j=1)^3 f_lambda(theta_(n,j))
      * f_lambda(epsilon_n,r_*)^n = m^*_lambda
      for ALL six lambda.                           (F)

The equations in theta_n are polynomial over Q with strict inequalities. Since a real strict solution exists, real-closed-field transfer gives a real-algebraic strict solution; a fixed-n RCF algorithm can select it. This is exact equality, not an approximation or separate choices for the coordinates. No bound independent of n on the degrees of the selected head parameters is proved or assumed.

The literal word of section 2, with N=n+3 and baseline A, realizes (F) in the actual positive natural COMMON model. Its n repeated tail cells are nonidentity and strict. One graph and one parameter tuple determine the complete six-coordinate law.

There is also a single explicit rational tail sequence, with no per-n coin selection: take r_*=1/2 and epsilon_n=1/n^2 for n>=2. For every coordinate,

    1 >= g_(n,lambda)(epsilon_n) >= 1-1/n,

by Bernoulli's inequality. Therefore m^*/g_n(epsilon_n) tends to m^*, uniformly across the six coordinates, with coordinate error at most 1/(n-1). For ALL sufficiently large n it lies in O, and the local inverse gives a head theta_n tending to theta_0. Each such exact polynomial fibre has an algebraic strict head. Thus arbitrarily long presentations can be taken with exactly specified rational tail parameters, rather than relying only on separately chosen small coins.

Now apply the inherited calibrated original-source embedding. The SINGLE rational eight-row input

    y^*=Phi(m^*)=(F(m^*),2/3,25/48)

has, for every n, an admitted original COMMON realization of this kind, with the original graph/assignment and all eight rows retained in one physical bank. No original row was independently retuned. This lifts the variable-head control beyond the pair-only examples in the earlier arithmetic attempt.

There is also the head-only three-cell realization theta_0. Therefore the minimum word count and minimum original COMMON hybrid count of y^* are at most THREE. The unbounded n+3 presentations do NOT refute a computable upper bound for ONE witness, a minimum-count compression theorem, or G3 decidability. They refute only the proposed stronger step that input arithmetic should bound every repeated-tail multiplicity while an independently variable head is retained. That stronger step is not needed by every possible recognizer.

The same explicit sequence also gives a full-input version of the prior pair-only prime-support warning. Let S be ANY proposed finite set of rational primes, including all primes of the fixed rational input and 2. Take arbitrarily large n divisible by every prime in S. The pair-coordinate tail factor is

    f_1(1/n^2,1/2)=(2*n^2-1)/(2*n^2).

Every prime of S divides n, so none divides 2*n^2-1. That numerator exceeds 1 and is coprime to its denominator. Hence this actual rational tail factor contains a prime outside S. Its n-fold product has positive valuation there, cancelled exactly by the rational aggregate head moment m_1^*/g_(n,1). All six complete moments, and therefore the original eight-row input, remain fixed. Individual retuned head factors need not be rational; no claim assigning rational valuations to them separately is made. This excludes an all-presentations restriction to input-prime support. It does NOT exclude an existential short representative with better arithmetic data.

The open-chart/retuning principle is inherited classical IFT/RCF machinery, also used in the accepted source-interior work. The concrete content here is its explicit six-coordinate, rational-target, full calibrated-input application to this particular radical-count strategy. Historical novelty is unassessed.

## 7. Disposition of the full G3 attempt

The complete attempted route was:

1. Retain the original coupled finite-core fibre and enumerate actual positive witnesses for YES.
2. Obtain a source-complete coherent critical/normal branch for an unknown-size witness.
3. Convert its still-unbounded integer occurrences into reciprocal powers of an INPUT-fixed algebraic vector in a proper fixed polynomial variety.
4. Apply section 4's finite input-derived bound and discharge every branch by fixed-size RCF.
5. Exclude all original alternatives before returning NO.

Section 4 establishes a genuine arithmetic tool for step 3 WHEN its premise is actually met. Section 5 supplies one physical branch where it is met outside an exactly detected exception. Section 6 rejects an UNRESTRICTED extension to all heads: a freely variable three-cell head has no common nonzero polynomial identity at all, and unbounded weak powers can be hidden behind its retuning at the same full rational input. Because those heads are full-rank, this does not refute the more careful singular-head route in step 2. It shows why one cannot discard that route's constraints or demand a bound for every presentation instead of a suitable minimum witness.

The substantive unresolved singular case is still: the normal and its algebraic critical types vary with the unknown source, distinct types have independently varying integer multiplicities, and the output need not be a common n-th power of a point in one proper INPUT-controlled variety. Even if those counts have a common divisor, the primitive multiplicity vector is still unbounded. A fixed finite-type count is not a bounded primitive word. No input-effective repetitive template, primitive multiplicity vector, head field bound or finite original-input list of such templates has been proved here. The toric exception in section 5 also remains undisposed; its exact detection does not prove physical feasibility or infeasibility.

For arbitrary original observations the extra obstruction remains that the complete slot vector itself is unknown on a polynomial joint observation fibre. COMMON factors commute in this scalar reduction; actual INDEPENDENT/BOTH products need not and retain position-dependent prefix/suffix pullbacks. Neither a scalar root nor independently solved moments preserve those semantics.

Thus this attempt does NOT give the requested all-rival termination/negative certificate, and does NOT disprove its existence. It provides a reviewable input-derived finite-bound lemma and an actual-source test of its precise extension. The remaining target is still an input-effective bound or exact all-rival negative certificate for at least one faithful complete source representation, including all coupled and exceptional branches. The prior moving-normal theorem and contact-escape candidates do not silently supply that selection.

## 8. Evidence and review focus

Evidence here is hand/source argument only. Carr-O'Sullivan sections 1-2 and the indicated existing providers were read; no mathematical checker or algorithm described above was run. No independent review, Lean elaboration, axiom audit, runtime evidence, external acceptance or publication follows from this note.

Precise review targets are: the real-number-field scope of radical independence; the effective bounded-degree height gap; grouping and strict reciprocal-power equivalence; Descartes' seven-root rank certificate; preservation of all six equations while retuning the head; and the actual single-bank calibrated original-source lift. A reviewer must preserve the distinction between arbitrarily long presentations and arbitrarily large MINIMUM witnesses.

Full biological G3/G4 remain OPEN. Accepted CM/G2 results, obstruction originals, original failed/executed records, and all compiler/publication/privacy holds are unchanged.
