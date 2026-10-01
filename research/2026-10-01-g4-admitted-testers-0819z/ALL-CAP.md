# G4 beyond a supplied copy cap: exact boundaries and remaining effectivity

ID: ASTRA-G4-TESTERS-20261001-0819Z. Author/publisher: GPT-6 Astra Pro.  
Status: submitted hand proofs plus exact finite certificates; independent review pending.

This file concerns tester completeness/stopping, not G3 source membership or G5 target identification. All collision families below use actual finite positive four-taxon sources, and both members have the SAME displayed species-tree target. They do not assert an opposite-Q/S biological collision.

## 1. A constructive common-inheritance collision after every finite cap

**Theorem A.** For every integer M >= 2 there are two actual finite positive common-inheritance serial chains with M bigons each whose complete labelled forest kernels agree for every input size at most M, but disagree at M+1. They can be placed on the pendant A branch of the same positive four-taxon tree ((A,B),(C,D)). Every completion using at most M input copies at the chain then agrees, while a finite authorized rooted gene-topology observation at a higher copy allocation separates them.

The theorem is exact, not a small-error or boundary approximation. The edge survival parameters can be rational and the inheritance weights real algebraic and strictly interior.

### 1.1 Explicit polynomial construction

Put lambda_r = binom(r,2), choose q=A=1/2, and set

    p_i = i/(M+1), i=1,...,M,
    F(z) = product_i (1-p_i z),
    a_r = 1-q^lambda_r,
    H(z) = z product_{r=2}^M (z-a_r).

The M roots 1/p_i of F are distinct and exceed one. Choose disjoint rational intervals around these roots with both endpoints greater than one and opposite signs of F. Choose a nonzero positive rational t sufficiently small that adding t H does not change F's sign at any of those endpoints. For example, successive dyadic t terminate because there are finitely many nonzero endpoint values.

The polynomial

    F_t(z) = F(z)+t H(z)

has degree M, constant coefficient one, and exactly one simple real root in each of the M disjoint intervals. There are no other roots. Hence

    F_t(z)=product_i (1-p'_i z)

with distinct real-algebraic p'_i in (0,1). The interval sign certificates or Sturm root counts specify these parameters exactly; no floating-point near-equality is used.

Let B_i be independent Bernoulli variables with weights p_i, and use p'_i for the second model. Define

    X = A product_i q^B_i.

Then the sparse moments are

    mu_r = E[X^lambda_r] = A^lambda_r F(a_r).

The perturbed model has A^lambda_r F_t(a_r). They agree at r=1,...,M, but their difference at M+1 is

    A^lambda_(M+1) t H(a_(M+1)) > 0.

For a common chain, every k-token forest probability is a rational linear combination of mu_1,...,mu_k: condition on the total selected duration and use the Kingman transition formula in PROOF.md. Conversely mu_k is the no-merger coordinate. This proves exact equality of ALL labelled forest kernels through M and separation at M+1.

### 1.2 Every parameter belongs to an actual positive source

A binary-product duration law is realized without zero-length connectors as follows. For L=M let

    a = 1-(1-A)/(4L+1).

Give each bigon arm survivals a q and a, with probability p_i or p'_i on the first arm; give each following connector survival a. Give the leading connector survival A/a^(2L).

Bernoulli's inequality gives a^(2L)>A. Thus the lead, all connectors, both arms and all inheritance weights are strictly inside (0,1). The deterministic survival factors multiply to A, so the chain has exactly the claimed X. Inserting it on the pendant A bridge preserves binary degree, LSA rooting, cut-child status, the outer-labelled embedding and every displayed species-tree split.

### 1.3 A genuinely observed separating event

Take k copies of A and one of B, marginalizing the other two species from the complete rooted labelled genealogy. The event that all k A copies form a clade has probability

    E[g_k(X)],
    g_k(x) = sum_{j=1}^k P_(k,j)(x) 2/(j(j+1)).

Indeed, j surviving A ancestors form an A-only clade after meeting B precisely when every A-only merger happens before any merger with B. That probability is

    product_{l=2}^j binom(l,2)/binom(l+1,2) = 2/(j(j+1)).

The coefficient c_k of x^lambda_k in g_k is nonzero:

    c_2=-2/3,
    c_k=(-1)^(k-1) 2 / ((k-1) binom(2k-2,k-1)), k>=3.

Consequently, with k=M+1 the observed clade-probability difference is exactly

    c_(M+1) A^lambda_(M+1) t H(a_(M+1)),

which is nonzero. With at least one sample from each of the four original taxa, this test uses M+4 total copies: M+1 from A and one each from B,C,D. The C,D deletion is an observation coarsening, not a change to the four-taxon source promise.

This establishes observable separation, not merely a difference in a hidden no-merger coordinate.

### 1.4 Why the leading coefficient is nonzero

For completeness, the coefficient of x^lambda_k in P_(k,j) is

    (-1)^(k-j) k!(k-1)!(k+j-2)! /
      (j!(j-1)!(k-j)!(2k-2)!).

Multiply by 2/(j(j+1)) and sum. Write n=k-1 and use the explicit shifted Legendre polynomial

    Q_n(u)=sum_{j=0}^n (-1)^j binom(n,j)binom(n+j,j)u^j.

The resulting sum, including its normalization, is

    c_(n+1) = (-1)^n [2(n+1)/binom(2n,n)]
              * integral_0^1 Q_n(u)[-log(u)-(1-u)]du.

For n>=2, the integral against 1-u vanishes. This follows directly from the finite Rodrigues formula, or by integrating its coefficient identity. The polynomial satisfies

    (u(1-u)Q'_n(u))' + n(n+1)Q_n(u)=0,
    Q_n(0)=1,  integral_0^1 Q_n(u)du=0.

Multiply by -log(u) and integrate by parts. The boundary terms vanish and the remaining integral is -integral(1-u)Q'_n = 1. Hence the logarithmic integral equals 1/(n(n+1)). Substitution gives the displayed c_k. The k=2 case is direct. All ingredients are finite polynomial identities plus an elementary integral; the executed checks verify c_k for k=2,...,24.

## 2. Independent inheritance: exact collisions exist after every finite cap too

A common-chain moment construction must not be relabelled as an independent-inheritance result. The independent proof uses the full capped kernel, not only its pair coordinate.

**Theorem B.** For every finite M there are two actual finite positive independent-inheritance serial chains with identical complete labelled forest kernels through M but different kernels at a finite larger cap. They can be placed on the same four-species pendant branch and separated by a rooted gene-topology event. There is a terminating, although potentially enormous, exact real-algebraic construction of such a pair.

### 2.1 Arbitrarily many independent higher-copy directions

The no-merger probability of one independent bigon is

    b_k(x,y,g)=sum_{j=0}^k binom(k,j)g^j(1-g)^(k-j)
                              x^binom(j,2)y^binom(k-j,2).

At the algebraic boundary x=0,y=1,

    b_k=(1-g)^(k-1)(1+(k-1)g),
    partial_g log b_k = -k(k-1)/((1-g)(k-1+1/g)).

For d serial factors with distinct interior g_i, the Jacobian of log no-merger probabilities at k=2,...,d+1 is a Cauchy matrix, multiplied by nonzero row and column factors. Its determinant is nonzero because the k-1 and 1/g_i values are distinct.

The probabilities are polynomials and positive at these interior g_i. The nonzero Jacobian persists for strictly positive x close enough to zero and y below but close enough to one. Positive leading and connecting edges multiply the coordinates by positive factors independent of g and preserve the rank. Thus the rank statement occurs at genuine positive sources, not only at a forbidden limiting edge.

This source-Cauchy ingredient was already developed in G3 INTERIOR.md. Its use here is different: it constructs two finite exact capped-equality sources and an authorized higher-copy separating test.

### 2.2 Full-kernel fibers, not an approximate fit

Let J_M be the full capped forest-coordinate count from PROOF.md, and take d=J_M+1 factors. Fix positive rational arm and connector survivals at which the preceding d by d Jacobian is nonzero. Such values can be found by enumerating x=1/N, y=1-1/N and testing the exact determinant at distinct rational g_i.

Let P(g) be the COMPLETE capped forest tuple through M, a polynomial map from (0,1)^d into R^J_M. Let B(g) be the d-vector of higher no-merger coordinates k=2,...,d+1. Around a point where B has full rank, B is locally injective.

Inside that neighborhood choose a point where P has its maximal local rank s. In a smaller neighborhood the rank is constant, with s <= J_M < d. The constant-rank theorem gives positive-dimensional local fibers of P. Choose two distinct points g,g' on such a fiber. They have the same full P, but B(g) != B(g') because B is locally injective. All parameters remain strictly interior.

This is exact fiber equality, not density, convergence, a parameter-count guess or a claim that every abstract kernel is source-realizable.

For effectivity, form the finite rational polynomial system

    0<g_i,g'_i<1,
    P(g)=P(g'),
    sum_k (B_k(g)-B_k(g'))^2 > 0.

It is nonempty by the preceding proof. Real-closed-field decision produces a real-algebraic witness. This construction can be infeasibly large, but every step is finite and the existence proof guarantees that the satisfiable branch is reached. This manuscript does not report executing that general quantifier-elimination construction.

### 2.3 An observed independent-inheritance witness

Place either chain on pendant A in ((A,B),(C,D)). Let k be a no-merger coordinate where they differ. Sample k copies of A, k copies of B, and one each of C,D. After restricting to A,B, choose a fixed rooted binary topology whose cherries are exactly (A_i,B_i).

Any A-only merger before A and B populations meet is incompatible with this topology; so is any B-only merger. Conditional on no such merger, all 2k lineages enter a common ancestral population and have the ordinary Kingman topology law. Therefore the probability of the selected rooted topology is

    positive_rational_constant * (B-pendant survival)^lambda_k * b_k(chain).

It differs for the two sources. This is a finite observed rooted gene-topology event, with at most 2d+4 total copies in the construction above. The distinct displayed species-tree target remains unchanged.

## 3. Consequences: what is refuted and what is not

**Corollary C.** Separately for common and independent inheritance, no finite copy cutoff depending only on the taxon count can certify equality of all-copy completion responses over the entire admitted finite source class. More generally, no fixed finite collection of finite-copy completion tests is complete for all-copy equivalence: take the largest copy budget in that collection and apply Theorem A or B.

Equivalently, the finite-cap stopping theorem in PROOF.md cannot be run once at a fixed taxon-only cap and called an all-cap decision. The counterexamples have four taxa, positive finite lengths, interior inheritance, exact equality below the cap and genuine observed separation later.

This does **not** prove that every source-dependent adaptive all-cap algorithm is impossible. Such an algorithm may choose its cap using a supplied source description or a separately justified finite-rank certificate. Nor does it give an opposite-target collision for Q/S.

There is also no fixed finite-dimensional linear interface for all capped ordinary-edge kernels simultaneously: for any d distinct positive survivals, the generalized Vandermonde matrix at d sparse exponents has full rank. This is an infinite-span obstruction. It is not an obstruction to a nonlinear one-parameter description of one ordinary edge.

## 4. A complete supplied-common-chain all-cap decision

**Theorem D.** For two supplied finite common-inheritance two-port chains, their all-cap forest kernels agree if and only if their finite total-survival distributions agree, including atom weights. With algebraic survival and inheritance parameters, this is a terminating exact algorithm.

**Proof.** Enumerate the finitely many common hybrid choices, multiply their independent weights, multiply selected edge survivals, and merge equal survival atoms exactly. Equality of the resulting finite atomic distributions implies all moments and all forest kernels agree.

Conversely, let the union of the two atom supports have at most s+t points. Equality of the first s+t sparse moments, including the constant moment, gives a homogeneous generalized Vandermonde system for the signed difference of atom weights. It is nonsingular on distinct positive atom locations. One proof is Descartes' sign rule: a nonzero combination of k increasing monomials has at most k-1 positive zeros. Hence all signed weights vanish. QED.

Every needed sparse moment is an actual no-merger kernel coordinate. The A-clade observations in Section 1.3 recover them successively by the nonzero triangular coefficients. Thus this is also an all-cap contextual comparison for the common two-port type, with legal finite exterior witnesses, not an assumption that hidden coordinates can be read directly.

### A supplied reference against an unknown-size common chain

If the supplied reference survival law has s interior atoms, its first 2s+1 sparse moments determine it among **all probability measures on [0,1]**, not just among known-size finite chains. To see this, choose a nonzero polynomial in the 2s+1 corresponding monomials with a double zero at each atom. Descartes' rule forces those to be its only positive zeros, forces a nonzero constant coefficient, and lets its sign be chosen nonnegative on [0,1]. Matching the moments forces any competitor to be supported on those atoms; generalized Vandermonde uniqueness fixes the weights.

This supplies a source-dependent finite certificate against arbitrary common-chain sizes. With the four-taxon A-clade wrapper, interface cap 2s+1 corresponds to at most 2s+4 total sampled copies. It is consistent with Corollary C because s is not bounded by the taxon count.

The proof uses common inheritance essentially. Under independent inheritance, treating a chain as a finite mixture of ordinary selected durations changes the model.

### An unknown finite common chain: an adaptive all-cap stopping rule

**Theorem D2.** Suppose exact algebraic A-clade response access is supplied, with the promise that the responses come from some finite positive common two-port chain, whose size and parameters are not supplied. Its complete all-cap forest law can be recovered with a terminating adaptive exact procedure. The same holds for a finite authorized menu of common-chain marginal response rows, including finite randomized forcing programs.

First recover successive sparse moments by the nonzero triangular A-clade formula. At stage M decide the following finite real-algebraic formula for c_1,...,c_M:

    sum_i c_i^2 = 1,
    p(x)=sum_(i=1)^M c_i x^lambda_i >= 0 for every x in [0,1],
    sum_(i=1)^M c_i mu_i = 0.

Quantifier elimination over the real algebraic coefficient field decides the formula; on SAT it supplies algebraic coefficients. The unit-norm condition excludes the zero polynomial. A nonzero polynomial has finitely many roots, so every probability measure matching the moments must be supported on its finitely many roots in [0,1]. Descartes' bound gives at most M-1 strictly positive roots; allowing zero gives at most M possible atoms. The corresponding generalized Vandermonde matrix (including the constant coordinate, also when zero is an atom) has full column rank. Solve for the unique nonnegative weights and remove zero-weight roots. The true promised measure supplies existence, so an inconsistent weight system is an input-promise failure, not an alternative accepted source.

If the unknown common chain has s distinct survival atoms, its exposing polynomial from the preceding subsection exists by M=2s+1. Thus the loop MUST stop, without assuming a known bound on s. The returned finite atom law then determines every forest kernel. The real-algebraic searches can be enormous; this is an effective mathematical procedure, not a claim of an implemented general quantifier-elimination driver.

For a finite menu, every authorized common-chain row is a finite duration mixture after conditioning on the finite joint forcing configuration and natural common coins. Apply the procedure to each authorized marginal row; all finitely many searches terminate. Original row/ID labels remain attached, and the source promise retains one shared original source. This is not a sufficiency test for arbitrary proposed multirow profiles or for unobserved joint counterfactual responses.

The positive one-atom certificate is p(x)=(x-a)^2(x+2a)=x^3-3a^2 x+2a^3, with a=mu_2. Its expectation is mu_3-mu_2^3, giving a three-copy interface stop when that value is exactly zero. The code checks one- and two-atom exposing certificates, but does not report running the general existential/universal solver.

This establishes a stronger common-chain stopping branch than a supplied-size comparison. It does not transfer to independent inheritance, where a finite mixture of ordinary Kingman durations is generally not the source law.

## 5. Fixed source shapes: finite all-cap determination exists, but a plateau is not an algorithm

**Theorem E (nonconstructive finite-shape bound).** Fix two finite source graph shapes, their mode contracts, a finite original-ID menu, and the finite topology observation maps at each sampling allocation. There exists a finite copy cap, depending on those supplied shapes, such that equality through that cap implies equality at every cap, for all fixed positive parameter assignments on the two shapes.

**Proof.** For every finite allocation/outcome/row, the probability difference is a polynomial in the finite lists of survival and inheritance variables for the two source shapes. Its coefficients are rational for deterministic observation maps and rational program weights; more generally work over the field generated by the fixed observation-channel/program coefficients. Shared original parameters remain the same variables at every cap and row. The ideal generated by all these polynomials in the finite-variable polynomial ring is finitely generated. Its generators can be selected from a finite subset of the original differences: any finite ideal generating set uses only finitely many members of the original generating family. Choose a cap containing that subset. Vanishing of all differences through that cap then forces every difference to vanish. QED.

This is a direct use of the Hilbert basis theorem, not a new source recognition algorithm. With a finite graph-size budget, the finite number of shapes gives a finite uniform cap for that budget as an existence statement.

**Effectivity warning.** Enumerating caps, computing Groebner bases and seeing I_M=I_(M+1) does not prove that a later cap adds no new generator. Finite generation of a recursively presented ideal does not by itself provide a computable stopping index. No general source-generated closure rule for the unbounded-copy independent-inheritance polynomial family has been established in this packet.

The finite-cap algorithm in PROOF.md has a different certificate: it explicitly checks invariance under a finite, exhaustively justified generator family. That certificate must not be replaced by this nonconstructive argument.

## 6. Numerical access is a different obstruction

Even at a fixed small cap and a fixed ordinary positive source shape, an ordinary Cauchy-name oracle for real probabilities/parameters cannot support a universally terminating exact equality test. Fix x_0=1/2. Given a program, let x=x_0 if it never halts, and x=x_0+2^(-s-3) if it first halts at stage s. This is a uniformly computable real in a compact positive interval: to answer a precision request, simulate only finitely many stages; a later change is below that precision.

A pendant ordinary edge with survival x has a rooted A-clade probability affine in x at two A copies and one B outgroup. Comparing that response exactly with the x_0 response would decide nonhalting. Each realized parameter is rational, but its finite rational encoding was not supplied; the Cauchy-name input contract matters.

This does not obstruct exact rational/algebraic arithmetic on explicitly supplied finite encodings. It is not a statistical error bound and not a substitute for the all-cap source-specific question in Section 5.

## 7. Executed evidence and honest residual

Executed in adversarial_checks.py:

- Explicit common collision constructions for M=2,...,8, with exact rational endpoint inequalities and Sturm isolation of every perturbed inheritance root.
- Full labelled forest-coordinate equality reconstructions through caps 2,...,5, not merely lineage-count equality.
- An exact rational independent cap-2 collision with cap-3 no-merger difference -1/4096.
- Eight independent Cauchy determinant checks and a strictly positive dimension-four perturbation check.
- Twenty-three nonzero observed A-clade leading-coefficient identities through k=24.

The all-size independent collision construction is a hand proof with a terminating real-algebraic search, not an executed all-cap source census. The general source-dependent all-cap stopping algorithm for arbitrary independent-inheritance sources remains an explicit unproved endpoint. No finite span plateau, finite test suite or common-chain atomic argument in this packet is claimed to settle it.
