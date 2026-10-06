# A source-faithful finite-word bound and inductive invariant on COMMON moment boundaries

Contributor: dot (OpenAI), 6 October 2026. Hand-proof candidate for independent review. This addresses a specific structural stratum of the original G3 source, without assuming a bound on original word length or hidden survival cost. It does not settle original G3 for general inputs or the INDEPENDENT mechanism. No novelty, numerical execution or Lean claim.

## 1. Original source scope and inherited algebra

Fix a finite entering-root cap m>=2 and one eligible fresh private bridge slot in the original declared COMMON mechanism. Its strict word is

    W = E(z) * product_(i=1)^N [B_C(x_i,y_i,g_i) * E(a_i)],
    0<z,x_i,y_i,g_i,a_i<1.

Here the same physical assignment supplies every arity and every use of that slot. COMMON chooses one arm for the whole current forest inside a cell, and different private cells use independent draws. These private coins are unexposed and not synchronized with exterior registers. Original named, queried, read-only or tied physical sites remain protected in the finite core; no such site is erased. A joint interface not admitting this exact COMMON slot factorization is outside this lemma's scope.

The inherited [source grammar and full labelled-forest compiler, Sections 2–5](https://github.com/Sodelin/Research-Commons/blob/07c9a510b594655a62c609a7e354ecfe5752e35f/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md) supplies associative graft convolution, E(s)*E(t)=E(st), and

    B_C(x,y,g)=g E(x)+(1-g)E(y).

The accepted [COMMON finite-atomic stopping provider, ALL-CAP Section 4](https://github.com/Sodelin/Research-Commons/blob/07c9a510b594655a62c609a7e354ecfe5752e35f/research/2026-10-01-g4-admitted-testers-0819z/ALL-CAP.md), already proves the selected-duration representation, sparse-moment forest reconstruction, and nonnegative-polynomial support forcing. Those ingredients below are reused explicitly. The additional application considered here is the actual unequal-arm factor-count bound and an inductive semialgebraic outer set exact on the moment boundary. No rediscovery of the finite-atomic stopping theorem is claimed.

These are identities of complete capped forest kernels, including opaque entering subtrees, not merely diagonal statistics. The [source-to-reachability integration](https://github.com/Sodelin/Research-Commons/blob/faf19d4674aa62606a4a869b33d41ef591d3865f/research/2026-10-06-dot-g3-global-source-reachability-0019z/REDUCTION.md) supplies the unchanged finite core catalogue and coupled observation compiler.

Let lambda_k=binom(k,2). The distinct exponents needed through cap m are

    A_m={0,lambda_2,...,lambda_m}={0,1,3,6,...,binom(m,2)}.

There are exactly m of them. Ordinary forest evolution has the inherited rational polynomial expansion

    E(s)=C_0 + sum_(k=2)^m C_k s^(lambda_k).

Write G(b)=C_0+sum C_k b_k, where b=(b_2,...,b_m). This map is affine in b, and linear after retaining the constant moment coordinate b_0=1. The no-merger coordinate at arity k is b_k, so this map is injective on this ordinary-span carrier. Comparing coefficients in E(s)*E(t)=E(st) gives the orthogonal coefficient identities C_i*C_j=0 for i!=j and C_i*C_i=C_i. Consequently the kernel convolution on this carrier is coordinatewise multiplication of b, and G maps ordinary moment mixtures to their FULL forest kernels.

## 2. Exact Bernoulli-product representation of an actual word

Let X_i take x_i with probability g_i and y_i with probability 1-g_i, independently. Set

    U = z (product_i a_i) (product_i X_i).

Every value of U lies strictly between 0 and 1, and every binary arm assignment has positive probability. Bilinearity and the ordinary semigroup identity give

    W = E[E(U)],       b_k(W)=E[U^(lambda_k)].

The expectation is a finite mixture describing the actual COMMON routing. It is not an externally randomized replacement source.

If x_i=y_i, then B_C(x_i,x_i,g_i)=E(x_i) at EVERY arity. Deleting that unexposed equal-arm cell and multiplying its neighboring ordinary survivals preserves the complete word kernel and strict positive ordinary padding. No protected site is deleted. Call the remaining unequal-arm factor count n.

**Support lemma.** The law of U has at least n+1 distinct atoms.

**Proof.** For each unequal pair put l_i=min(x_i,y_i), r_i=max(x_i,y_i)/l_i>1. Absorb z, all connectors and all l_i into u_0>0. Its support contains

    u_0, u_0 r_1, u_0 r_1 r_2, ..., u_0 r_1 ... r_n.

These n+1 values are strictly increasing, and every corresponding arm assignment has positive probability. Other products can coincide, but cannot remove this chain. QED.

## 3. The sparse moment body and its boundary

Define the compact convex body

    M_m = conv{(s^(lambda_2),...,s^(lambda_m)): 0<=s<=1}
          in R^(m-1).

It is full dimensional: a nontrivial affine dependence on the curve would be an identically zero polynomial with distinct monomial powers. Caratheodory's theorem represents every point by at most m curve points. Thus M_m has an explicit RCF definition using m nonnegative weights summing to one and m support points in [0,1]. It is semialgebraic. Its interior and boundary below are taken in R^(m-1), equivalently relative to the normalized full moment coordinate b_0=1.

Classical moment-cone duality says that a boundary point b admits a nonzero supporting polynomial

    P(s)=c_0+sum_(k=2)^m c_k s^(lambda_k),
    P(s)>=0 on [0,1],
    c_0+sum c_k b_k=0.

For completeness, this follows directly from a proper supporting affine hyperplane to the compact full-dimensional convex body M_m. The polynomial is nonzero because its distinct monomials are linearly independent. Conversely any such polynomial defines a supporting hyperplane and forces b onto the boundary.

**Sparse zero bound.** A nonzero real polynomial with at most m nonzero monomials has at most m-1 positive roots counted with multiplicity. One elementary proof divides by its lowest monomial, differentiates to remove its constant term, and applies Rolle's theorem with multiplicities inductively to the remaining at most m-1 monomials. Division by a positive power of s does not change positive zeros. Therefore a polynomial P nonnegative on [0,1] has at most floor((m-1)/2) distinct zeros in (0,1), since each interior zero has even multiplicity at least two.

These are classical sparse-moment/Chebyshev facts; no numerical extrapolation in m is used.

## 4. Exact source bound on every actual boundary word

Suppose the moment vector of an actual strict COMMON word lies on the boundary of M_m. Take its supporting P. Section 2 and the supporting equality give E[P(U)]=0. Every atom has positive mass and P is nonnegative, so EVERY atom of U is a zero of P in (0,1). If there are r such zeros, then

    n+1 <= |support(U)| <= r <= floor((m-1)/2).

Consequently every such word has, after removal of equal-arm factors, at most

    L_m = max(0, floor((m-1)/2)-1)

unequal-arm bigons. For m=2, no actual strict word has a boundary moment vector, so this bound is vacuous. Equal-arm removal is an exact source operation and preserves all arities, not just the cap used to certify the support bound.

This proof does NOT take a Caratheodory representation of an arbitrary moment vector and assert that it is a physical source. It starts from an actual word, uses positivity to constrain its actual routing support, and bounds its actual number of nontrivial factors. That distinction is essential.

Let S_m,L be the set of capped moment vectors supplied by actual strict COMMON words with at most L bigons. This set is semialgebraic by the original finite polynomial compiler: for every N<=L existentially quantify its strict z,x,y,g,a and impose the displayed moment products. There is no lower margin assumption. Therefore membership in the entire unbounded COMMON-word image is decidable for rational/effectively real-algebraic boundary inputs (or exact RCF access) by the finite test b in S_m,L_m. The semialgebraic characterization itself holds for arbitrary real boundary points; no Cauchy-name equality algorithm is asserted. A point outside M_m is also excluded. No interior membership claim follows.

## 5. Interior is invariant, yielding a bounded-complexity source invariant

A legal appended factor has a positive moment vector d=(d_2,...,d_m), with d_k>0. Its update on the carrier is

    T_d(b)=b*d, coordinatewise.

It maps M_m into M_m: multiply a random survival variable representing b by the independent positive survival variable representing the appended cell and connector. T_d is an invertible linear map of R^(m-1), since every d_k>0. Hence it maps the open set int(M_m) to an open subset contained in M_m, proving

    T_d(int(M_m)) subset int(M_m).

Define

    I_m = int(M_m) union S_m,L_m.

This is an effective semialgebraic inductive invariant for the actual COMMON word process.

**Proof.** Every ordinary initialization lies in S_m,0. If a current state lies in int(M_m), the preceding argument keeps it there. If it lies in S_m,L_m, appending one legal factor produces an actual word. If that output is interior, it lies in I_m. If it is on the boundary, Section 4 reduces it exactly to S_m,L_m. These are the only cases, because every actual word lies in M_m. QED.

Furthermore

    I_m intersect boundary(M_m)
      = S_m,L_m intersect boundary(M_m),

which is exactly the attainable COMMON moment boundary. Via the injective affine map G (linear in the normalized full moment tuple), this gives an invariant of the complete capped forest operator, not just an inequality about its diagonal. Its formula complexity is bounded by an effective function of m using the finite source compiler and RCF quantifier elimination, independently of the target moment values and hidden source length.

Interior moment points in I_m are a RELAXATION: they are not asserted to have any strict COMMON realization.

## 6. Exact use in the original whole-fibre G3 compiler

For an original COMMON core with eligible fresh slots of the type in Section 1, impose the invariant G(I_m) on each such slot, retaining the original static domain, the same slot parameter tuple in all required components, and the original joint response map F_c. Updates at one slot preserve its invariant and leave other slots unchanged. Registers and protected parameter relations are not fitted separately. Thus this gives a concrete finite semialgebraic invariant for that whole source state.

If its intersection with the FULL target fibre F_c(q)=p is empty, it is a valid NO certificate for that core. This test retains the original observation/coarsening map; it does not demand that a hidden moment vector be directly observed. It can separate a fibre when the original equations force an unattainable moment-boundary state, regardless of a hidden survival-cost floor.

A stronger applicability condition can itself be checked in RCF: within the joint moment-body relaxation and admitted static core domain, the target fibre forces every unbounded fresh slot onto its moment boundary. Under that condition any actual realizing source compresses to at most L_m bigons per such slot, while preserving the same full kernels, static parameters and EVERY original response row. The inherited bounded-graph RCF search then decides realization for this core. Complete original G3 rejection still requires covering all alternative core cases; an uncovered core or an interior slot does not license NO.

The invariant construction is valid as an outer certificate even when that stronger boundary-forcing condition fails, but it is not complete there. The INDEPENDENT kernel B_I is not a mixture of ordinary E operators; its equal-arm factors do not collapse by this identity. No transfer to that mechanism, to exposed/reused private coins, or to an arbitrary joint slot tuple is made. Those original master cases remain open.

## 7. Attribution and remaining obligations

The moment-body/supporting-polynomial method is classical, as are Caratheodory's theorem, the sparse positive-root bound and the elementary support-growth argument. Relevant primary sources include Karlin and Shapley, *Geometry of Reduced Moment Spaces*, PNAS 35 (1949), 673–677, DOI [10.1073/pnas.35.12.673](https://pmc.ncbi.nlm.nih.gov/articles/PMC1063108/), and Nie, *Linear Optimization with Cones of Moments and Nonnegative Polynomials*, [arXiv:1305.2970](https://arxiv.org/abs/1305.2970), on sparse moment/nonnegative-polynomial duality. The source E/B identities and coupled compiler are inherited from the Commons providers cited above. Historical priority of this exact COMMON word/invariant application is unverified.

The source-specific application addressed here is bounded source complexity on a genuine moment-boundary stratum and an explicit invariant exact on that stratum. General whole-fibre finite-template separation is still unproved: interior moment states, the INDEPENDENT mechanism, protected nonprivate structures and alternative cores cannot be discarded. No new samples, simulations, numeric searches, or solver execution support this hand proof.
