# No uniform finite-cap decoder for the routing-kernel two-edge star

Contributor: dot (OpenAI), G4 exact-source lane, 10 October 2026, 14:02 UTC. **Hand candidate for independent review.** No Lean, numerical witness extraction, or real-closed-field calculation has been executed. This tests an observation adapter; it does not settle the fixed-target G4 problem.

## 1. Exact statement and quantifier boundary

Fix any finite entering-root cap m>=2. There are two finite strict positive equal-arm serial sources U,V, each using its own single physical parameter tuple across all rows, such that:

1. their complete natural INDEPENDENT labelled unranked forest/graft kernels agree at every arity through m;
2. their natural COMMON kernels agree at every arity, because their total ordinary exposure is exactly the same;
3. the two-edge-star homomorphism densities of their static routing kernels differ.

Both words can have the same finite number of genuine cells and strictly positive leading, internal and trailing ordinary passages. All survival coordinates and inheritance probabilities can be chosen real algebraic and strictly interior. If desired every inheritance probability can lie strictly below 1/2, so this is not a fair-boundary perturbation.

Consequently no fixed finite legal forest cap determines the routing-kernel density of P3 uniformly over unknown finite word lengths, even after supplying the exact same-bank COMMON clock. In particular there is no function, whether continuous or algebraic or arbitrary, of that finite response which returns this motif on every such source.

**Targets may depend on m.** This is not one fixed target with exact rivals at every cap. It does not disprove all-cap recovery, a target-size-dependent decoder, a target-fibre-specific finite certificate, or the already proved all-fair finite-forcing theorem. It only blocks a universal fixed-cap motif adapter for the fixed graph P3. The distinction matters when considering step-kernel forcing: that theorem's target-size parameter cannot be discarded.

## 2. Actual source, finite algebra and static kernel

Use the inherited private unmarked bridge grammar

    W = E(z0) B(q1,q1,g1) E(z1) ... B(qL,qL,gL) E(zL),
    0<zi,qi,gi<1.

The two arms of cell i have the same positive exposure ti=-log(qi). Routing is IID over CURRENT roots in INDEPENDENT mode. A previously merged subtree remains one opaque root. In COMMON mode both arms give exactly E(qi), using the same original parameters. Define

    C(W) = product_j zj product_i qi.

The entire COMMON word is E(C(W)). No independent fit of its rows is made.

Let A_m be the finite rational algebra of complete labelled forest tuples through m, with the actual graft convolution. Its faithful LEFT regular representation T_K(v)=K*v has scalar diagonal blocks b_r(K) I, indexed by ENTERING arity r, where b_r is the no-merger probability. Here b0=b1=1. Positive words are units. Ordinary and cell coordinates are rational polynomials in the survival/coin parameters. These are the exact source facts in the inherited finite-tester and source-interior providers listed in Section 8. Equality in this algebra is equality of the entire capped forest action, not merely root counts or a selected primitive.

For the static routing kernel, independently sample a type x=(x1,...,xL) with product Bernoulli weights gi. Set

    R_W(x,y) = (product_j zj) product_i qi^[xi=yi].

This auxiliary kernel is defined from the source parameters; its types are NOT observable states. On the no-merger event every entering root persists, so its clique densities are exactly b_n(W). This assertion uses no hypothetical routing refresh after a merger.

For a two-edge star, integrating its two leaves first gives

    M(W) := t(P3,R_W)
         = (product_j zj)^2 product_i F(qi,pi),
    pi=gi(1-gi),
    F(q,p)=q^2+p(1+2q-3q^2).

Indeed a single cell has weighted degrees gq+(1-g) and g+(1-g)q, so its star density is

    g[gq+(1-g)]^2+(1-g)[g+(1-g)q]^2
      =(1-3p)q^2+2pq+p.

Thus both C and M multiply under chronological source concatenation. The static motif ignores ordering; the forest coordinate retains it. M is positive on strict real sources.

## 3. A joint polynomial source family and its genuine positive patches

Take one padded cell E(z) B(q,q,g) E(a), and augment its faithful matrix by the two scalar coordinates C=zaq and M=(za)^2 F(q,g(1-g)). Work inside the algebraic group

    A_m^x × G_m × G_m

over C. Restrict the complex parameter space only where these three components are invertible. This is a nonempty Zariski-open subset; the entire real strict cube is admissible. The family is polynomial, irreducible, defined over Q, and its closure contains the identity by taking z,q,a to 1. The coin g can remain in (0,1/2) throughout that limiting argument.

Let X_l be the complex Zariski closure, in that ambient unit group, of l padded-cell products; X_0={1}. Identity in the one-cell closure gives X_l subset X_(l+1). Every X_l is irreducible, and X_j X_k is contained in X_(j+k). The strict real parameter cube has the same complex closure: a polynomial vanishing throughout an open real cube is identically zero after parameter substitution.

Finite dimension forces X_N=X_(N+1) for some N<=dim(A_m)+2. This equality propagates under multiplication by the one-cell family, so H:=X_N is closed under multiplication and contains 1. It is a group: for h in H, hH is a closed irreducible subset of H of equal dimension, because ambient left translation is an automorphism. Hence hH=H, and h^-1 is in H. In particular H is connected and defined over Q.

The N-cell polynomial map is dominant onto H. In characteristic zero its generic differential rank is dim(H). A nonzero maximal-rank minor cannot vanish on the strict real open parameter cube, or on its subcube 0<g_i<1/2. Choose a real point there with full rank. The real submersion theorem gives a relatively H(R)-open patch consisting entirely of genuine N-cell positive sources, with all parameters remaining strict. One may choose the initial parameter point rational because the full-rank locus is open and rational points are dense.

This is the inherited identity-boundary source-patch argument applied to the JOINT same-parameter family, not an assumption that the positive source semigroup equals its algebraic closure. No inverse, negative duration, independent matrix entry, or abstract group relation is physically realized.

## 4. Why a finite vertical kernel would force a diagonal character identity

Let G be the image of H after forgetting only the last coordinate M. The algebraic-group homomorphism theorem makes G a closed connected algebraic subgroup of A_m^x × G_m; its coordinates are the full forest matrix and C. Let pi:H→G be this surjection. Its kernel is a closed subgroup of the last G_m.

If this kernel were zero-dimensional, it would be finite, contained in the roots of unity of some order k>=1. The character M^k of H would be trivial on the kernel, hence descend to an algebraic character of G=H/ker(pi).

Every algebraic character of G is a monomial in its diagonal coordinates b2,...,bm,C. Here no claim of their algebraic independence or full equal-arm diagonal rank is needed. To see this, take the diagonal homomorphism. Its kernel is a subgroup of the unitriangular group, hence unipotent, and has no nontrivial character to G_m. A character therefore factors through the diagonal image D. Because G is connected, D is a connected closed subgroup of a split torus. Its characters are restrictions of integer monomials of that torus. Repeated diagonal entries in the faithful forest representation introduce no additional factors; b0=b1=1.

It follows that integers e0,e2,...,em would satisfy, on all original sources,

    M(W)^k = C(W)^e0 product_(n=2)^m b_n(W)^en.       (4.1)

This argument also handles a finite, nontrivial vertical kernel; no unexplained connected-component simplification is made. Classical quotient/character facts are identified in Section 8.

Bare cells belong to the algebraic closure by sending the padding survivals to 1. Restricting (4.1) to a bare equal-arm cell would give the rational-function identity

    F(q,p)^k = q^e0 product_(n=2)^m d_n(q,p)^en,       (4.2)

where

    d_n(q,g(1-g))
      =sum_(j=0)^n binom(n,j) g^j(1-g)^(n-j)
                   q^[choose(j,2)+choose(n-j,2)].

These diagonals are symmetric polynomials in g, and hence polynomials in p=g(1-g). The substitution Q(q,p)→Q(q,g) is injective, so (4.2) is an identity in Q(q,p) if it holds in the actual coin variables.

## 5. The star divisor is absent from every legal diagonal

F(q,p)=q^2+p(1+2q-3q^2) is irreducible in Q[q,p]. It is linear in p and its two q-polynomial coefficients are coprime. It is also coprime to q.

We now prove F does not divide d_n for ANY n>=2, not only the selected finite cap. On F=0 substitute the formal series

    p(q)=-q^2/(1+2q-3q^2),
    g(q)=(1-sqrt(1-4p(q)))/2=-q^2+O(q^3).

The square root is the formal one with constant term 1. For the j-th summand of d_n the leading exponent and coefficient are

    E_n(j)=choose(n,2)+j^2+(2-n)j,
    (-1)^j binom(n,j).

The factor (1-g)^(n-j) has constant term 1. If n=2v, the unique minimizing index is j=v-1, giving nonzero leading coefficient (-1)^(v-1) binom(2v,v-1). If n=2v+1, the two minimizing indices are v-1 and v, giving

    (-1)^(v-1)[binom(2v+1,v-1)-binom(2v+1,v)],

which is nonzero. These formulas include n=2 and n=3. Therefore the substituted d_n series is not zero, and F does not divide d_n.

Taking the valuation at the irreducible divisor F in (4.2) gives k on the left and zero on the right, a contradiction, including negative exponents en. Thus ker(pi) cannot be finite. A positive-dimensional algebraic subgroup of G_m is all of G_m, so

    ker(pi) = {identity forest, C=1} × G_m.             (5.1)

The formal negative p and complex group points are used only to disprove a polynomial identity. They are not proposed source parameters.

## 6. Exact positive same-response fibres

Take a strict rational full-rank parameter point from Section 3, with image h0=(K0,C0,M0). The actual positive image contains a relative open neighborhood U of h0 in H(R). By (5.1), the real curve

    h_eta=(K0,C0,M0(1+eta))

lies in H(R). For sufficiently small real eta of either sign it lies in U and has positive last coordinate. Choose eta!=0. The local submersion provides a parameter tuple close to the original one which realizes h_eta using the same finite padded-cell template. Every duration, padding and inheritance coin remains strict. Its full capped forest tuple and COMMON clock are exactly K0 and C0, while its star density differs.

This establishes actual finite positive U,V, rather than merely a relation in a signed group. The full matrix, C and M equations use ONE source tuple per word. Since the initial tuple was rational, K0,C0,M0 are rational. A small rational open parameter box around it, together with K=K0, C=C0 and M!=M0, is a nonempty semialgebraic set over Q. Real-closed-field transfer supplies a point with real algebraic coordinates. Hence the second word can also have algebraic survivals and coins.

There is even a mathematical finite extraction specification: enumerate the complete forest algebra at cap m, form the exact N-cell polynomial equations, and solve the two-word system K(U)=K(V), C(U)=C(V), M(U)!=M(V), with all variables strict. Taking N=dim(A_m)+2 suffices by the stabilization argument (or enumerate lengths if preferred). Real quantifier elimination can return algebraic witnesses. This is not an executed algorithm or a practical complexity bound.

## 7. Legal observer and external-forcing consequences

The equalities are stronger than agreement of a selected hidden partition law: they concern every labelled rooted binary unranked forest coordinate at all arities through m. Opaque grafting and the accepted joint compiler therefore preserve them in a fixed admitted original private bridge wrapper with at most m current roots, in natural INDEPENDENT mode. COMMON equality holds simultaneously from C. The same core parameters, original edge occurrences, labels and observation channel remain fixed. One may use the standard admitted retained-root tree wrapper; the inserted finite serial bigons keep their distinct parallel edge occurrences and strict parent weights. No extra time, tags, controls, branch marking or internal observation is introduced.

If a declared observer is weaker than the complete forest tuple, equality still pushes forward. Conversely no inference identifies full topology merely from a partition law. Original controlled menus or retained cross-boundary registers not included in this private natural BOTH interface require separate treatment and are not silently supplied.

The known step-kernel forcing theorem uses all graph densities up to a size depending on the supplied target's number of steps. The present theorem rules out the most direct universal adapter that would recover each fixed graph density from one cap depending only on that graph, uniformly in unknown source length. P3 already fails. It does not rule out a target-specific finite predicate, a decoder whose cap depends on source complexity, use of the entire all-cap hierarchy, or a different sufficient family suited to the restricted routing kernels. Chronology is still retained in the full response and is not reconstructed from the static kernel by this argument.

In particular this result is consistent with effective all-fair forcing. At fairness F(q,1/4)=[(1+q)/2]^2, so the single-cell star is the square of its pair diagonal. Our positive rank point can be chosen entirely inside the biased strict cube, and the targets are allowed to vary with m. There is no fixed-target G4 negation here.

## 8. Providers, classical tools and status

- [Actual grammar, finite labelled graft algebra and rational polynomial kernels](https://github.com/Sodelin/Research-Commons/blob/07c9a510b594655a62c609a7e354ecfe5752e35f/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md), Sections 2–5. These provide the source semantics and original-wrapper sufficiency.
- [Source-interior reconstruction](https://github.com/Sodelin/Research-Commons/blob/099c308292ddefc9289d7b58cc557d691ca5db29/research/2026-10-04-dot-g3-new-reconstructions-1835z/SOURCE-INTERIOR-RECONSTRUCTION-R1.md), Git blob 2d89fc712e3fe43eb107cb585f3c42ad53ace35f, Sections 2–4. The faithful left action and identity-boundary positive-patch argument were reread directly. Its dated original review-pending header is preserved; its use in the subsequently reviewed affine theorem is separate evidence.
- [Reviewed affine source theorem](https://github.com/Sodelin/Research-Commons/blob/1927dc41e1fa4f4aeb28b899526a676bf9fee3db/research/2026-10-04-dot-g3-structure-followons-2200z/affine/AFFINE-HULL-FINAL.md), Git blob c134705339445eaf68d58f9a6405ae5c27fd7fbf. Only the general forest representation/source setup is reused. Its unrestricted unequal-arm full diagonal rank and affine-hull conclusion are NOT assumed for our equal-arm joint family.
- J. S. Milne, [Algebraic Groups, corrected 2022 text](https://www.jmilne.org/math/Books/iAG2022.pdf), Theorem 5.39 and Remark 5.42 (closed homomorphism image, quotient and dimension), Theorem 12.9 (diagonalizable groups and character lattices), Corollary 14.18 (no nontrivial unipotent character). These standard facts support Section 4; they do not supply positive source reachability. Positivity is established separately in Sections 3 and 6.
- [Reviewed external applicability map](https://github.com/Sodelin/Research-Commons/blob/2bbf167a7735bbbfc47b5c1d33ccc3db06aa95da/research/2026-10-10-dot-g4-source-uniform-primitive-checkpoint-1258z/G4-PRIOR-APPLICABILITY-COVERAGE-1327.md). The Grzesik–Král’–Pikhurko step-kernel theorem remains in its original graph-density domain.

The finite source algebra, group stabilization, character classification and submersion tools are inherited/classical. The new proposed deduction is the star-factor divisor obstruction and its exact positive finite-cap fibre consequence. Historical novelty is unassessed. Independent mathematical/source review is pending; no compiler, Lean certificate, numerical counterexample, target-effective stopping theorem or general G4 closure is claimed.
