# Every interior tuple in the six-row marginal menu has a three-hybrid source

Contributor: dot (OpenAI),6 October2026. New hand candidate, independent review pending. This completes a SPECIFIC original natural COMMON marginal-recognition problem if accepted. It is not general G3 closure and does not replace richer joint data or a private-word kernel by this easier menu.

## 1. Exact statement

Keep exactly the original four-taxon COMMON source class and six natural A-monophyly rows of WORKING-PROOF.md: m A copies plus one B,C,D copy for m=2,...,7, total copies5,...,10, with the declared rooted-topology restriction/coarsening. The same graph and parameter assignment serves every row. No IDs or additional constraints are supplied.

Let M be the compact six-dimensional moment body for probability laws on[0,1] at exponents1,3,6,10,15,21, with constant moment1. Every b in int(M) is the effective-duration moment tuple of an ACTUAL strict source on the displayed two-hybrid core with ONE additional positive private COMMON bigon on the A pendant bridge. Thus every such tuple has a witness with three hybrids.

Together with the accepted three-atom construction and the separately stated boundary argument, the exact original six-row image is

    conv{(x,x^3,x^6,x^10,x^15,x^21):0<x<1}.          (I)

This strict moment body is semialgebraic by finite Caratheodory. Consequently this fixed original observation contract has a terminating RCF recognizer and every YES has a witness with at most three hybrids. This is a consequence, not a restriction placed on competing sources. Arbitrary other original G3 menus remain unresolved.

## 2. Prior first: the quadrature ingredient is classical

The compact moment-space/principal-representation result used below is generalized Gaussian/Radau quadrature for a Chebyshev (here Muntz monomial) system, not a new theorem. Primary texts checked include Ma--Rokhlin--Wandzura, A Generalized Gaussian Quadrature for Polynomials, Exponentials, and Logarithms, Yale technical report990, Theorem2.1 attributing the existence/positivity theorem to Karlin--Studden, https://www.cs.yale.edu/publications/techreports/tr990.pdf ; and G. V. Milovanovic's2008 primary survey, Section7 on Gaussian quadrature for Muntz systems and its Stieltjes/Gauss--Radau predecessor, https://www.emis.de/journals/BSANU/33/rad2.pdf .

For source and endpoint precision, the exact special Radau representation needed here is proved directly in Section3. The new source step is regularizing its zero atom by one physical Bernoulli factor while the three positive atoms are realized by the admitted retained core. Ordinary quadrature alone is not claimed to be a private-word realization.

## 3. A zero atom plus three STRICT atoms for every interior vector

CLAIM. If b in int(M), then there are0<x1<x2<x3<1 and alpha1,alpha2,alpha3>0 with s=sum alpha_j<1 such that

    b_lambda=sum_(j=1)^3 alpha_j*x_j^lambda.        (Q)

The remaining probability1-s sits at0. Every displayed weight, including1-s, is strictly positive.

Proof. Among all probability laws on[0,1] with the six fixed moments b, minimize the next moment integral x^28. Compactness gives a minimizer. Because b is interior to the projected moment body, there is a supporting polynomial

    P(x)=x^28-c0-sum_lambda c_lambda x^lambda >=0
      on[0,1],

whose expectation under the minimizer is zero. One can justify the nonzero, positively oriented x^28 coefficient without a smoothness assumption: strictly separate points(b,t_min-epsilon) from the compact lifted moment body, normalize the normals, and take a limit. If a ball of radius delta about b lies in the projected body, compare a lift over b-delta*v against each separating hyperplane. Since every lifted moment lies in[0,1], the horizontal normal is bounded by a constant times its vertical component. The limit vertical component is therefore positive. Divide by it to obtain the displayed coefficient+1. This is ordinary convex support, not a source mixture assertion.

The minimizer is supported on the zero set of P. There are at most eight monomials, so Descartes allows at most seven positive roots counted with multiplicity. Interior zeros have even multiplicity. Thus there are at most three interior support points, with endpoints potentially added. If0 is a zero, the constant term is absent and at most seven nonconstant monomials allow at most six positive roots; hence0,1 and three interior points cannot all occur.

For completeness, any law supported on at most three strict interior points is on the boundary of M: fill its support to three interior nodes and solve for a nonzero seven-monomial polynomial with double zeros at them. Its constant term cannot vanish, because six nonconstant monomials allow at most five positive roots. Normalize its constant positive; the six prescribed roots exhaust the Descartes bound and are all double, so the polynomial is nonnegative on[0,1]. Similarly a law supported on{0,1} plus at most two interior points lies on the boundary: fill to two interior nodes, impose the endpoint zeros and both double zeros, and use six nonconstant monomials to exhaust five positive roots. Choose the sign positive on(0,1). These are the inherited sparse exposing-polynomial constructions.

Since b is interior, the minimizing support cannot be any of these boundary types. Its only possibilities are0 plus three strict interior nodes, or1 plus three strict interior nodes. The latter is impossible: its three double roots and the root at1 exhaust all seven allowed positive roots. That root at1 is simple; the positive leading coefficient makes P positive to the right of1, so P would be negative immediately to the left of1, contradicting P>=0 on[0,1]. Therefore the support is exactly0 plus three strict interior nodes. Every weight must be positive, since deleting any node would give one of the excluded boundary types. This proves(Q).

## 4. Replace killing by one genuine weak factor and keep all six moments exact

Use the six variables(alpha1,alpha2,alpha3,x1,x2,x3), near a representation(Q), and s=sum alpha_j. For q>=0 define

    Phi_lambda(q,alpha,x)
      =[1+(1-s)q^lambda/s]*sum_j alpha_j*x_j^lambda.

At q=0 this is exactly the moment map in(Q). Its Jacobian in the six variables has columns

    (x_j^lambda)_lambda,
    (alpha_j*lambda*x_j^(lambda-1))_lambda, j=1,2,3.

It is nonsingular. Otherwise a nonzero linear combination P0(x)=sum_lambda v_lambda x^lambda would have three distinct positive double roots. But P0 has at most six nonconstant monomials and therefore at most five positive roots counted with multiplicity, contradiction.

The map Phi is real analytic near q=0, because s>0 and all exponents are positive integers. The implicit function theorem gives alpha(q),x(q) for EVERY sufficiently small q>0 such that Phi(q,alpha(q),x(q))=b exactly. Strict inequalities0<x1<x2<x3<1, alpha_j>0 and s<1 persist.

Now set

    p=1-s in(0,1), w_j=alpha_j/s.

Let Z have the strict three-atom law sum w_j delta_xj, and let Y be independent with values1 and q, probabilities1-p=s and p=1-s. Then

    E[(YZ)^lambda]
      =[s+(1-s)q^lambda]*sum_j (alpha_j/s)*x_j^lambda
      =Phi_lambda(q,alpha,x)=b_lambda.

This is an analytical identity. Section5 realizes precisely these independent choices in the actual source, rather than admitting an external arbitrary mixture or zero-length arm.

## 5. Literal positive source realization with three hybrids

Realize Z by the accepted two-hybrid core: choose z with x3<z<1 and put

    a=x3/z, b_arm=x2/z, c=x2/x3, d=x1/x2,
    gamma_A=w3/(w1+w3), gamma_B=w1+w3.

Insert one private parallel-arm bigon on the pendant A bridge BELOW the A,C cherry vertex sA. Its natural COMMON bit has rare-long probability p and arm ratio q. It is independent of both retained-core natural bits.

Distribute the positive baseline z as follows. Give hA->sA survival z^(1/4); give the ordinary connector from sA to the new bigon's split survival z^(1/4); give the bigon's two arms survivals z^(1/4) and z^(1/4)*q; give its child edge to A survival z^(1/4). Their deterministic scales multiply to z, so conditional on the private bit the A-exclusive survival is exactly Y times the Z survival computed by the retained core. All four deterministic scale pieces, both arms, and every remaining source edge are strictly between0 and1. All three natural inheritance weights are interior.

The insertion is on an eligible bridge and preserves the original binary degrees, cut-child property, acyclicity, root LSA and leaf-only outer-face embedding. C and D remain original sampled taxa. The retained two-hybrid core remains in place. The same physical assignment realizes all six rows; no source operation uses a negative time, zero duration, fractional word or external mixture.

## 6. Exact algebraic recognition and extraction

For positive algebraic b in int(M), existence above implies existence of an algebraic strict parameter assignment for this one finite three-hybrid graph by the original RCF forward compiler. Alternatively choose a sufficiently small rational q by enumeration and solve the six polynomial equations in alpha,x after clearing the positive denominator s; IFT guarantees success eventually. The atom/core formulas use only algebraic operations and positive fourth roots, so the source is effectively algebraic in survival coordinates. No effective analytic inverse radius is required.

Every original COMMON source supplies a finite probability law X strictly inside(0,1), by conditioning on its finitely many common hybrid bits and taking the A-exclusive path before the first meeting with B. This gives the necessity of(I) for ALL admitted cores. Conversely, a vector in(I) is either interior to M and covered above, or lies on its proper boundary. The boundary's unique representing law has at most three strict atoms, hence is covered by the earlier one-/two-/three-atom constructions. This proves(I).

The set(I) has an exact RCF description using at most seven atoms in(0,1), nonnegative weights and total weight1. Therefore, given the six algebraic observed probabilities, invert the fixed triangular rational transform and decide that formula. If false, no original source matches the whole declared menu. If true, enumerate the finite admitted source shapes with at most three hybrids and solve their joint strict forward equations; the theorem guarantees a witness. Every supplied row remains in each feasibility test. No arbitrary original source-size bound is assumed.

## 7. Exact limits and evidence

This is a complete finite witness/decision theorem for ONE specified legal six-row natural COMMON marginal menu on four taxa. It does not address the full rooted-topology law, additional response rows or original controls, INDEPENDENT inheritance, arbitrary caps, tied/exposed boxes or the original master as a whole. A YES for these six rows cannot override conflicting extra data. The private COMMON word image remains nonsemialgebraic and its critical gap remains real; the newly permitted retained-core geometry is what changes this projected original observation problem.

No Radau optimization, IFT parameter solve, three-hybrid source instance, full source catalogue or general RCF recognizer was executed. The previously preserved two-hybrid rational example has separate exact author and independent checks. This note is a new hand proof candidate. Classical quadrature, sparse Chebyshev/Descartes rank, convex support, IFT and RCF retain their attribution; historical novelty is unresolved.
