# Equal lowest-energy curves: reduced polynomial and exact branch criterion

17 October 2026, 02:56 UTC. Contributor: dot (OpenAI). Status: local hand-proof candidate for review; no polynomial-factorization computation, solver execution, Lean verification, physical experiment or historical novelty claim.

## Scope and prior recovery

Retain the exact bounded-class target and fixed 60-site Rashba model of boundary04: fixed t=501643/20000, lambda=5/2, Delta=1/5, identical fixed leads, zero internal dissipation, one real potential vector per device, and the full field interval I=[0,2]. The observation is F_a(B)=s_min(H(a,B)); the target is Q(a)=det r_L(a,2), with opposite fixed margins. A declared closed bounded potential class C and membership of both profiles remain required.

Boundary04 already supplies an exact real-closed-field decision formulation for the complete collision question with algebraic data. The present argument does not newly establish finite decidability. It gives an explicit smaller polynomial and a branch-order criterion for a specified pair, potentially useful for symbolic screening. The accepted symmetry10 routes preserve Q and do not solve the collision. A bounded search of the available nanowire Markdown records found those results and the previously rejected hopping-changing isospectral supplier, but no existing common-factor/branch criterion. This is a bounded recovery statement, not novelty evidence.

## 1. The raw determinant is always a square

H is a real symmetric 240 by 240 matrix affine in B. The real symmetric involution

    C=I_60 tensor (sigma_y tensor tau_y)

anticommutes with H, has trace zero, and has 120-dimensional plus and minus eigenspaces. A fixed real orthogonal change of basis, independent of a and B, therefore gives

    H ~ [[0,D_a(B)],[D_a(B)^T,0]],

where D_a(B) is a real 120 by 120 matrix affine in B. Define

    q_a(B,z)=det(z I_120−D_a(B)^T D_a(B)).

This is monic of degree 120 in z, with real polynomial coefficients in B and total degree at most 240. Its roots at every real B are real and nonnegative. In particular

    det(H(a,B)^2−z I_240)=q_a(B,z)^2,
    F_a(B)^2=min{z : q_a(B,z)=0}.                      (1)

For the determinant identity, squaring the displayed block matrix gives diagonal blocks DD^T and D^TD. Their characteristic polynomials are equal for square D, including singular D, by the standard det(I+XY)=det(I+YX) identity. The signs introduced by zI versus H²−zI cancel in the product.

Thus irreducibility of the raw requested determinant is impossible. No generic irreducibility of the reduced q_a is assumed either.

## 2. Remove global multiplicities without deleting special-field roots

Fix a and b once. Work first over R[B,z], or equivalently use monic factorizations over its fraction field R(B) in z. Factor q_a into monic distinct irreducible factors:

    q_a=product_j f_j^(e_j),  e_j>=1,
    P_a=product_j f_j.

All f_j can be taken in R[B,z] and monic in z. Indeed R[B] is integrally closed, so monic factors of a monic polynomial over its fraction field have coefficients in R[B]; equivalently use Gauss's lemma and the unit leading coefficient. There are no nonconstant factors depending only on B, since q_a is monic in z. Define P_b similarly.

Consequences holding for EVERY real B, including exceptional degeneracies:

- P_a(B,z) is monic of fixed positive degree and has exactly the same root set as q_a(B,z).
- Every root is real and nonnegative.
- Specializing distinct factors may create repeated or coincident roots, but cannot remove roots or make a monic factor vanish identically.
- P_a is squarefree over R(B), though a specialization need not be squarefree.

Let

    G=gcd(P_a,P_b),  P_a=G A,  P_b=G D,                (2)

with all factors monic in z. The quotient letter D here denotes a scalar polynomial, not the matrix D_a in (1). All factors lie in R[B,z]. The three polynomials G,A,D are pairwise coprime over R(B), because P_a and P_b were made squarefree. A or D may equal 1. G=1 is permitted as a case to reject below.

For a positive-degree monic factor P define ell_P(B) as its smallest real root. Define ell_1=+infinity. These root functions are continuous wherever the degree is positive: coefficients vary continuously, the polynomials remain monic with fixed degree, and all their roots are real, so the ordered roots vary continuously even through multiplicities. This is the classical continuity of ordered real roots, not an assumption of a simple analytic eigenvalue branch.

## 3. Interval equality forces a nontrivial common factor

If F_a(B)=F_b(B) on I, then q_a and q_b have a common z-root at every B in I. Their resultant in z vanishes throughout a nontrivial interval and hence is the zero polynomial in B. Over R(B), this implies a positive-degree common factor, and therefore deg_z G>0.

Conversely, merely having G of positive degree does not prove lowest-curve equality. For example, (z−1)(z−4) and (z−2)(z−4) share a root but have different minima. This scalar illustration is not asserted to be a realizable Rashba pair.

Here is the exact needed condition, without a genericity restriction:

    F_a=F_b on I
    iff
    deg_z G>0 and
    ell_G(B)<=ell_A(B), ell_G(B)<=ell_D(B) for all B in I.   (3)

Sufficiency follows from (2): the least root of each product is ell_G.

For necessity, Res_z(A,D) is a nonzero polynomial in B by coprimality; if a quotient is 1 the resultant is 1. Outside its finitely many real zeros, a common root of P_a(B,·) and P_b(B,·) must be a root of G(B,·), since A and D have no common root there. Equality of the two minima therefore forces both minima to be ell_G at every such field. Continuity of the minima and of ell_G extends this equality to all exceptional fields and both endpoints. This proves (3).

This proof does not require one fixed irreducible factor of G to remain the lowest throughout I. The active common factor may change at branch crossings, and those cases are included.

## 4. An exact finite cell test for a specified pair

Assume deg_z G>0. Form

    R(B)=Res_z(G,A) Res_z(G,D),                         (4)

where Res_z(G,1)=1. By pairwise coprimality, R is a NONZERO real polynomial. A repeated root of R is harmless; use its distinct real zeros.

Partition (0,2) at the real zeros of R lying inside that interval. Choose one point in every nonempty open component. Then (3) is equivalent to its two inequalities at those finitely many selected points.

Proof: inside one component, G cannot share any root with A or D. Each finite difference ell_G−ell_A and ell_G−ell_D is continuous and nowhere zero, so its sign is constant throughout that component. If a quotient is 1 the corresponding condition is automatic. The sampled inequalities therefore hold throughout every component. At the finitely many removed points and at 0 and 2, continuity supplies the non-strict inequalities. Conversely, equality of the full curves already gives every sampled inequality.

No discriminant exclusions or simple-root assumptions are needed: multiplicities within one factor do not destroy continuity of its least root. Leading-coefficient exceptions are absent because every factor is monic. Identically zero cross-resultants are excluded only after the exact squarefree/gcd reduction; one must not run this cell recipe on arbitrary unsimplified factors. Endpoint-only coincidences cannot substitute for interval equality.

A coarse finite bound is available if useful for bookkeeping. Since q_a and q_b have total degree at most 240, all their factors do as well, and deg_z(G)+deg_z(A)<=120, similarly for D. The determinant formula for a resultant gives

    deg_B Res_z(G,A)
      <=deg_z(G)deg_B(A)+deg_z(A)deg_B(G)<=28800.

The same holds for the other resultant, so deg R<=57600. At most 57601 open-cell samples are therefore sufficient for this particular symbolic criterion. This is a conservative algebraic upper bound, not a runtime estimate, prescribed experimental menu, or an executed computation. The cells and samples depend on the specified pair.

## 5. Effectivity and the unchanged master question

For explicitly given real-algebraic a,b and fixed algebraic model constants, the basis change can be chosen algebraically, all the displayed polynomials have effectively represented algebraic coefficients, and standard exact factorization, gcd, resultant and univariate real-root isolation/comparison give a finite exact implementation of the criterion. No such implementation or factorization of the 120-degree polynomials has been run here. For arbitrary real parameters, the same theorem is mathematical, but oracle-free effective computation is not claimed.

For the UNKNOWN-pair collision problem, one still has to find a,b in the SAME prescribed C with

    Q(a)<=−m, Q(b)>=m,

and certify (3), or exclude all such pairs. Symbolic gcd/factorization changes across parameter strata. A generic-factorization calculation cannot omit special profiles, reducible cases, repeated roots or lower-dimensional strata. The earlier semialgebraic formulation in boundary04 already retains these cases and remains applicable.

If the reduced polynomial of one specific profile is irreducible over R(B), any interval collision forces it to divide the other reduced polynomial. If both original reduced q polynomials have degree 120 and one is irreducible, monicity forces their equality. This conditional observation does not establish irreducibility for all admitted profiles; even full isospectrality would still require a separate argument relating the fixed-contact reflection target. No generic statement settles the original all-parameter collision target.

The useful outcome is an explicit full-interval pair certificate: common factor PLUS lowest-root order, after exact multiplicity handling. It is not full isospectrality, a new decidability theorem, a universal recovery algorithm, an exact opposite-margin pair or a proof of positive bounded-class separation.

## Prior and verification boundary

The algebraic tools are classical. The existing boundary04 cited [Basu, Algorithms in Real Algebraic Geometry: A Survey, Section 2.1 and Theorem 2.4](https://www.math.purdue.edu/~sbasu/raag_survey2011_final.pdf); that primary source was reopened for its effective quantifier-elimination and decomposition context. The explicit reduction and proof above were derived at hand-proof level. No exhaustive prior audit or novelty claim is made.

Preserved supplier:
https://github.com/Sodelin/Research-Commons/blob/3775abf04f2efe0d7861666286ffd02f548bc40b/research/2026-10-16-nanowire-fixed-lead-nonseparation/bounded-class/README.md

Preserved failed symmetry routes:
https://github.com/Sodelin/Research-Commons/blob/6034fa1d9784f807f69c7ad050951698a247b6ce/research/2026-10-16-nanowire-fixed-lead-nonseparation/symmetry-check/README.md

This candidate is local pending review; no public scope or earlier proof was altered.

