# Extension to algebraic representations of the same source group

Contributor: dot (OpenAI), 6 October 2026. Hand-proof candidate extending the companion cocycle obstruction. No computation and no original-G4 closure claim.

## Exact scope

At any fixed cap use the same accepted freely parameterized INDEPENDENT private-word family S. In its fixed ordinary-conjugated faithful LEFT regular coordinates, the positive real source group has the form

G=T ⋉ U,  T={D(b):b_2,...,b_m>0},  U=I+u,

with fixed identity blocks at arities zero/one. The radical u is an associative nilpotent block algebra, decomposed as u=direct_sum_(i>j>=1) u_ij. Empty arity is isolated. Products of composable individual blocks satisfy XY=[X,Y] because the reverse product is zero. These are accepted source-group facts, not additional physical controls.

Here G is the positive real component of the accepted split real algebraic source group H, rather than the whole real algebraic group. Let rho:G→GL(V) be the restriction of ANY finite-dimensional rational/regular real algebraic group representation of H, and let chi(D(b)U)=product b_i^(alpha_i)>0 be a fixed diagonal monomial character. Let M be any fixed real symmetric form, possibly singular and indefinite. Suppose

D(K)=rho(K)^T M rho(K)-chi(K)M >=0 for every K in S,
D(E_tau)=0 for one tau>0.                                    (1)

**Claim:** D is identically zero on G. Hence passing to algebraic tensor/exterior-power representations cannot repair the specified PSD-cocycle method. This does not concern arbitrary nonlinear inequalities or non-PSD cone tests.

If rho is to be an original-observable certificate, its entries and chi must be recoverable from finitely many legal responses. The obstruction below allows even the full capped source kernel; thus it does not assume hidden observations are available.

## 1. Positivity forces conformality under the entire diagonal torus

The split torus acts in real weight spaces V_beta with algebraic characters beta(b), monomials with integer exponents. Write mu_beta=sum_i beta_i lambda_i, so rho(E_t) acts there by exp(-mu_beta t). Every u_ij has torus weight b_i/b_j and raises mu by lambda_i-lambda_j>0. Thus rho(U) is triangular in increasing mu, with no nontrivial action between equal-mu spaces. The diagonal of rho(K) is beta(b(K)).

Put c=sum alpha_i lambda_i. Ordinary equality in (1) forces M_beta,gamma=0 unless mu_beta+mu_gamma=c.

If mu_beta>c/2, a vector in V_beta and its image under rho(K) have no possible self-pair under M. Its D-quadratic form is therefore zero. PSD makes its entire D-row zero. Pairing with V_gamma of complementary ordinary weight gives

(beta(b(K))gamma(b(K))-chi(K)) M_beta,gamma=0.                (2)

All higher triangular terms have ordinary weight sum larger than c and disappear. For a nonzero block, the accepted diagonal-character sign theorem forces beta gamma=chi as characters, not just on ordinary time.

In the middle ordinary eigenspace mu=c/2, the diagonal beta-block of D is

(beta(b(K))^2-chi(K)) M_beta,beta.

Unless beta^2=chi, the scalar takes both signs by the same source theorem, so M_beta,beta=0. If beta^2=chi, that D-block is already zero. Thus every individual beta-block has zero D-quadratic form in either case. PSD then makes all its D-cross rows zero, and (2) again forces beta gamma=chi wherever M_beta,gamma is nonzero.

It follows that

rho(T)^T M rho(T)=chi(T)M for every T in the positive torus.   (3)

If M=0 the conclusion is immediate. Otherwise (3) in particular forces chi to be an algebraic weight pairing. Caps zero/one are trivial; the cap-two ordinary-normalized character assertion is elementary, as in the companion proof.

## 2. Logical extensions of positivity, not physical source operations

For K=D(b)+N in S put U(K)=K D(b)^(-1)=I+N D(b)^(-1). By (3) and the cocycle identity,

D(U(K))=rho(D(b))^(-T) D(K) rho(D(b))^(-1) >=0.              (4)

For any positive torus T and U in U,

D(TUT^(-1))=chi(T)rho(T)^(-T)D(U)rho(T)^(-1).                (5)

Thus every torus conjugate of U(K) also has PSD defect. Equations (4)–(5) are consequences of the hypothesized certificate. They do not assert that inverse diagonals or torus conjugates are admitted sources.

Let A(X)=d rho(X)^T M+M d rho(X) for X in u. We prove A(u)=0 by induction on block distance d=i-j.

## 3. Remove lower grades and extract the next one

Let T_epsilon have b_i=epsilon^(i-1) for i>=2 and b_1=1. Its adjoint scales u_ij by epsilon^(i-j). For fixed actual K write

U(K)=I+sum_(d>=1) U_d(K),
log U(K)=sum_(d>=1) Z_d(K),

where all sums are finite and homogeneous in block distance. Assume A vanishes on every u_ij of distance less than d. The corresponding elements form infinitesimal M-isometries; their Lie algebra and exponentials preserve M.

Conjugate U(K) by T_epsilon and left-multiply by

exp(-sum_(e<d) epsilon^e Z_e(K)).

This multiplier is an M-isometry, so the resulting defect stays PSD by the exact cocycle identity. Its matrix logarithm is epsilon^d Z_d(K)+O(epsilon^(d+1)). Hence its leading defect is

epsilon^d A(Z_d(K))+O(epsilon^(d+1)),

and A(Z_d(K)) is PSD.

The finite associative logarithm shows that Z_d-U_d is a sum of products of at least two lower-distance blocks. A nonzero product follows a strictly increasing arity chain. It is a nested commutator of those individual blocks; all reverse products vanish. Thus it lies in the Lie algebra of already established M-isometries. Consequently

A(Z_d(K))=A(U_d(K)) >=0.                                  (6)

This argument also applies after any constant positive torus conjugation, by (5).

## 4. Separate blocks and use the actual affine source theorem

For fixed distance d, the characters b_(j+d)/b_j are independent: their edges j→j+d form disjoint directed paths, with no cycle. One can prescribe arbitrary positive ratios along them recursively, keeping b_1=1. Therefore a constant torus can scale one selected distance-d block by R and every other distance-d block by 1.

Apply (6) after this conjugation, divide by R and let R tend to infinity. The closedness of the PSD cone gives

A(U_ij(K)) >=0 for every actual K.

But U_ij(K)=K_ij/b_j(K), with b_j>0. Hence

F_ij(K)=A(K_ij) >=0.                                      (7)

F_ij is LINEAR in the ORIGINAL capped kernel K: K_ij is a fixed block of its faithful regular matrix and A is a fixed linear map. It vanishes on ordinary edges. The accepted same-family affine-PSD corollary therefore gives F_ij(K)=0 for every K in S.

The accepted affine-hull theorem says that the actual off-diagonal blocks K_ij span u_ij. Thus A(u_ij)=0. This proves the induction at distance d, and eventually A(u)=0.

## 5. Conclusion and boundaries

Every rho(exp X), X in u, preserves M. Since U=exp u and the torus is conformal by (3), all of G is conformal with character chi. Thus D(K)=0 identically, proving the claim.

The proof does not replace positivity by a finite sample check. It controls every original positive private word through exact source group/convex facts. It allows nonlinear algebraic representations, including finite tensor powers, and indefinite forms. The source positivity assumption cannot yield a strict genuine-bigon defect in this class.

This leaves arbitrary non-cocycle observables, positivity restricted to a different invariant cone rather than all vectors, non-algebraic representations, other mechanism/tie classes, and the original master problem untouched. No necessity of the rare-route return construction is asserted.

All provider identities and original assumptions are those bound in SOURCE-COCYCLE-OBSTRUCTION.md and SOURCE-BINDINGS.json. This extension requires its own independent hand review before acceptance.
