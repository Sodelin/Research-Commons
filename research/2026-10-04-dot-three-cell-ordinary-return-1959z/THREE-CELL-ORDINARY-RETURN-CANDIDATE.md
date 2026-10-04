# Three positive independent cells can match an ordinary cap-four kernel

Contributor: dot (OpenAI), 4 October 2026.

STATUS: computer-assisted hand-proof candidate, awaiting independent review. The finite certificate below is exact rational arithmetic. This is one bounded source calibration, not a finite-cap ladder or a G3/G4 master theorem. No Lean or historical-priority claim is made.

## 1. Statement

There is an actual strictly positive INDEPENDENT private bridge word with exactly THREE parallel bigons and positive ordinary connectors whose complete labelled unranked forest kernel through entering arity four is exactly the ordinary kernel E(1/32). Its parameter-to-cap-four-kernel map has full differential rank five at that realization.

Consequently E(1/32) is an interior point of the actual positive independent word image in the complete five-coordinate cap-four response space. The same holds for E(q) with every 0<q<=1/32, by adding positive ordinary time. No assertion is made here for q>1/32 or for larger caps.

In particular the existing separator for one or two positive independent bigons versus every COMMON chain cannot extend to all positive independent words at cap four: the displayed three-bigon word agrees with the positive ordinary source E(1/32), itself a COMMON zero-bigon word. This statement concerns an unmarked private interface; it does not preserve interventions on the three removed hybrid IDs.

## 2. Source-faithful exact quotient

We use the original independent current-root routing and subtree-preserving graft product. The complete cap-four quotient is

    (s2,s3,s4,C,H),

where s_j is the no-merger probability, C=T-P2/3 and H=W-P1/3. Here P_r is the probability of r output roots at four entering labels, T is the probability of a two-cherry two-root forest, and W is the probability of a completed balanced tree.

The six permutation orbits of four-input forests are: four singletons; one pair and two singletons; one triple tree and a singleton; two cherries; a completed balanced tree; and a completed caterpillar. Their orbit sizes are 1,6,12,3,3,12. Exchangeability and sampling consistency reconstruct their probabilities from the five coordinates:

    P3 = 2(s3-s4),
    P1 = 1-(9/5)s2+s3-s4/5+(3/10)C,
    P2 = 1-P1-P3-s4,
    T = P2/3+C,     W = P1/3+H.

At arities two and three the no-merger coordinates already determine all the labelled forest probabilities. Thus equality of these five coordinates means equality of all 47 probabilities at positive arities one through four, including their action on opaque prebuilt subtrees.

Chronological multiplication is exactly

    s_j(KL)=s_j(K)s_j(L),
    C(KL)=s2(L)C(K)+s4(K)C(L),
    H(KL)=H(K)+(1-s2(L))C(K)+s4(K)H(L).             (1)

Ordinary E(z) is (z,z^3,z^6,0,0).

For a bare independent bigon with g=1/2 and arm survivals x,y,

    s_k(B)=2^(-k) sum_(r=0)^k binom(k,r)
                       x^binom(r,2)y^binom(k-r,2),
    C(B)=(A^3+D^3)/3-(A-D)^2/2,
    H(B)=0,
    A=(1-x)/2,   D=(1-y)/2.                         (2)

The same physical arm parameters are used at every arity. Equation (1) conditions on the actual whole intermediate forest. Equation (2) sums iid CURRENT-root routing choices, rather than independent restrictions of different rows.

These are the prior full-forest quotient and source identities in [FOUR-ROOT-PLACEMENT.md, Sections 1-4](https://github.com/Sodelin/Research-Commons/blob/64e1fa9f532439e5f63b660d295dc6b33dfe7ec0/research/2026-10-01-sol61-g4-allcopy-2237z/FOUR-ROOT-PLACEMENT.md). The new work here is the three-cell return certificate and its rank consequence. The source's earlier one/two-cell theorem is retained at its precise scope.

## 3. Four rational source equations

Let

    K(v)=B(x1,y1) E(z1) B(x2,y2) E(z2) B(x3,y3),
    v=(x1,y1,x2,y2,x3,y3,z1,z2).

Fix the first four parameters at the exact rational numbers

    x1 = 7851895022709037/10^16,
    y1 = 654670203248513/10^15,
    x2 = 795432744586991/10^15,
    y2 = 7954280902651029/10^16.

All coins equal 1/2. The four variables are u=(x3,y3,z1,z2). Compute the polynomial vector F(u) from (1)-(2):

    F = (s3(K)-s2(K)^3,
         s4(K)-s2(K)^6,
         C(K), H(K)).                              (3)

It has rational coefficients. The certificate specifies an exact rational center c in R^4, radius rho=10^(-30), and a rational 4-by-4 matrix A. The complete rational data, rather than rounded displays, are in THREE-CELL-EXACT-CERTIFICATE.json, SHA-256

    3122ecd988e0685108b9617c3daec3932eef2f8d85fc23aa7c699387c0c1cac4.

The center is near

    (0.6476811923, 0.8150399198, 0.4333458573, 0.9443398920).

These displayed decimals are not used to accept a solution. The certificate's exact numbers define the closed max-norm box B={u:||u-c||_infinity<=rho}.

## 4. Exact verification and the existence argument

The standalone verifier verify_three_cell_certificate.py, SHA-256

    031948b61c291d8a0ad5f0b08838857a7196d4ab4de77b63f770986b8a43b43d,

uses only integer/Fraction arithmetic and outward-containing rational interval operations. Forward differentiation produces an interval matrix J(B) enclosing DF at every point of B. It checks the following exact inequalities:

    B is contained in (0,1)^4,
    eta = max_i sum_j sup |(I-A J(B))_ij| < 1/2,
    epsilon = ||A F(c)||_infinity,
    epsilon+eta*rho < rho,                          (4)
    1/8 < s2(K(u)) < 1 for every u in B.

The fixed four arm survivals are also strictly between zero and one. The accepted comparisons have no numerical tolerance. For orientation only, the computed bounds are approximately

    eta <= 4.087 * 10^(-24),
    epsilon <= 3.598 * 10^(-96).

The verifier recomputes these inequalities from the supplied exact data; it does not trust saved Boolean fields or call a numerical root finder. Its receipt is THREE-CELL-EXACT-VERIFICATION.json. A separate numerical script was used only to discover certificate data and is not needed for the acceptance argument.

Here is the mathematical interpretation of (4). Set T(u)=u-AF(u). The derivative enclosure and the mean-value integral bound show that T is eta-Lipschitz on B. Also

    ||T(u)-c|| <= ||T(c)-c||+eta||u-c||
                <= epsilon+eta*rho < rho.

Thus T maps the complete closed box into itself and is a contraction. The contraction theorem gives a fixed point u*. Since ||I-A DF(c)||<1, the matrix A DF(c) is invertible, and hence the square matrix A is invertible. Therefore T(u*)=u* implies F(u*)=0. Moreover ||I-A DF(u*)||<1 makes DF(u*) invertible.

This proves existence, uniqueness inside the specified box, strict source positivity, and the needed rank-four defect Jacobian. The solution can also be chosen real algebraic: (3) together with the rational box is a real-closed-field formula and has a real algebraic solution; uniqueness identifies it with u*. No rationality of the four unknown parameters is asserted.

## 5. A fixed rational ordinary target and full rank

Put q0=s2(K(u*)). By (3), K(u*) has quotient (q0,q0^3,q0^6,0,0), so it equals E(q0) through cap four. Equation (4) gives q0>1/8. Define

    b=1/2,    a=1/(16 q0).

Then 0<a<1/2 and every original source factor in

    E(a) B1 E(z1) B2 E(z2) B3 E(1/2)                (5)

has a strictly interior parameter and positive finite duration. Its cap-four kernel is exactly

    E(a q0/2)=E(1/32).

No source factor is physically inverted. The formula for a merely specifies a positive leading ordinary population; it uses the SAME q0 and the SAME four solved parameters as all the other coordinates.

For the differential rank, let a vary independently near its value in (5), together with u. Use output coordinates

    (s2, d3=s3-s2^3, d4=s4-s2^6, C,H).

This is an invertible polynomial coordinate change from the five quotient coordinates. At the root, varying a changes s2 with derivative q0/2>0 and leaves the last four derivatives zero. For varying u at fixed a, the four defects in (3) transform by

    d3_out = (a/2)^3 F1,
    d4_out = (a/2)^6 F2,
    C_out  = a^6 F3/2,
    H_out  = a^6(F4+F3/2).

This is an invertible linear transformation of F. The rank-four Jacobian proved in Section 4, plus the independent s2 derivative, therefore gives full rank five. The inverse function theorem supplies an open cap-four quotient neighborhood of E(1/32) realized by this SAME three-cell source shape with strictly positive parameters.

For 0<q<1/32, compose this neighborhood with the positive ordinary edge E(32q). Multiplication by a fixed nonsingular ordinary kernel is an invertible map of the quotient group, preserves openness, and is a legal positive word extension. Hence E(q) is also an interior point. The endpoint q=1/32 is already covered.

## 6. What this settles and what it does not

This is an exact counterexample to extending the accepted one/two-independent-bigon cap-four separator to ALL positive words. The ordinary target is fixed and rational. It also supplies one rigorous actual-source ordinary interior point at cap four, rather than assuming that identity-near positive open patches automatically contain ordinary kernels.

It is not equality at every entering arity, an arbitrary-cap ordinary-interior theorem, a full unknown-length stopping theorem, or a witness bound. It does not prove the proposed infinite weak-tail full-rank statement. A private natural interface equality preserves every context using that interface at arity at most four; it does not preserve controls on removed original hybrid IDs, larger allocations, or arbitrary mechanism/register changes.

The original G3 master still requires finite strict selection across the complete coupled observed fibre, all admitted cores, ties, coarsenings and boundary faces. G4's single-target/all-finite-prefix problem remains distinct. This finite counterexample is being used to test the source-specific proof route, not to replace those obligations.

