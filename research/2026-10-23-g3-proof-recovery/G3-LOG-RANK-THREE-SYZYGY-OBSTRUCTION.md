> Recovered authored source, 23 October 2026. Current disposition is in the package result catalogue. A completed hand proof is **PROVED (not Lean formalized)** at its stated scope; independent review is a separate field. Historical candidate/open headers below do not reopen a completed component or establish a broader endpoint. This publication is not a new proof or a new execution. Private local addressing/receipt locators are omitted; the original and public hashes and exact projection kinds are recorded in SOURCE-MANIFEST.json.

# G3: all homogeneous rank-three logarithm matrices already have the rectangle

Existing G3 owner,22October2026UTC. NEW **HAND/UNCOMPILED** argument plus a
separate actually executed exact finite algebra certificate. No arithmetic
zero procedure, original source recognition or G3 endpoint is claimed.
No subagent, model, compiler/native job or local Git action occurred.

## Precise result

Keep the inherited purity branch and notation

    ell_n=a*T_n(r), a>0, n in {3,6,10,15,21},
    T_n(t)=sum[k=0..n-2](n-1-k)*t^k.

Assume r is transcendental. Let L(X) be ANY m-by-n matrix of homogeneous
RATIONAL linear forms in five variables, with rank L(T(r))=3 and

    3 < mn/(m+n).                                     (1)

Then L(X) already has an identically zero rectangle after invertible
rational row/column operations, whose dimensions m',n' satisfy

    m'/m+n'/n>1.                                     (2)

Consequently the proved Waldschmidt--Masser theorem cannot contradict this
putative pure branch by ANY such rank-three matrix: its rectangle conclusion
already holds before any logarithm is substituted. Together with the prior
rank<=2 argument, this screens all homogeneous rational-linear rank<=3
matrix sizes. It does NOT screen rank>=4, affine constants or auxiliary logs.

The proved arithmetic theorem/strict bound and its primary-source scope
are retained in G3-LOG-MATRIX-RANK-BOUNDARY.md. This argument does not invoke
the stronger structural-rank or Matrix Coefficient conjectures. Multiplying
by the same nonzero a does not change the matrix rank.

## The exact NEW finite input

Let P be the kernel of the homogeneous map

    Q[X1,...,X5] -> Q[u,t], Xi -> u*T_i(t).

It is a homogeneous PRIME ideal. The formal scale u here is only a device
to define the homogeneous relation ideal, not an auxiliary logarithm in L.
The previous exact coefficient certificates give P1=P2=P3=0 and dim P4=9.
The NEW calculation computes ALL linear syzygies of this complete P4:

    S1(P4)=ker(P4 tensor span_Q(X1,...,X5) -> Q[X]_5).

In the old exact integer quartic basis, its multiplication matrix is
126-by-45, with EXACT rank43 and nullity2. All kernel vectors were checked
against the ORIGINAL integer multiplication matrix; their distinct positive
free coordinates prove independence. A43-by-43 minor has determinant673103
modulo the previously certified prime1000003, giving the rank lower bound.
Thus dim_Q S1(P4)=2, including after extension of scalars to Qbar.

check_log_curve_quartic_syzygies.py3935B/SHA
3cc7fd8d805177d84b05f27617d6d5804ab446cde81360fbea970e3ac0c15b2a
reuses the exact old curve/kernel constructors. The quartic basis is a
necessary input to this NEW multiplication question, not a new claim that
the earlier degree1--4 computations were missing. The executed result keeps
the entire multiplication matrix, monomial/column orders, old quartic basis,
two integer syzygies and complete minor indices, encrypted before persistence:

    [encrypted runtime receipt retained privately]
    ciphertext da73b4f2d6a7d950278ea2358ebbcf14ab6f1fc2b59494e3308a3a172ce2d142.

Actual execution took0.662seconds. No full quintic relation ideal, numerical
log equality, determinant-matrix classification or G3 decision was run.

## Lemma: universal linear determinant identities span the field kernel

For any m-by-n matrix A over a characteristic-zero field K, rank A>=4,
consider one formal coordinate z_IJ for each4-by-4 minor. The evaluations
of UNIVERSAL linear identities among generic4-minors span, over K, the
entire kernel of the functional z_IJ -> det A_IJ.

Here "linear identity" means a coefficient homogeneous linear in the
generic matrix entries multiplying each degree4 minor. We need no general
minimal-resolution theorem. The following identities suffice after rank
normalization:

1. In a4-by-5 submatrix, expansion with one duplicated row gives a linear
   relation among its five4-minors, for each of its four rows.
2. The transposed5-by-4 duplicated-column identities.
3. In a5-by-5 submatrix, the difference of any two Laplace expansions of
   its determinant, along rows or columns, is such a linear identity.

The vector space of ALL universal linear identities is defined by rational
coefficient equations. It is stable under row/column changes and extension
of scalars: Cauchy--Binet linearly transforms the minor coordinates, and a
change of the generic matrix variables transforms degree1 coefficients.
Therefore it suffices to verify spanning at A=diag(I_s,0), s=rank A. Row/
column operations over K in this proof need not be rational constants; they
only prove a field-span statement about universal identities.

At that diagonal matrix, write I0,J0 for the portions of I,J in {1,...,s}.
If I0!=J0, a duplicated-row or duplicated-column relation forces z_IJ=0:
choose an unmatched pivot index and add its missing column/row. The selected
diagonal entry1 is the only surviving coefficient in that relation.

If I0=J0=P but |P|<4, both I and J contain an index outside {1,...,s}.
Choose a pivot index b outside P. In the5-by-5 submatrix with rows I+{b}
and columns J+{b}, expansion along row b is, up to sign, z_IJ; expansion
along a zero row is0. Identity3 therefore forces z_IJ=0.

Only coordinates z_PP with P a4-subset of {1,...,s} remain. If s=4 there
is just one. If s>4, Identity3 on each principal5-subset equates the
coordinates for its4-subsets. The graph of4-subsets joined when their
intersection has size3 is connected. Thus every remaining coordinate is
equal. These are exactly the actual minors, all1, up to a single common
scalar. The quotient by the universal linear relations has dimension1,
as asserted. This proves the lemma for all sizes, not by finite sampling.

## The span of L's quartic minors has dimension at most three

Work over K=Q(X1,...,X5). If the generic rank of L is>=4, let W be the
rational span of ALL its4-minors and let d=dim_Q W. Transcendence of r and
rank L(T(r))=3 imply every one of these minors vanishes IDENTICALLY on the
parametrized curve. Hence W is a subspace of the known complete P4.

Choose a rational basis F1,...,Fd of W. Expressing all minors in this
basis is a constant rational surjection C:Q^N -> W. The minor-evaluation
functional over K factors through the nonzero functional

    W tensor K -> K, Fi -> Fi(X).

Its kernel has dimension d-1. By the preceding lemma, universal linear
determinant identities span the full preimage kernel before applying C;
after C they therefore span this(d-1)-dimensional kernel. Each projected
identity has coefficients which are rational LINEAR forms in X, so is a
member of S1(W), embedded in S1(P4). Its K-span has dimension at most2
by the exact certificate. Therefore d-1<=2 and

    d<=3.                                           (3)

This uses all minors together, not only a particular4-by-5 block. Linear
dependencies among the minors cause no problem: quotienting by C's constant
kernel maps the full functional kernel SURJECTIVELY onto the kernel in W.

## Prime-ideal factorization excludes d=2 or d=3

If d=2, the field-span statement gives a nonzero linear syzygy
l1*F1+l2*F2=0. Independence of F1,F2 makes l1,l2 nonproportional nonzero
linear forms, hence coprime. The UFD property gives F1=h*l2,F2=-h*l1 with
h homogeneous of degree3. Primality and P1=P3=0 contradict Fi in P.

If d=3, it gives two K-independent linear syzygy vectors b,c in Q[X]_1^3.
Their nonzero cross product q=b cross c has degree2, and F=(F1,F2,F3) is
proportional to q over K. Divide q by the gcd g of its nonzero coordinates,
degree e<=2, to obtain a primitive vector q'. Primitivity and the UFD
property imply

    F=h*q', h in Q[X], deg h=2+e, deg q'=2-e.

If e=2, q' is constant, contradicting independence of the three Fi. If
e=0 or1, h has degree2 or3, so h is not in P. Primality then puts every
nonzero coordinate of q' in P, of degree2 or1, also impossible. This
excludes d=3. None of these UFD steps assumes independence of logarithms;
they concern the exact formal polynomial prime ideal.

Thus a generic-rank>=4 L must have d=1: all its4-minors are rational
multiples of one nonzero F in P4.

## d=1 forces generic rank4 and a constant four-dimensional block

If generic rank were>=5, choose an invertible5-by-5 submatrix B over K.
Its adjugate is F*D for a constant rational matrix D, since every cofactor
is a4-minor. D is invertible. Laplace expansion gives det B=F*l for a
nonzero homogeneous linear l. The adjugate identity yields

    B*D=l*I, hence B=l*D^{-1}.

Its nonzero4-minors are therefore constant multiples of l^4. Since one
is also a nonzero constant multiple of F, F is proportional to l^4.
Primality then gives l in P1, contradiction. Generic rank is exactly4.

Choose an invertible4-by-4 pivot block B. In the top four rows, Cramer's
rule expresses each other column as B times a vector of4-minor ratios.
All these ratios are rational CONSTANTS, because numerator/denominator
are constant multiples of F. The corresponding statement holds for other
rows. Generic rank4 then gives constant rational row/column relations
putting the whole L in one4-by-4 block, with all other rows/columns zero.

If m,n were both4, (1) would fail. Otherwise at least one zero full row or
column gives an identically zero rational rectangle satisfying (2). This
case therefore cannot provide a new arithmetic contradiction either.

## Generic rank3 and conclusion

If the generic rank was already3, choose a rational x0 of rank3 and put
L(x0) in rank normal form by rational operations. For every rational y,
all4-minors of L(x0)+h*L(y) vanish identically. The linear h coefficient
in each pivot3-plus-one minor is the corresponding bottom-right entry of
L(y). Hence that entire(m-3)-by-(n-3) rectangle is identically zero.
Its normalized size is2-3/m-3/n>1 by (1). This is exactly the elementary
maximal-rank tangent argument used earlier, now applied to generic rank3.

These cases exhaust the generic rank: it cannot be below the specialized
rank3; when it is above3, (3) and the prime-ideal argument reduce it to the
constant four-block case. The announced all-size rank-three screen follows.

## Scope and next real gate

The arithmetic purity/exact-zero implication remains OPEN. This new result
eliminates the earlier smallest rank3 shapes5-by-8,6-by-7,7-by-7 and ALL
larger homogeneous rational-linear rank3 attempts, not merely those samples.
No qualifying contradiction matrix was constructed. The next such route
would need rank>=4 and a genuinely new higher-degree structure. Combined
with the earlier width bound, possible first rank4 shapes include6-by-13,
7-by-10,8-by-9 and9-by-9; this is not an existence claim.

The new finite computation did NOT find zero linear syzygies: it found TWO.
The proof above explicitly uses that outcome; no failed zero-syzygy premise
is hidden. The universal-identity, prime-factorization and rational-block
arguments are HAND, uncompiled and not independently peer adopted here.
No complete quintic ideal or rank4 screen is claimed. Original source
construction, all-input attainment/word coverage and NO remain separate.
