> Recovered authored source, 23 October 2026. Current disposition is in the package result catalogue. A completed hand proof is **PROVED (not Lean formalized)** at its stated scope; independent review is a separate field. Historical candidate/open headers below do not reopen a completed component or establish a broader endpoint. This publication is not a new proof or a new execution. Private local addressing/receipt locators are omitted; the original and public hashes and exact projection kinds are recorded in SOURCE-MANIFEST.json.

# G3: exact boundary of a broader logarithm-matrix route

Authored22October2026UTC in the existing G3 workspace. HAND proofs below;
the finite quartic calculation has its own actual verification. No original
G3 completion, theorem-of-absence, new model run or Lean acceptance is claimed.
No local Git action occurred.

## The controlling original implication

The complete inherited [three-log purity reduction](https://github.com/Sodelin/Research-Commons/blob/9d21c0727564ae0ba101039d97b07c614d17f2e1/research/2026-10-10-dot-g3-three-log-purity-1210z/THREE-LOG-PURITY-REDUCTION.md)
was reread, not inferred from its title. Its Git blob is
6f6c389d223e5056738a6c3c8399ecaa62eebdac. Under its FULL five-coordinate
cone promise, purity is the original all-source COMMON **NO** branch and
nonpurity is the finite-source YES branch. Thus algebraicity of a parameter
in a fixed finite physical YES chart does not prove that a pure node must
be algebraic: that argument would put a physical witness in the NO branch.

Write n in {3,6,10,15,21}, ell_n=log(b_n), with the stated positive algebraic
inputs and promise. The surviving putative pure branch has

    ell_n=a*T_n(r), a>0,
    T_n(t)=sum[k=0..n-2] (n-1-k)*t^k,

where r is in the promised compact interval. The inherited exact polynomial
in three logarithms vanishes precisely on the promised pure branch. Positive
distance can be semidecided by approximations; an exact-zero procedure has
not been supplied. The transcendental-r, five-independent-log branch remains
unexhibited and unexcluded here.

This note concerns that arithmetic gate. It does not replace actual source
reflection, all-input attainment or unrestricted NO coverage by a log-curve
membership declaration.

## What the broader theorem actually requires

For an m-by-n matrix of logarithms of algebraic numbers, the
Waldschmidt–Masser theorem in [Dasgupta, Theorem1.6 and Section5.1](https://sites.math.duke.edu/~dasgupta/papers/Baker.pdf)
uses the strict bound rank(M)<mn/(m+n). Its conclusion is a zero rectangle
after invertible RATIONAL row and column operations, with dimensions m',n'
satisfying m'/m+n'/n>1. A singular square matrix need not meet that bound.
The same source's structural-rank statement is a conjecture; its arbitrary
affine determinantal representation lemma does not make it a proved rank
comparison. Only the named introduction/Sections4.3/5.1 were reviewed,
not the entire45-page paper.

The [Dasgupta–Kakde2024v1 paper](https://arxiv.org/html/2408.08178v1)
distinguishes its Matrix Coefficient Conjecture from proved implications;
its two-by-two case includes the four-exponentials conjecture. This review
does not promote the stronger rank criterion or an unfinished implication
in that version into a G3 proof, or claim a complete2026 literature survey.

The matrices screened below have entries in the RATIONAL linear span of
the five ell_n. Such entries are again real logarithms of positive algebraic
numbers. No additional auxiliary logarithm or constant1 is introduced.

## New lemma: every rank-at-most-two attempt already has the rectangle

Let X=(X_1,...,X_5), let L(X) be any m-by-n matrix of homogeneous rational
linear forms, and suppose r is transcendental. Set T=(T_3,...,T_21).
The earlier finite certificate (owner-retained reference: `check_log_curve.py`) proves that homogeneous
monomials of degrees1,2,3 in T are independent over Qbar. It is reused here;
those degrees were not recomputed.

**Claim.** If s=rank L(T(r))<=2, then the generic rank of L(X) is s.

Every (s+1)-minor vanishes at T(r). Transcendence first makes its substitution
in T(t) a polynomial identity; degree-(s+1) independence then makes that
minor the zero polynomial in X. Conversely, an s-minor nonzero after
substitution is nonzero before substitution. This proves the claim, including
the zero-rank case.

Choose x0 in Q^5 with rank L(x0)=s; such a point exists because a nonzero
rational minor cannot vanish on all Q^5. Rational row/column operations put
L(x0) in rank normal form diag(I_s,0). For every y in Q^5, every (s+1)-minor
of L(x0)+h*L(y) is identically zero. The minor on the first s pivot rows/
columns and one additional row/column has linear h-coefficient equal to the
corresponding entry of L(y)'s bottom-right block. Hence that entire
(m-s)-by-(n-s) block is identically zero for every y, and therefore for L(X).

If the strict Waldschmidt–Masser bound holds, this rectangle has

    (m-s)/m+(n-s)/n = 2-s*(1/m+1/n)>1.

It already exists in the rational coefficient pencil. Applying the theorem
to a*L(T(r)) therefore returns a relation which is true identically before
any logarithm is inserted. It supplies no contradiction to this putative
pure branch. This screens ALL homogeneous rational-linear matrix sizes of
rank0,1,2, not just the previously screened rank-one two-by-three shape.
It does not screen higher rank, affine constants or auxiliary logarithms.

## New width bound and the entire four-row rank-three case

Let V be any k-dimensional rational subspace of Q(t), and let B(t) be an
m-by-n matrix with entries in V and rank<m. Suppose

    n>(k-1)*(m-1).                                      (1)

Then B already has a rationally transformed zero rectangle of the strict
Waldschmidt–Masser size. This assertion is elementary and does not use a
transcendence theorem.

Choose a nonzero left null vector f in Q(t)^m and let d be the dimension of
the rational span of its components. A constant rational row change puts
this null relation in the first d rows, with independent coefficients
f_1,...,f_d and zero coefficients on the remaining rows. Let F be their
span. The projection of each column onto these d rows lies in the kernel of

    V^d -> Q(t), (v_i) -> sum_i f_i*v_i.

The image is F*V and has dimension at least d+k-1. To see this without a
product-space theorem, clear denominators and choose bases of F,V with
distinct polynomial degrees. Their product degrees contain the sum of the
two degree sets, which has at least d+k-1 distinct integers. Corresponding
products are independent. Thus this kernel has dimension at most
(k-1)*(d-1).

A rational column change therefore kills the first d rows on at least
n-(k-1)*(d-1) columns. The resulting rectangle satisfies

    d/m + [n-(k-1)*(d-1)]/n > 1,

because (1) implies n>(k-1)*m*(d-1)/d for every1<=d<=m. All these are
identically zero rational functions, so specialization at transcendental r
and multiplication by the same nonzero a preserve them.

For our k=5, a genuinely new matrix route must therefore have both

    n<=4*(m-1), m<=4*(n-1).                            (2)

For m=4 and rank3, the strict arithmetic threshold requires n>12, whereas
(2) requires n<=12. Thus **every four-row rank-three attempt** is also
already explained by an identically zero rational rectangle. The transpose
is included. The first shapes not screened by these lemmas include5-by-8
and6-by-7 of rank3; the first square is7-by-7. This is a narrowed next target,
not a constructed matrix, a proof that one exists, or an exclusion of all
higher-rank constructions.

## Exact new quartic calculation

The70 homogeneous quartic monomials in T give a77-by-70 integer coefficient
matrix. Unlike degrees1–3, its exact rank is61 and its kernel dimension is9.
The earlier modular deficiencies alone did not establish this.

check_log_curve_quartics.py (owner-retained reference: `check_log_curve_quartics.py`) reuses the original
polynomial constructor and computes an integer kernel by fraction-free
elimination and rational back-substitution. It verifies all9 vectors against
the ORIGINAL matrix. Distinct nonzero free coordinates prove their
independence. A61-by-61 minor has determinant956015 modulo the previously
certified prime1000003, giving the complementary rank lower bound. These
certificates prove the exact rank and remain valid over Qbar.

Actual phone execution passed in under a second. Complete basis, row/column
indices, source/dependency hashes and result are encrypted at

    [owner-local path omitted]
    ciphertext SHA256 4dca0fc393a48a560740854f43f436d4f2142ca3df3bd0d485428197608adf67.

A separate Wolfram exact-kernel calculation returned the same rank/nullity
and zero products. Its formatted long basis was elided by that interface;
it is not advertised as a complete exported basis. The complete phone
certificate is the reproducible record above. The first phone revision
failed when an empty sum became a float; Fraction(0) fixes that denominator
collection. The failed source/reproduced traceback and received Wolfram
response are retained, encrypted:

    [encrypted runtime receipt retained privately]
    ciphertext SHA256 1a2cef609f000ef5a59374ccbc43da6f7fd549764208d1f15c1039cf6a9dd52e.

The degree4–6 modular lower-bound exploration is retained separately as
[encrypted runtime receipt retained privately]/ciphertext
6cef55ad643ae77bb58f87b3318788ffd3df6d994a920096c4e00a9a623db405.
No exact degree5/6 rank or complete defining ideal is claimed. In particular,
the9 quartics do not themselves construct a rank-three matrix satisfying
the strict theorem, or justify algebraic independence of the logarithms.

## Remaining implication and bounded next action

The exact promised zero test is still missing. A broader matrix attack would
now need an ACTUAL rational-linear matrix of rank at least3, satisfying the
strict bound and violating its rational-zero-rectangle conclusion; the
smallest eligible shapes above would need new quartic-level structure.
The two lemmas remove large families of futile candidates. They do not
turn the stronger structural-rank conjecture into an available theorem.

Keep this arithmetic branch separate from the useful original-source work:
actual whole unused-bank/prefix independence, full current-root grafting and
finite fixed-fibre consumers do not decide this global COMMON gate. General
G3 remains ACTIVE and OPEN; the next work must supply a real arithmetic or
all-input source/NO mechanism rather than repeat a failed rank-one screen.

Primary-source review/source packets were encrypted before persistence in
records19888/19892/19903, exact basenames and ciphertext hashes in the current
continuation index. No private record was uploaded. All source/native-writer,
held/consumed-job, no-subagent and no-local-Git boundaries remain.
