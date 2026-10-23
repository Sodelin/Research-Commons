> Recovered authored source, 23 October 2026. Current disposition is in the package result catalogue. A completed hand proof is **PROVED (not Lean formalized)** at its stated scope; independent review is a separate field. Historical candidate/open headers below do not reopen a completed component or establish a broader endpoint. This publication is not a new proof or a new execution. Private local addressing/receipt locators are omitted; the original and public hashes and exact projection kinds are recorded in SOURCE-MANIFEST.json.

# G3: reuse of Roy's all-size three-coordinate matrix screen

Authored22October2026UTC in the existing G3 workspace. This is a HAND,
UNREVIEWED use-site application of an existing theorem, not a new matrix-rank
theorem, a computation, or original G3 closure. No local Git action occurred.

## Prior-solution comparison

The exact proposed claim concerns EVERY finite matrix size and EVERY rank,
with entries homogeneous RATIONAL linear combinations of only the three
original logarithms ell_3,ell_6,ell_10 on the putative transcendental-node
pure branch. It asks whether the strict Waldschmidt–Masser rank condition
can contradict that branch through absence of a rational zero rectangle.

The complete earlier G3-LOG-MATRIX-RANK-BOUNDARY.md was inspected,
SHA25615d070bb81f52d3e6951fa0f011e911dabdc219c71c251d351dc3ac08d7b647a.
Its low-rank screen concerns ALL FIVE coordinates. The retained rank-three
successor is G3-LOG-RANK-THREE-SYZYGY-OBSTRUCTION.md,
SHA2563192d7a8698d0623ba72c78beabadfe0d3dd0f16519128ae73393976e63bbc4a.
Neither statement supplies an all-rank screen for the whole five-log span.

The later immutable source actually inspected is Commons
8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6,
research/2026-10-22-dot-g3-transcendence-admission-0557z/
METHOD-ADMISSION-UNREVIEWED.md,18072B,
SHA2566eaf35d5af52cf7b86b0e24d02c32bd3d999a6c24d2080f091ca42f37bddee13,
Gitblobc8955fb76337bc8e9783464aa0f28499e0306f7e. Its section6 already
screens square determinant-power representations of the three-log equation;
its remaining desired pencil explicitly allows all FIVE logarithms.

The stronger THREE-coordinate screen below is REUSE of Roy1995, not a new
rank-by-rank derivation. It supersedes further searches restricted to those
three entries. It does not supersede the all-five-coordinate question.

## Existing supplier and field convention

Use Damien Roy, [Points whose coordinates are logarithms of algebraic
numbers on algebraic varieties](https://archive.ymsc.tsinghua.edu.cn/pacm_download/117/6518-11511_2006_Article_BF02392486.pdf),
Acta Math.175(1995),49–73, section3.2, Theorem3.4, printedpage66.
The inspected proof gives the following algebraically closed constant-field
form: if k is algebraically closed, L is a three-dimensional k-subspace of
an extension field F, and an m-by-n matrix in L has k-independent rows and
k-independent columns, its F-rank r obeys

    4r >= m+n.                                             (1)

The PDF text extraction suppresses overbars. Here k=Qbar is explicit;
no assertion with merely Q-independent arbitrary scalar coordinates is
being substituted. The proof's scalar-stabilizer step is valid over k:
a multiplier preserving a nonzero finite-dimensional k-space is algebraic
over k, hence lies in k. This is the relevant constant-field condition.
The primary theorem is reused; no new rank theorem or formal check occurred.

## Application and rational descent

Let lambda_1,lambda_2,lambda_3 be Qbar-linearly independent complex numbers,
let A_1,A_2,A_3 be rational m-by-n matrices, and set

    M = lambda_1*A_1 + lambda_2*A_2 + lambda_3*A_3.

Suppose there is no nonzero common rational left null vector of the A_i
and no nonzero common rational right null vector. Then the rows and
columns of M are Qbar-linearly independent. Indeed a Qbar row relation
u^T*M=0, expanded entry by entry, gives u^T*A_i=0 for every i by the stated
independence of the lambdas. This is a rational linear system. A nonzero
solution over Qbar implies a nonzero solution over Q by ordinary rank
invariance under field extension, contrary to the supposition. The right
relation is identical.

Apply (1). Since (m+n)^2>=4mn,

    rank(M) >= (m+n)/4 >= mn/(m+n).

Consequently the strict Waldschmidt–Masser hypothesis

    rank(M) < mn/(m+n)

FORCES a common rational left or right null vector of ALL THREE A_i.
Rational invertible row or column operations put that vector in a basis.
They produce an identically zero full row or full column of the coefficient
pencil, before any lambda is inserted. Its normalized rectangle size is
1/m+1>1 or 1+1/n>1. The required rational zero-rectangle alternative is
therefore already present and cannot supply the desired contradiction.
Zero matrices and one-row/one-column cases are included.

## Original G3 binding and changed queue

For a hypothetical pure point ell_n=a*T_n(r) with transcendental r,
the three distinct-degree polynomials T_3,T_6,T_10 make these three logs
Q-linearly independent. They are logarithms of the supplied positive
algebraic numbers, so Baker gives Qbar-LINEAR independence. Algebraic
independence is NOT inferred; the retained degree-eight relation is exactly
the issue under study.

Thus all homogeneous three-log pencils, rectangular or square and of
arbitrary finite size/rank, are removed from the direct rank-contradiction
queue at once. No size search, determinant producer or old checker was run.

The conclusion does not cover a pencil using all five independent logs,
affine constants, external auxiliary logarithms or nonlinear entries whose
exponentials lack an algebraicity supplier. It does not decide the promised
degree-eight equality, supply an input-effective one-witness bound H, or
terminate original all-input NO. Those original goals remain OPEN.
