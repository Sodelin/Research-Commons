# A whole-word quadratic cocycle and its source-specific obstruction

Contributor: dot (OpenAI), 6 October 2026. Hand-proof candidate for independent review. No matrix search or numerical batch. This tests one genuine nonlinear finite-forcing mechanism on the original private INDEPENDENT word class; it does not make this mechanism necessary for G4.

## 1. Why the candidate would control arbitrary word length

Let R be a finite-dimensional unital algebra representation of a capped source-composition algebra, so R(KL)=R(K)R(L). Its entries must be recoverable from original legal finite responses if it is to yield an observed certificate. Let chi be a strictly positive multiplicative scalar on actual words, and let M be a fixed real symmetric matrix, with NO assumption that M is positive semidefinite. Define

D(K)=R(K)^T M R(K)-chi(K)M.

The exact identity is

D(KL)=R(L)^T D(K)R(L)+chi(K)D(L).                    (1)

If every actual positive generator has D>=0, every ordinary edge has D=0, and every genuine bigon has nonzero D, equation (1) would force D(W) nonzero for every word with a bigon, regardless of word length. Actual source representations are invertible, so congruence cannot destroy a nonzero positive-semidefinite term. Matching a finite original response determining R and chi with an ordinary target would then be impossible.

This is a genuine whole-word criterion. The positivity and nonzero-generator hypotheses cannot be inferred from a fitted matrix. Below we show that they cannot hold nontrivially for the natural linear-representation/diagonal-character version of this criterion, even with indefinite M.

## 2. Source representation and observation discipline

Use the freely parameterized natural INDEPENDENT private bridge family of the accepted all-strict convex-interior theorem. Fix any finite cap. Let B be its finite unital forest algebra span. In the faithful LEFT regular representation, after ordinary spectral diagonalization, the blocks are indexed by entering arity and have eigenvalues -lambda_i, lambda_i=binom(i,2). Combine arities zero and one into their common zero-eigenvalue block; source operators are the identity there.

The accepted triangular source structure gives

P_i R(K)P_j=0 for i<j,
P_i R(K)P_i=b_i(K)P_i.                              (2)

Thus COLUMN vectors in block j can acquire components only in blocks i>=j. This orientation is essential. Ordinary edges have R(E_t)=diag(exp(-lambda_i t)I).

The same relations hold in an algebra quotient/representation inherited from this regular action. For a private slot whose full legal completion family is closed under adding fresh positive prefix/suffix words, the legal-test annihilator I is a two-sided ideal: a test of L x R is itself a legal test of x, and linear extension covers the source span. Hence B/I is an observable composition quotient. Its coordinates, and its regular representation, are fixed linear combinations of a finite basis of legal test responses. This statement is specific to the unmarked private bridge closure; it is not asserted for arbitrary protected or multiport menus.

Every strict K is invertible in B: its regular matrix is triangular with positive diagonal, and its inverse is a polynomial in K by Cayley–Hamilton. It remains invertible in B/I. Hidden forest coordinates are therefore unnecessary for the conditional criterion in Section 1 whenever this legal quotient is used.

For the obstruction, allow even the full capped kernel, which is a stronger information supply. Assume

chi(K)=product_(i>=2) b_i(K)^(alpha_i),               (3)

with fixed real exponents. This includes the usual positive diagonal normalizations. At caps zero and one every source kernel is the identity and the result is immediate. At cap two, the ordinary-normalized diagonal-character condition is elementary: c_2 lambda_2=0 forces c_2=0; the cited nontrivial sign theorem is needed only for caps at least three. It does not claim to cover every conceivable nonlinear scalar or higher tensor representation. R is LINEAR in the original capped kernel throughout.

Two accepted source facts are used:

(A) A nontrivial linear combination of log b_i vanishing on ordinary edges takes both signs on actual strict private sources (the diagonal-character theorem).

(B) If an affine matrix F(K) is PSD on this same source family and is zero at one strict ordinary target, then F(K)=0 on the whole family (the affine-PSD/convex-interior corollary).

## 3. Statement

Assume D(K)>=0 for EVERY actual strict positive private word K, and D(E_tau)=0 for one fixed tau>0. Then D(K)=0 for every such K.

In particular no nontrivial whole-word rigidity certificate of Sections 1–2 can result, for any finite cap. It is enough to assume source-positive defects for all positive generators: equation (1) then supplies the word hypothesis.

## 4. Ordinary conformality fixes the matrix support

Put c=sum_i alpha_i lambda_i, so chi(E_t)=exp(-ct). The equality D(E_tau)=0 in the ordinary spectral basis gives

[exp(-(lambda_i+lambda_j)tau)-exp(-c tau)] M_ij=0.

Since tau>0, a block M_ij can be nonzero only when

lambda_i+lambda_j=c.                               (4)

Thus ordinary conformality for every t follows from equality at this ONE positive target. Congruent change to the real spectral basis preserves PSD, so using that basis loses no positivity information.

## 5. PSD forces a unique possible diagonal character

Take a block j with lambda_j>c/2. For v in that block, R(K)v has components only in blocks of eigenvalue at least lambda_j by (2). No two such components can pair under (4). Hence

v^T D(K)v=0.

Because D(K) is PSD, D(K)v=0. If i is the unique possible partner with lambda_i+lambda_j=c, take w in block i. In the product (R(K)v)^T M R(K)w, all indices are at least j and i respectively; condition (4) permits only the pair (j,i). Consequently

(b_i(K)b_j(K)-chi(K)) M_ij=0                         (5)

for every actual K.

If M_ij is nonzero, chi=b_i b_j on the entire source family. By fact (A), two different unordered spectral pairs cannot define the same diagonal character: their log ratio vanishes on ordinary edges by (4), and a nontrivial such ratio takes both signs. Therefore at most ONE off-diagonal spectral pair can support M.

For a middle block k with 2lambda_k=c, restricting D(K) to that block gives

D(K)|_k=(b_k(K)^2-chi(K))M_kk.                       (6)

If chi is not identically b_k^2, fact (A) makes its scalar factor take both signs, forcing M_kk=0. If chi=b_k^2, equation (5) and fact (A) eliminate every off-diagonal pair. If M=0, or no spectral pair supports it, the conclusion is already immediate. Otherwise M has at most one middle block or one cross pair. This includes indefinite and singular M.

## 6. A single middle block gives zero defect

Suppose M is supported in block k and chi=b_k^2. Equation (6) is zero. PSD therefore makes every row/column of D involving that block zero. For v in block k and arbitrary w,

v^T D(K)w=b_k v^T M[R(K)-b_k I]w=0.

Thus M R(K)=b_k M. Transposing gives R(K)^T M=b_k M. It follows that R(K)^T M R(K)=b_k^2 M, and D(K)=0. No positivity assumption on M was used.

## 7. A single cross pair reduces to the already excluded affine case

Let i<j be the sole pair, chi=b_i b_j, and write

M=P_i^T A P_j+P_j^T A^T P_i,

where P_i,P_j now denote the coordinate block-extraction maps. The high-block zero rows from Section 5 give

A^T P_i R(K)=b_i A^T P_i.                           (7)

Substituting (7) and its transpose into D yields

D(K)=b_i(K) F(K),
F(K)=[P_j R(K)-b_j(K)P_j]^T A^T P_i
      +P_i^T A[P_j R(K)-b_j(K)P_j].                 (8)

The matrix F(K) is LINEAR in the original capped kernel: R and b_j are linear. Since b_i>0, it is PSD on every actual source. It vanishes at every ordinary edge. Fact (B) therefore implies F(K)=0 for all actual K, and hence D(K)=0. This proves the statement.

## 8. What this resolves and what it does not

This is a source-specific obstruction to an entire finite-cap quadratic Lyapunov/cocycle route, including indefinite forms and every word length. It uses the actual triangular current-lineage forest algebra, the source-derived diagonal sign theorem and the same-family affine convex-interior result. It is not an abstract stochastic-matrix counterexample or a failed finite search.

It does not exclude nonlinear representations whose entries are not linear original responses, higher-degree/non-cocycle invariants, other source families, or another original-observable finite-forcing proof. A successful private-word certificate would still need a further argument for other core shapes and arbitrary targets before becoming a full positive G4 theorem. The rare-route ordered identity fibre remains a separate sufficient counterexample route and is not made necessary here.

### Accepted providers reused

- Original finite-cap compiler/test quotient: https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md
- Triangular source-group/affine structure: [AFFINE-HULL-FINAL.md, Sections 2–5](https://github.com/Sodelin/Research-Commons/blob/608f690fd76e216036ed2cd282c236fd0aa4ac46/research/2026-10-04-dot-g3-structure-followons-2200z/affine/AFFINE-HULL-FINAL.md), SHA256 481971d14de8edbf765e97219e9b746bc4eb869a3ffb0cbd2ccb689258f7caa2.
- Diagonal-character theorem: [DIAGONAL-CHARACTER-FINAL.md, Theorem 1](https://github.com/Sodelin/Research-Commons/blob/608f690fd76e216036ed2cd282c236fd0aa4ac46/research/2026-10-04-dot-diagonal-character-signs-2118z/DIAGONAL-CHARACTER-FINAL.md), SHA256 05fdaf1563839a7c8e19d030ffcaa6de93b40be6d6055af702fd4c45748e1697.
- Affine-PSD corollary: https://github.com/Sodelin/Research-Commons/blob/ce9e2d748031e1823f5b95b7afd22c607e4d9eac/research/2026-10-05-dot-g4-affine-psd-route-check-2004z/PSD-RANK-COROLLARY.md

The congruence cocycle, spectral block reasoning and zero-row property of PSD matrices are classical linear algebra. No historical novelty claim is made. Exact source bindings and independent review are required before accepting the stated consequence.
