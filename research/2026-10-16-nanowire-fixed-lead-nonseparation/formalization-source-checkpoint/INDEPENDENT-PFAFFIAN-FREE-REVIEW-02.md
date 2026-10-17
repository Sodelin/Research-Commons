# Independent hand review of the Pfaffian-free all-channel route

17 October 2026, 01:33 UTC. dot (OpenAI), working with Nolan.

Reviewed: `LEAN-PROOF-ROUTE-AUDIT-01.md`, SHA256 `3f48810d0050e87d1f3567df21a3ad0d35d30a986e60798e5a5f59ea33600f25`.

**Scoped hand-proof PASS.** The necessary inequalities and explicit full-region attainment route are valid for every finite N>=1. No blocking mathematical defect found. This review does not claim Lean compilation, an independently re-audited Mathlib inventory, new numerical execution, novelty, or microscopic wire realization.

## Necessity

1. **SVD parameters stay fixed.** For the given real contraction M, fix orthogonal U,V and its singular values s once. The interpolation function varies only the diagonal coordinates t in U diag(t) V^T, keeping U,V and therefore F=U^T J U, G=V^T J V fixed. Negative cube coordinates are legitimate: every cube vertex produces a real orthogonal matrix, which has a corresponding unitary PHS matrix. They need not be singular values of the original M.

2. **No hidden squared coordinate.** With the half-Frobenius convention, cyclic trace gives N-g=(1/2) sum_ij F_ij G_ij t_i t_j. Both F and G are antisymmetric, so diagonal terms vanish exactly. Each remaining monomial has distinct indices, and det(U diag(t) V^T)=det(U)det(V) product_i t_i also contains every coordinate only once. Thus Q-(N-g)+N-1 is separately affine, including N=1. Its value at any point of [-1,1]^(2N) is the convex multilinear interpolation of its vertex values. This is an all-finite-dimension argument; no fixed bound or approximate reduction occurs.

3. **Unitary Schur step.** AB^T+BA^T=0 implies A^{-1} B A^T=-B^T when A is invertible. Therefore (conj A-conj B A^{-1}B) A^T=conj A A^T+conj B B^T=I. The block determinant is det(A)/det(A^T)=1, with no unproved sign choice or conjugate determinant cancellation. Consequently Q=-1 implies A singular. Since A is square, A^dagger is singular too. Choose a unit v in its kernel; AA^dagger+BB^dagger=I gives ||B^dagger v||^2=1, hence ||B||_F^2>=1. With g=2||B||_F^2, Q=-1 gives g>=2. Q=+1 uses g>=0. These establish Q>=1-g at every vertex and hence every contraction.

4. **Other bounds and hole exchange.** Orthogonal vertices have 0<=g<=2N and |Q|=1. The same separate affinity proves those scalar bounds throughout the cube. Swapping outgoing electron/hole rows preserves PHS and contraction, sends g to 2N-g, and multiplies determinant by (-1)^N. Applying the lower bound to the swapped matrix gives precisely the high-edge inequality. Singular original M requires no division and causes no exception in interpolation.

## Sufficiency

5. **Two-mode block.** Direct hand multiplication confirms orthogonal second/fourth columns, squared column norms q^2,1,1,1, determinant q, and adjacent covariance entries qc and c. Thus the displayed block is contractive for |q|<=1 and c^2+s^2=1, and contributes conductance 2-(1+q)c. No square of q enters the conductance expression.

6. **Even N.** One q-block plus N/2-1 unit-determinant blocks gives determinant q and g=N-(N-1+q)c. The coefficient D=N-1+q is nonnegative. If D>0, the claimed region is exactly |N-g|<=D, so the specified quotient c lies in [-1,1]. D=0 occurs only at N=2,q=-1; the region then forces g=2 and c=0 is valid. In particular the flat extreme q=-1 is attained, not approached in a limit.

7. **Odd N.** The one-mode diag(q,1) block contributes determinant q and conductance 1-q. The remaining (N-1)/2 positive blocks contribute (N-1)(1-c), giving the stated formula. For N>1 the interval condition gives |c|<=1. N=1 has no paired blocks and exactly g=1-q, for every q in [-1,1], including q=0 and q=+-1.

8. **Endpoints and exact complex witness.** Choosing s=sqrt(1-c^2) is valid at c=+-1 as well as in the interior. Direct sums multiply determinants, add conductance and preserve contraction. Reversing the fixed Majorana basis yields actual canonical PHS complex matrices with the same determinant and conductance. This establishes every point in the full algebraic region without a connected-fibre or Pfaffian argument.

## Formalization boundary

The route is a complete alternative hand argument, but its Lean dependencies remain genuine obligations: zero-mode SVD realization, basis conversion and normalization, Schur/norm lemmas, expression-level coordinate affinity, direct-sum index equivalences and exact witness construction. A compiled generic cube lemma alone would not discharge those bindings. I did not inspect or execute the proposed Lean module or verify installer state in this review. No installation or compilation was attempted.
