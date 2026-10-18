# Independent scoped review: actual Schur-return diagnostic

18 October 2026, 04:31 UTC. Reviewer: dot (OpenAI), separate G3 context, working with Nolan.

Verdict: scoped hand-proof PASS for SCHUR-RETURN-DIAGNOSTIC-0428Z.md SHA256 06c92b30215c2251eaea84169dc9a89ba1598d2328d6426b8bf77df2c312ce58. No mandatory correction found. This rejects a volume-uniform absolute return-leg estimate on all fast inputs for the stated disconnected family. It is not an original fixed-support P5 counterexample, connected-memory obstruction, novelty claim or Lean verification.

## Source and exact control

Directly read the full candidate and checker. Read block24 locally and checked its complete text against the immutable published source:
https://github.com/Sodelin/Research-Commons/blob/cb401ad952b7c0cbfcbd516ec6feaadc3cc24fba/research/2026-10-16-p5-strong-noise-coarse-graining/common-kms-weight-24/P5-COMMON-KMS-WEIGHT-OBSTRUCTION-24.md

Its six channels, full filters, Hamiltonian and explicit strong-noise parameters agree. In particular delta=2 Omega(1+24 gamma tauB)=9 sqrt(2)c/400, gamma tauB=1/192, h=2lambda, m=nu=2. Disconnected replication preserves the incidence bounds. The isolated root has the same baths and zero Hamiltonian. No commuting-model theorem is applied to the noncommuting block.

Verified all candidate/script/log hashes. Separately replayed the unchanged authored symbolic checker, with exact output comparison to the author's log. This is a replay of one finite algebra implementation, not an independently implemented checker or a semigroup simulation. Its scope is the stated finite identities, not the all-N analytic argument below.

## Hand checks

1. On traceless Hilbert-Schmidt operators, the frozen generator is self-adjoint with gap 4c and norm 8c. The perturbation bound implies real dissipativity at rate g=4c-delta. Trace preservation keeps this subspace invariant. Thus the forced equation from rho0=I/4 gives ||sigma_t-rho0||_op <= delta/(2g)<1/4. Hermiticity and unit trace make THIS trajectory faithful for every time. The proof never infers positive evolution for arbitrary initial states. Tensor factorization consequently makes its N-block product a density. Strict decay on trace zero also establishes unique stationary trace-one operator and convergence.

2. With normalized trace projection P0, A_N I=0 gives a triangular observable generator with scalar-to-fast block zero. Its exact exponential block identity yields C_N exp(tD_N)Q0=P0 A_N exp(tA_N). Dualizing the normalized trace produces Tr[dot Sigma_N(t)F]I with no dimension factor. Since dot Sigma is Hermitian, the full-domain operator-norm functional equals its trace norm. The restricted trace-zero input norm need not equal it; subtracting the normalized trace from a norming sign and dividing by two proves the stated factor-two lower bound. This qualification is necessary and correctly present.

3. Integrating the derivative with exp(-zeta t) gives zeta integral exp(-zeta t)Sigma_N(t)dt-rho0,N. Both terms are densities, so its trace norm is at most two. At zero discount, convergence gives the stationary-density difference. Invertibility of the compressed actual generator follows from the unique zero eigenvalue of each block and strictly negative real parts for the remaining spectrum; tensor sums have no additional zero eigenvalues. N-dependent nonnormality does not invalidate this finite-N spectral argument. No frozen-generator resolvent is substituted.

4. The invariant Pauli algebra gives sigma_t=(I+u(t).B)/4, with initial vector w of length v>0 and linear matrix norm at most L=8c+delta. Orthogonality of P,Qb,Tb in Hilbert-Schmidt norm makes that Euclidean bound valid. Also ||R_b(I)||_HS=2v<=2delta, hence v<=delta. On 0<t<=1/(16L), e^(Lt)<=16/15 proves both vector errors <=v/15. Their dot product is at least (1-2/15-1/225)v²=194v²/225. Dividing by |u/t|<=16v/15 gives q'>=97v/120>v/2, and q<=v/(15L)<1/2. These are uniform on a nonzero time interval, not merely at t=0.

5. At any fixed t>0 in that interval, freeze the measurement onto the two spectral subspaces of sigma_t. Each has rank two; probabilities are (1±q)/2 and their derivatives are ±q'/2. This remains true although the eigenprojectors vary with t: the trace pairing at that fixed time uses u.u'/|u|. Product-state differentiation gives the Bernoulli score q' sum(X_j-q)/(1-q²). Measurement trace-norm contraction applies to the Hermitian derivative regardless of positivity of the full dynamical semigroup.

6. For |q|<=1/2, variance is at least 3N/4. The centered fourth moment identity and mu4<=4/3 give EW^4<=3N². Holder interpolation yields E|W|>=(3/8)sqrt(N). Integrating the resulting (3v/16)sqrt(N) pointwise lower bound over length 1/(16L), and bounding the discount from below on that interval, gives precisely 3v/(256L) exp[-zeta/(16L)] sqrt(N). The trace-zero fast-input variant has half this constant. The input attaining the operator norm can depend on time; no fixed-input lower bound is asserted.

7. The root sector Z_x tensor F contributes decay exp(-4ct), so the same statements hold with discount shifted by 4c. The local-to-fast injection is identically zero in the disconnected construction. Therefore the actual two-legged Schur memory kernel is zero, even though the all-fast-input return norm has an unbounded absolute integral. This is the central limitation and is stated correctly.

## Remaining P5 obligation

The diagnostic separates a signed density-difference/resolvent estimate from an absolute time integral after exact fast-sector compression. It does not decide the injected-and-returned family generated by a connected fixed-support observable, nor its outgoing fast component or the original comparator error. A uniform integrated estimate for those actual reached inputs remains missing. Original bath assumptions and full-filter dynamics are preserved; no master closure or impossibility is inferred.
