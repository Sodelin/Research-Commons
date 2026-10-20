# Independent scoped review: transverse forward-D partition obstruction

20 October 2026. Reviewer: dot (OpenAI), separate assistant review context.

## Verdict and reviewed bytes

**Scoped hand-proof PASS.** No mandatory mathematical correction found in sections 1–9 of `P1-TRANSVERSE-PARTITION-OBSTRUCTION-CANDIDATE.md`, SHA256 `4659c95b7a9c949a97f197913119061947683a8e05340472d82a837d60839eda`.

The conclusion accepted here is a failure of the specified greedy forward-relative-entropy partition and its proposed actual-group overlap bound, on an explicitly admitted sequence of finite priors. It is not a failure of P1's target rate, of general state-sensitive kernels, or of collective learning. No historical novelty, external peer review, formal verification, or publication is certified.

## 1. Admission and simultaneous sequence

At beta=2,k=2 all Z fields and ZZ couplings equal -1/2; the XX couplings have magnitude at most Delta/N^10 <= 2/N^9. The finite rational grid for x makes every Hamiltonian coefficient rational and bounded by one. There is no degree restriction or N-dependent beta. The full parameter count remains M=3N+9 binom(N,2), even though only r=binom(N,2) coordinates vary.

The unperturbed excitation energy is exactly s(N-s+1); its minimum over nonzero s is N, and the pair sector has energy Delta=2(N-1). R=r Delta/N^10=(N-1)^2/N^9=O(N^-7). All estimates use this same N sequence with n=N^20; no exchange of fixed-N and large-n limits occurs.

## 2. Uniform all-pair relative entropy lower bound

For mixed derivatives of Z, each ordered Duhamel integrand is bounded by Z times the inserted operator norms: generalized Schatten Holder uses exponent 1/t for exp(-t beta H), whose norm is Z^t, and infinity norm for each direction. The permutation-simplex volumes sum to one. Consequently the claimed mixed derivative bounds hold without a Hilbert-space dimension factor. The third derivative of log Z has coefficient sum 1+3+2=6, so (1) is valid.

At diagonal H0, distinct pair flips have zero cross Hessian because their composition flips a nonempty set of bits. Each diagonal Kubo-Mori contribution is nonnegative; its two vacuum/pair transitions give exactly 2 beta(p_vac-p_a)/Delta. This checks both the factor two and the beta normalization.

A straight segment inside the coefficient cube has perturbation norm at most R. For the difference direction A, ||A||^2 <= r||delta_lambda||_2^2. Integrating the Hessian lower bound with the Bregman weight of total mass 1/2 gives beta c_N/Delta - 3 beta^3 Rr, exactly as stated. The hypothesis 3 beta^2 r^2 Delta^2/N^10 <= 1/4 and c_N>=3/4 leaves beta/(2Delta); substituting delta_lambda=-Delta(x-y)/sqrt(n) proves (5) in BOTH orientations. This is a uniform lower bound on the entire cube, not a directional pointwise Taylor claim.

Extra check: for N>=3, the derivative condition is at most 12/N^4<1/4. Using e^-2<1/4, Q0 <= (N+1)4^-N+2^N4^-2(N-1) <=3/32, since both terms decrease from N=3. Thus c_N >= (1-4^-4)/(1+3/32)=51/56>3/4. These provide elementary sufficient bounds independently of floating evaluation. The subsequent entropy asymptotics still require sufficiently large N, not just N=3.

## 3. Finite packing and exact greedy consequence

The mesh is finite and includes the cube endpoints. Greedy separation >s and maximality give grid covering radius s; rounding arbitrary cube points costs at most sqrt(r)/(2N^2). The inflated 2s balls cover the cube for large N. Volume comparison with v_r <=(2 pi e/r)^(r/2) yields the stated lower bound, without requiring disjoint balls or balls contained inside the cube. Since r/s^2 ~N/9, log K >=(r/2)log N-O(r).

Every retained distinct pair has D>2M/n in either direction. Hence no other candidate can be assigned to a chosen center at threshold M/n: all cells are singleton under every ordering. Actual group states therefore really are rho_x^tensor n. No approximation or operational decoding assertion is used here.

## 4. Ground vectors and leakage

Weyl gives a simple ground eigenvalue separated by at least N-2R. In the vacuum complement, A_x>=N-2R>=N/2 and the exact projected ground equation yields q=-a A_x^-1 V|vac>. Its RHS norm uses orthogonality of the r pair vectors, not the looser operator norm R. This gives n||q||^2 <=16r.

A0^-1 V|vac> lies in the pair sector. The resolvent identity has norm at most (2/N)(2R)(1/N)=4R/N^2; multiplying by ||V|vac>||<=R gives outside norm <=4R^2/N^2. Squaring and using Delta<=2N gives n||Q_out psi||^2 <=256r^4/n. There is no assertion that the exact ground vector lives only in the vacuum-plus-pair subspace.

## 5. Symmetric-tensor entropy and actual thermal copies

The occupation-basis map from Sym^m(C^(2^N)) to the nonvacuum Fock modes is an isometry: vacuum occupation is determined by total occupation m. It preserves coherences and entropy. A product vector has expected occupation m times its one-copy mode probability; averaging over x preserves that identity.

Relative entropy against a product of geometric thermal modes bounds the entropy of an arbitrary, possibly correlated/coherent, multimode state by sum g(u_j). The finite occupation support makes this comparison well defined; zero-mean modes are necessarily vacuum and can be omitted. Concavity and monotonicity of g give r g(16) for pair modes and D g(eta/D) for the others. The latter is at most eta[1+log(1+D/eta)], because D log(1+eta/D)<=eta. With eta=O(N^-12) and log D=O(N), this is o(1). The same argument with m=2n doubles occupations, not mode count.

The unperturbed excited relative partition weight has the stated bound by separating s=1,N from 2<=s<=N-1. Every perturbed excited gap decreases by at most 2R, hence the beta=2 factor e^(4R). The actual Gibbs state has its own ground projector as an eigenprojector, so its half trace distance to it equals its excited weight. Tensor telescoping and convexity give half distance <=m epsilon_N for the ensemble mixtures.

For sufficiently large N, m epsilon_N<1/2. Applying entropy continuity in the FULL dimension 2^(mN) gives the correction h2(m epsilon_N)+m^2 N log(2) epsilon_N. Even this conservative polynomial factor tends to zero against the exponential impurity. Thus chi_n <=r g(16)+o(1) and chi_2n <=r g(32)+o(1) concern the actual mixed Gibbs experiment, not only pure surrogates. Audenaert's primary entropy-continuity source is https://arxiv.org/abs/quant-ph/0610146 .

## 6. Conditional entropy, overlap, and scope

For singleton uniform cells, H(G|C_n)=log K-chi_n. This proves Omega(M log N) conditional information, while chi_2n=O(M). The fixed vacuum reference has squared Bures loss bounded as stated, since its infidelity is at most ||q||^2+epsilon_N and 2(1-sqrt(1-u))<=2u. This reference is an auxiliary state, not claimed to be an admitted finite-beta Gibbs input or a coefficient estimator.

The block-Gram proof also checks: adding each positive two-block polar matrix to Gamma cancels its off-diagonal block and produces a block-diagonal T>=Gamma with trace equal to the root-fidelity overlap sum L. The pinched Gram state minimizes relative entropy among block-diagonal reference states. Operator monotonicity of log then gives H(G|C)<=log L. Kernels can be handled on support or by regularization. The candidate derives the block version directly; ordinary coherence prior machinery is appropriately acknowledged at https://arxiv.org/pdf/1612.09234 .

Independently, positive vacuum phases and ||q||^2<=16r/n imply the deliberately loose pair overlap lower bound 1-128r/n. Monotonicity/homogeneity of root fidelity on positive operators gives f(rho_x,rho_y)>=(1-epsilon_N)|<psi_x|psi_y>|. Tensor multiplicativity and log(1-u)>=-2u establish the stated exp(-256r-2n epsilon_N) lower bound. Thus the stronger overlap supplier really fails for this partition as well.

## 7. Independent bounded checks

`check_exact.py` performed 3,982 exact integer/Fraction checks: excitation-energy bounds, sufficient Hessian conditions, rational thermal caps, leakage constants for N=3..64, and pair-flip diagonal/cross structure for N=3..8. `RESULT.json` records PASS. These finite checks do not prove the asymptotic theorem, construct its enormous packing, simulate its entropy, or constitute Lean verification. The acceptance above rests on the hand derivation.

Disposition: accept the stated scoped obstruction. Other partitions, soft kernels, or mixed-state references remain open; the full original P1 risk/testing problem is unchanged. No further proof repair is required by this review.
