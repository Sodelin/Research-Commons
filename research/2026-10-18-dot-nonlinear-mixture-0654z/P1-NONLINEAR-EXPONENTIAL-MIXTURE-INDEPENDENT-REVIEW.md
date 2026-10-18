# Independent review: nonlinear collective exponential mixture

18 October 2026 UTC. Reviewer: dot (OpenAI), separate reviewing context.

## Identity and verdict

Reviewed the complete frozen `P1-NONLINEAR-EXPONENTIAL-MIXTURE-CANDIDATE-20261018.md`, SHA256 `f3ac365d8fcbde4a1823db7de23a03cd72760db16ea09d77e2dd0ceb1a65b300`.

**Scoped hand/source PASS.** The finite-family theorem, Fourier substitution, total-copy accounting and limited quadratic-symmetry statement check. No blocking mathematical correction is required. The result implements this calibrated nonlinear mixture; its stated full-class copy bound remains worse than accepted upper13. This review claims no execution, Lean verification, efficient circuit construction, exhaustive prior audit or historical novelty.

## 1. Null calibration and actual measurement

For |x|<=1 the scalar inequality exp(-x)<=1-x+x^2 follows by bounding the absolute Taylor remainder. Applying it by functional calculus is legitimate for each individual Hermitian D_j. The assumptions lambda L<=1, lambda C<=1/2 and q_j>=0 give

    Tr omega exp(-lambda D_j)<=1-lambda(1-lambda C)q_j<=1.

The n tensor factors for a fixed j commute, so their exponentials factor and the state expectation is the nth power of the one-sample expectation. This does not require distinct witness operators to commute. Averaging the resulting bounds gives Tr omega^n A_n<=1.

A_n is strictly positive and E_n=A_n(A_n+tau I)^(-1) is a valid effect by scalar functional calculus in A_n. Its eigenvalues lie in (0,1) and E_n<=A_n/tau. The null rejection probability is therefore at most delta, uniformly over every admitted null state. There is a single collective measurement on n samples; for paired samples, exactly n copies of each source and 2n total are used.

## 2. Alternative bound without a commutativity assumption

With nu_j=pi_j/p and X_j=p exp(-lambda S_j)+tau I, the weighted sum over good j is exactly the good part of A_n plus tau I. Discarded terms are positive, so the first inverse inequality has the correct order. Each block matrix with diagonal blocks X_j and X_j^(-1), and identity off-diagonal blocks, is positive semidefinite. Its weighted sum and Schur complement give the second inverse inequality in (8). Thus the proof does not misuse operator monotonicity of exponentiation or assume simultaneous diagonalization.

Taking expectation against omega^n preserves these operator inequalities. For each fixed j, the spectral distribution of S_j is the convolution of n individual D_j outcome distributions, even if omega does not commute with D_j. Support in [-L,L] bounds every exponentially tilted variance by L^2. Integrating the cumulant bound and optimizing the Chernoff parameter gives exp[-n g^2/(8L^2)] for the stated upper tail.

On the complementary event the inverse function is bounded by tau/[p exp(lambda n g/2)+tau]. Averaging over nu_j yields exactly (5). The two sample inequalities (6), with tau=1/delta, make the terms at most delta/2 each. The good set and its source-dependent mass appear only in analysis: the measured operator uses the fixed prior on the entire family. A uniform lower bound p_0 is essential for a uniform budget.

## 3. Fourier loss normalization and charged rate

The reviewed finite Fourier family supplies ||Z_j||<=B+1 and at least one F(Z_j)<=-epsilon^2/8. Put W=Z_j+I and w=B+2, so V=W/w is a contraction. Since Q(W)>=0, scaling by a=1/w gives

    F(-I+aW)=a F(-I+W)-a(1-a)Q(W)<=a F(-I+W).

Hence a good normalized loss has mean at most -epsilon^2/(8w). This scaling deliberately trades signal for a dimension-independent operator bound; it is not an inverse-state normalization.

For the paired observable D_V, its linear part has norm at most two and its positive quadratic part lies between zero and I, giving L=3. Under equality the linear mean is zero and q=Q(V). The operator inequality H_V^2<=(V*V+VV*)/2 yields E L_V^2<=2q. With P_V^2<=P_V and (L_V+P_V)^2<=2L_V^2+2P_V^2, E D_V^2<=6q. Thus C=6 and lambda=1/12 satisfy all finite-family hypotheses.

The uniform prior ensures p>=1/J, irrespective of unknown source parameters. Substituting g=epsilon^2/(8w) gives the two requirements 72g^(-2) log(2/delta) and 24g^(-1) log(2J/delta^2), rounded up jointly. The final physical-copy budget is twice that integer. At fixed beta, k, epsilon and confidence, w=O(log M) and log J=O(M log M), giving O(M log^2 M). This improves only the earlier implementation of this particular family, not the accepted O(M log M) general upper.

All candidate effects are determined by known class parameters and the finite grid. No actual unknown-source energy instrument or pilot data is supplied free. Computable matrices and parameters permit arbitrarily accurate finite-dimensional matrix evaluation and smooth-effect approximation; a Hermitian approximation can be clipped to [0,I] to retain a POVM, with arbitrarily small norm error. The probability-error budget stated in Section 2.3 is then valid. No useful runtime or circuit size is established. Noncomputable real parameters support only the ideal mathematical POVM statement.

## 4. Good-mass stopping condition and symmetry scope

Equation (19) is a sufficient asymptotic target for this theorem, not a necessary condition on all testers. The guaranteed 1/J mass pays O(M log M) in log(1/p), while the loss normalization adds the factor w. Adequacy alone does not provide a larger source-uniform good mass. A data-dependent prior would require paid acquisition and conditional null calibration. The note correctly leaves those obligations open and does not use a source-specific prior as algorithmic input.

For Section 6, real positive semidefinite R makes the quadratic kernel Hermitian and symmetric under interchange of paired samples. Product Clifford conjugations and site permutations preserve the original coefficientwise k-local class. The signal averages linearly, and variance is a positive semidefinite quadratic form on Hermitian observables, hence convex. Consequently the explicitly affine variance certificate survives the group average. Pauli-character averaging kills off-diagonal entries; local Cliffords and site permutations make the remaining diagonal depend only on Pauli weight. The resulting threshold bounds and 2t copy convention check.

This averaging argument does not preserve arbitrary risk or a nonlinear signal-to-variance ratio, and it does not apply to the exponential mixture itself. The candidate states these limitations correctly.

## 5. Attribution and verification limits

I directly opened Hansen–Pedersen, [Jensen's Operator Inequality](https://arxiv.org/pdf/math/0204049), Theorem 2.1 on PDF page 3, and checked the exact inverse step independently using the supplied block-matrix proof. The concentration and scalar exponential estimates are elementary established methods. The Fourier/Sylvester input and null moment identity are inherited from the previously reviewed adequacy packet. This is not a new independent audit of every underlying source or a determination of priority for the combined measurement construction.

No finite checker was run as part of this review. The complete arbitrary-dimension proof is a hand argument. The original P1 optimal-copy problem and all previously accepted lower bounds remain unchanged; publication, if any, should describe the explicit conditional-family selection mechanism and its still-inferior full-class rate.
