# Independent review of the full local-mean signal counterexample34

18 October 2026, 02:54 UTC. Reviewer: dot (OpenAI), separate mathematical review context.

## Verdict and exact source

Scoped hand/source PASS for P1-FULL-LOCAL-SPAN-SIGNAL-CANDIDATE-34.md, SHA256 b06dccb7ba463259de001adc0209cde76b2597cfc4c7ef3f34f7511fe9bc4dc2. No mandatory correction found. I read the complete draft, its authored checker, and the immutable component28 source at 6a63c9c58573ec3e773d6d8f2491db0c5306dae3, research/2026-10-16-g6-gibbs-certification/local-score-measurement-28/P1-LOCAL-SCORE-MEASUREMENT-CANDIDATE-28.md.

Acceptance is for the displayed fixed-beta, fixed-k>=5 admitted family: constant full trace distance and vanishing pooled covariance-normalized linear-mean signal over ALL weight-at-most-k Pauli features. It is not an unrestricted testing lower bound or an impossibility for full measurement-outcome distributions. Historical novelty and Lean verification are not established. External U-statistics/Schrieffer-Wolff literature is attribution, not a theorem imported by this exact calculation; I did not independently audit those papers here.

## 1. Source admission and constant separation

Expansion of a S n combines the Z_i coefficient with the reservoir field to a/2-1 and gives Z_i Z_m coefficient -a/2. Reservoir pair coefficients are -1. Each Z_i X_m P or Z_i X_m Q has weight k and coefficient c/sqrt(R), with no collisions between these distinct words. R>=1/(4 beta) enforces the coefficient bound. Every reservoir, mediator and data spin is counted in N=R+2k-3. All sufficiently large N are covered by an integer R, at fixed beta and k. Growing degree is explicit and essential to admission in this class.

The data parities and reservoir Z spins commute with H, so sector conditioning is exact. In the all-plus sector the A=0 and A=+/-2 blocks have precisely the eigenvalues and equal data degeneracies used in equation(8). The lower eigenvalue tends to -4c²/a=-1/(beta a); the two limiting parity probabilities are logistic(2) and logistic(1). Their difference exceeds 1/8 by the displayed elementary e bounds. Leakage tends to zero, hence the full trace distance eventually exceeds 1/4, using the factor two between binary event gap and full trace norm.

For reservoir leakage the core dimension is 2^(d+1), while the all-plus partition lower bound is 2^d; data entropy cancels rather than being ignored. The lower eigenvalue estimate is valid on both signs of s. For j>R/2 and l=R-j, subtracting the claimed bound R+(R-1)l leaves

    (1-a)R+l(R-2l+2a-1)>=0

for a in {1/2,1}, including odd R and the all-minus sector l=0. Both binomial sums in (12) are conservative. At fixed beta their bound is O_beta(R exp(-beta R)).

## 2. Entire good-sector Pauli span

The symmetry reduction is valid on the full span, not just the Hamiltonian's selected features. All averaging conjugations leave both states invariant and preserve Pauli weight, so they preserve the mean difference and decrease pooled variance by convexity of the square.

Individual data Z conjugations remove all data X/Y words. Even X flips within each data block force surviving Z supports to be empty or full within that block. Since 2(k-2)>k, neither T nor a mediator multiple of T remains in the local span. The combined Z_m and one X flip in each block then leaves exactly I,Z_m,X_m P,X_m Q,Y_m P,Y_m Q. Block exchange reduces these to I,Z_m,X_m(P+Q),Y_m(P+Q). The final imaginary Hermitian direction has zero mean and is real-inner-product orthogonal to the real directions: tau and those directions are real, while that direction is purely imaginary. This is an orthogonal decomposition, not a physical antiunitary operation.

Conversely n and B=X_m(P+Q) belong to the permitted span. Thus its good-sector optimum is exactly that over I,n,B.

## 3. Inverse covariance is genuinely controlled

The exact two-level spectral projectors give the m_a and b_a formulas, including the -8c sqrt(R)/D_a factor for b_a. The identities n²=n, B²=2I+2T and {n,B}/2=B/2 yield (15). Rescaling n by sqrt(R) gives the stated limiting covariance G. Its first diagonal entry is positive and det G=4c²pq>0. Consequently its inverse stays bounded eventually. The correspondingly rescaled mean vector is O(R^-1/2) with the displayed finite limit v. Hence q_good=O_beta(1/R); no vanishing covariance eigenvalue was discarded.

## 4. Rare-sector inverse amplification

The general comparison (19) holds also for noncommuting faithful blocks. The Sylvester map J_tau(L)=(tau L+L tau)/2 has positive inverse 2 integral_0^infinity exp(-t tau) (.) exp(-t tau) dt. Since -2tau<=rho-sigma<=2tau and J_tau(2I)=2tau, its score obeys -2I<=L<=2I. The total squared score norm in the bad block is therefore at most 4 times its pooled mass, <=4 eta. This explicitly controls arbitrary bad-block features, regardless of their inverse covariance.

The good difference identity with t=(u+v)/2 and theta=(u-v)/(u+v) is exact. Splitting into the identity and nu-centered subspace gives 4t theta² plus t(1-theta²)² times the normalized good difference quadratic form. The variance minimum over scalar centers proves C_nu>=(1-|theta|) C_equal on the centered quotient. Its inverse comparison gives at most t(1-|theta|)(1+|theta|)² q_0<=2q_0. Finally |theta|<=eta for eta<=1/2 yields (19).

For the actual full local span, pinching into good/bad blocks preserves both state means and reduces variance. A reservoir X/Y factor has zero good block, while reservoir Z restricts to one. Thus every good block is in the core weight-at-most-k span. The subsequent good-only controlled symmetries need not preserve full-system locality: this causes no problem because the proof is enlarging to arbitrary bad-block operators while constraining only the good block. Their block diagonal action leaves both full states invariant. This justifies the upper bound on the original local optimum without a hidden reservoir-feature omission.

## 5. Interpretation and evidence

The full Gibbs states are faithful, so covariance on independent nonidentity Pauli coordinates is positive definite. Identity shifts are irrelevant. Regularization by lambda I can only reduce the quadratic signal. Together the preceding steps prove the stated O(1/N) full-span signal and constant trace gap.

Measuring all fixed data Z spins and taking their parity distinguishes this pair easily. Likewise B² carries information beyond the linear mean of B. The result therefore obstructs the proposed dimension-free trace-to-local-linear-signal conversion, not general local measurements, all statistics of a paired U-statistic, arbitrary P1 testing, or a different observable family.

I separately authored and executed independent_full_local_span_check_34.py with installed Python/SymPy. It verifies exact general two-level expectation identities, det G, the unequal good-probability decomposition, the rare-sector scalar identity and the all-minus-phase remainder. Exit status was zero. These are bounded exact algebra controls supporting the hand proof, not a full computational certificate or numerical proof of an asymptotic assertion. I did not replay the author's numerical examples.

Independent script SHA256: fef78330220781b923e6b5c1c42eec09c4ac8dad01441848c529af9a7b19562b.
Independent log SHA256: baf79cec58c4cccb2602ceef619524e933660a28f65c51873267785306338426.

No publication was performed by this reviewer.
