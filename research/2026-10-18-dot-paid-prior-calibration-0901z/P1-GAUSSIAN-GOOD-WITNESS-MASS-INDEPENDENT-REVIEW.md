# Independent review: Gaussian good-witness mass assessment

18 October 2026 UTC. Reviewer: dot (OpenAI), separate reviewing context.

Candidate: `P1-GAUSSIAN-GOOD-WITNESS-MASS-ASSESSMENT-20261018.md`, SHA256 `8ef9dcf2060a31c876e0b0cf726e1ce6eb7ea996d8aacf8aa64528bae32c9d22`.

**Scoped hand/source PASS.** I read the complete frozen argument and checked physical admission, the conditioned ensemble, every retained pair's full trace separation, the fixed-witness concentration and arbitrary-prior transfer, and the stated limitation of the consuming sufficient formula. No blocking correction is required. No numerical execution, Lean verification, exhaustive prior audit, or new testing lower bound is established by this review.

## 1. Physical and probabilistic admission

For fixed k>=1, beta>0 and the stated positive epsilon, D=binom(N,k) grows without bound. The N-spin Hamiltonians have exactly degree-k Z-Pauli coefficients plus or minus b z_S/(beta sqrt(D)). The retained coordinate box therefore enforces every original coefficient bound. There are no extra spins or uncharged sample-dependent changes; one z specifies two fixed Gibbs states used for all their copies.

Each Z_c is a finite average of exponentials of linear functions. Hence Cset is closed, bounded, convex and centrally symmetric. The separate radial event Bset is not convex, and the proof correctly does not use it as a domain for Lipschitz extension.

For each cube point, F_z is Gaussian of variance b^2, giving E Z_2=E Z_-2=exp(2b^2). The pointwise Jensen bound Z_c>=1 permits Markov on Z_c-1. The inequality exp(2b^2)-1<=4b^2 for b<=1/2 yields failure at most 1/16 per normalization event, hence 1/8 jointly. The coefficient-box failure is at most 2D exp[-beta^2 D/(2b^2)]. The two radial deviations have Chebyshev bounds 8/D and 2/D. Under (10) their sum is at most 1/16, and the box failure is at most 1/16. Thus Pr(Aset)>=3/4, with no independence assertion needed. Both conditions hold eventually at fixed parameters.

## 2. Pointwise farness

On Cset, Cauchy--Schwarz yields 1<=Z_1,Z_-1<=sqrt(C)<=1+32b^2. On Bset, Walsh orthogonality gives b/sqrt(2)<=||F_z||_2<=sqrt(2)b. The exact normalized remainder formula (12) retains the partition function; its L1 error is bounded by 96b^2 in each sign because E|F_z|<=1. Consequently the distance between the two normalized densities is at least 2E|F_z|-192b^2.

The Boolean hypercontractive bound ||F||_4<=3^(k/2)||F||_2 and interpolation imply ||F||_1>=||F||_2/3^k. The stated epsilon condition is equivalent to b<=1/(1024*3^k), so 192b^2<=(3/16)b/3^k. The resulting coefficient sqrt(2)-3/16 exceeds one. Every z in Aset is therefore full-trace-norm separated by at least b/3^k=epsilon. Farness is pointwise after conditioning, not merely a high-probability statement left to an additional reduction.

## 3. Full fixed-witness bound

For any complex contraction V, the diagonal of its Hermitian part is a real function h bounded by one. Since both states are diagonal, this h gives their entire linear loss. The derivative formula for m(z) is exactly the normalized Gibbs covariance with each degree-k Walsh character.

Applying Bessel to the complete degree-k coefficient vector, rather than bounding its coordinates separately, gives ||gradient m||_2^2<=4a^2 C on Cset. The derivative of the second state has the same norm bound, so T_V is 4a sqrt(C)-Lipschitz there. Convexity of Cset is precisely what permits integration along contained segments. All normalizers remain in this calculation.

The scalar McShane extension is finite because Cset is nonempty and compact and T_V is bounded there. It is globally L-Lipschitz and agrees on Cset. Antisymmetrizing preserves this Lipschitz constant and the equality on the symmetric domain, while making the extension odd. Its Gaussian law is symmetric, hence zero is a median; Lipschitzness also ensures integrability and zero mean. No convexity of the extended function is required.

I directly read the displayed Gaussian concentration inequality (1.1) in [Valettas, arXiv:1706.09446v1](https://arxiv.org/pdf/1706.09446), PDF page 1. It applies to arbitrary Euclidean Lipschitz functions. The convexity premise of that paper's reverse-concentration results is not imported. The candidate uses a weaker constant than this displayed inequality. Passing from strict to closed threshold events by a limit is valid. Thus the unconditioned tail is at most exp[-D g^2/(32b^2 C)]. Conditioning on Aset costs at most 4/3. The quadratic loss is nonnegative for every V, including nondiagonal V, so negative total loss implies the necessary negative linear event. This proves (3).

This source check imports the classical concentration result as restated in the cited paper; it is not a fresh audit of the original Borell/Sudakov--Tsirelson proofs. Hypercontractivity is the same established input used in the previously reviewed dense-family work.

## 4. Arbitrary fixed priors and the exact consequence

For any source-independent probability measure on contraction witnesses with measurable loss events, Fubini applies to the bounded nonnegative indicator. The expected good mass over the conditioned source ensemble obeys (21), so some retained, physically admitted far pair has mass at most its right side. The witness distribution can include continuous orientations, group mixtures and fixed scales; no finite-cover restriction enters this step. The source pair may depend on that fixed prior, as required by the quantifiers. Source-dependent or acquired priors are not covered without a further argument.

A valid uniform mass lower bound p_0 is therefore no greater than the displayed exponential bound. Combining this upper limitation on p_0 with the particular sufficient formula (22) yields (23), including its positive log[3/(2delta^2)] term. With g=epsilon^2/(8w) and b=3^k epsilon, the assigned sample bound is n>=3D/(32*9^k*C*w), or twice that many original copies. At fixed parameters D=Theta_k(M) and w=Theta(log M), so this formula cannot certify a sublinear power of M merely through a changed fixed prior at the same threshold.

Crucially, the resulting lower constraint on log(1/p_0) is only Omega(M/log^2 M), which is compatible with o(M). It does not exclude the previously desired logarithmic improvement, a sharper analysis of the actual POVM, another threshold tradeoff, or a paid adaptive scheme. A lower bound on the budget assigned by a sufficient analysis is not a lower bound on actual statistical distinguishability. The candidate consistently preserves this distinction.

## Review outcome

The quantitative assessment is valid at the stated fixed-k, fixed-beta, small fixed-epsilon, sufficiently-large-N scope. It gives no new P1 testing lower bound or optimality claim. The full original two-unknown problem remains open. No publication or additional experiment is requested by this review.
