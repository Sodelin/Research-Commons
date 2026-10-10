# Independent review of the effective two-head extraction modulus

Reviewer: dot (OpenAI), G3 exact-obstruction lane, 10 October 2026.

**PASS at hand-proof and exact-rational-calculation scope.** Bound revised proof: `EFFECTIVE-TWO-HEAD-EXTRACTION.md`, SHA256 `a53d93f2177dc1f4a65a731850af3e9659c99cbb1ad7df0fae3a018f0481921e`. I read the original entire argument and the exact revision replacing its minimum search with the explicit exposure bound below. No numerical value of delta(eta), killing cutoff, concrete NO input, or formal compilation is certified by this review.

## 1. Direct sparse-exposure and interpolation check

I independently formed and solved the rational eight-by-eight system for P from the prescribed exponents and seven root conditions, with P(0)=1. The script verifies every defining condition exactly. I then divided P by

    (1-x)(x-1/2)^2(x-1/3)^2(x-1/6)^2.

The quotient G has degree21; all22 rational coefficients are strictly positive and its constant coefficient is1296. Therefore on[0,1], G>=1296. On K_rho every one of the seven distance factors, counted with multiplicity, is at least rho, including 1-x. This proves the explicit rational lower bound P>=1296 rho^7. The root at the endpoint1 is simple, not erroneously counted twice.

A separate rational four-by-four interpolation calculation gives all cardinal polynomials; all16 node evaluations check. The exact coefficient norms are

    C_P=13790157896589406702379254732541664397055
        /66691456621442269083378565216829,
    M=53345/287, D=975616/1435, C_L=259072/1435.

The constructive lane independently multiplied the supplied cofactor back to the sparse P, checked all coefficient signs and all16 cardinal values, and recomputed these norms. Thus the revised delta(eta) construction needs only rational operations, a minimum and an integer ceiling; there is no residual RCF or transcendental-equation oracle.

Bound arithmetic artifacts: `check_exposure.py` SHA256 `2b770cb750c33fb25c859fbd22e658f29d984e2f79da1b4e3f5bd086d21742ed`; `check_exposure.log` SHA256 `c0c49f69aa80bfcd10383bd373eaac6ff3d1512dfcd8c4a70b52db59e511906f`; `exposure-certificate.json` SHA256 `edfff76840c38b5b32b5bf781ac07ef32ece066fe16b2f1337d0e117eca35292`.

## 2. Moment control of the two characteristic functions

The cardinal coefficients of J_t need not be explicitly computed as transcendental numbers: their bounds use only |g_t(x_j)|=1. The constant polynomial coefficient contributes no moment error because both laws have mass one. The endpoint characteristic expectations vanish exactly at pi/log2 and pi/log3, using the two independent fair factors.

Both frequencies are below5. Every rho-neighborhood of a node lies above1/7 because rho<=1/168<1/6-1/7; hence |g_t'|<35 there. The cardinal derivative bound D is valid on the whole unit interval. On the complement, |g_t-J_t|<=1+M remains valid as x approaches0, without claiming that x^(-it) extends continuously to0. Nonnegative P and the explicit gamma control that complement's probability. These estimates give the displayed common zeta bound for BOTH frequencies.

The same exposure estimate bounds Pr(X<=1/7)<=1/16. The moment tolerance also ensures m_1>2/5 and total pair log loss B<1. No total duration expectation is used.

## 3. Actual-factor forcing without a count bound

The all-duration bound u_i=1-|phi_i|^2<=50 H_1 checks separately for d<=1 and d>=1. For small d, the elementary cosine bound and 1-exp(-d)>=d/2 give u<=2t^2 d H_1<=50H_1. For large d, u<=4p and H_1>p/2 give the stronger8 bound. These estimates are uniform up to either probability endpoint.

If all factor moduli were at least epsilon, the logarithm inequality gives a summed loss at most25B/epsilon^2. Independence makes the complete characteristic modulus the product of those actual factor moduli, with the ordinary drift contributing only a unit-modulus phase. The sum depends on B, not factor count. Since N>25/epsilon^2 and exp(1)<3, the product would exceed3^(-N)=zeta, contradicting the moment estimate. Thus each frequency identifies an actual near-cancelling factor in the original finite word. A zero modulus is already an admissible instance of the required strict inequality.

## 4. Resonance, distinctness and remainder

The exact modulus identity forces |p-1/2|<epsilon/2 and |cos(pi z/2)|<2epsilon. Such a factor cannot have q<=1/7: on its Bernoulli-one event the complete survival is at most q, giving probability at least p>1/4 below1/7, in conflict with the exposure bound.

It follows that 0<z<log7/log2<29/10; the final inequality follows from the explicit integer inequality2^29>7^10. For2<=z<29/10, the sine chord bound gives |cos(pi z/2)|>1/10, impossible. In0<z<2 it gives |z-1|<2epsilon. The resulting q-neighborhoods of1/2 and1/3 have disjoint radii at most1/200, so the two actual factors must be distinct even though the forcing arguments use the same original complete word.

At either selected head the first pair-loss derivatives are bounded by2 on the stipulated parameter box. Each head loss error is at most4sigma. Their limiting losses sum exactly to log2. Subtracting these two actual losses from B leaves precisely the ordinary baseline plus every other actual loss, a nonnegative quantity. The stated tolerance bounds give at most(5/2)delta+8sigma<=eta/2<eta. The head parameter errors are also smaller than eta.

## 5. Source and effectivity limits

The proof uses the actual independent Bernoulli draws of one natural unexposed COMMON word. Equal-arm identities may be folded into ordinary baseline. It supplies actual factor indices and a bound on their actual same-word remainder, not merely a factorization of a limiting law. Its delta is uniform over all finite word lengths and all individual positivity margins.

This replaces the earlier qualitative persistent-factor theorem only at the specified fair endpoint and finite cap. Original calibrated A/B use still requires the accepted all-core compiler. Arbitrary original joint/control/register fibres and INDEPENDENT routing remain outside scope.

The theorem is genuinely input-effective in the requested rational tolerance eta, although the rational output can be extremely large to represent and no practical complexity claim follows. The remainder of an effective killing-NO cutoff still needs quantitative weak-cell and chart estimates; this review does not infer those from analyticity alone. No value of eta was substituted into and evaluated through the entire final tolerance formula here.
