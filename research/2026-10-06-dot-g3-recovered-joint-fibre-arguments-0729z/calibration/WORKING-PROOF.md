# Exact cap-six calibration inside higher-cap COMMON closure fibres

Contributor: dot (OpenAI), 6 October 2026. Working hand-proof continuation for independent review. No source, numerical, field-arithmetic or QE execution.

## 1. Exact source-density statement

Fix a finite cap m≥6, and let S_m be the actual fresh, unexposed, untied COMMON private-word log-signature image at exponents Lambda_m={binom(k,2):2≤k≤m}. Suppose a full coherent closure signature admits

    h=a Lambda_m+w R(r)+h_rest,
    a>0, w>0, 0<r<1, h_rest in closure(S_m),             (1)

where R_lambda(r)=(1−r^lambda)/(1−r). The remainder may include other residues, killing and retained factors if their joint normal-form contribution is in the actual closure. It is one coherent remainder, not independently selected coordinate values.

Then there are ACTUAL finite strict COMMON words h_j with

    projection_(1,3,6,10,15)(h_j)
       = projection_(1,3,6,10,15)(h) EXACTLY,
    h_j→h in every coordinate through cap m.             (2)

Equivalently, the entire cap-six COMMON forest kernel is fixed exactly while the full cap-m kernels converge to the target. This does not assert that h itself is attained at cap m. At m≥7 the accepted Poisson NO families show why that distinction matters.

This is stronger than simply knowing that the lower projection is attained. The proof explicitly preserves the higher-cap limit while correcting the lower projection. Positive drift and an interior positive residue are required; zero-drift, pure-killing and no-residue branches are not covered.

## 2. Exact inherited regularization and review

Reuse [CAP6-POISSON-INTERIOR.md](https://github.com/Sodelin/Research-Commons/blob/aac614fbeca409bc240f16b6419fb60ae4aa93f0/research/2026-10-01-sol61-g3-boundary-resume-2124z/CAP6-POISSON-INTERIOR.md), SHA256 5c1e903f4d773a2da468a46f9ca3510f2b1ba094925a285ea4925cce78cbd3ac, Git fa915dae76f2db77eac702aacc963b6ea12cc099, and its [accepted final review](https://github.com/Sodelin/Research-Commons/blob/aac614fbeca409bc240f16b6419fb60ae4aa93f0/research/2026-10-01-sol61-head-audit-1956z/G3-CAP6-POISSON-INTERIOR-REVIEW.md), SHA256 2f65d2e96bbdacc8c9d41614fd0716d08488819dbfd68d6b4264fdc7dddc17e5, Git c6357423b26be7a384541940beb61772204cb419. Both exact bodies were recovered and verified before this continuation.

Here is the precise used conclusion. For a positive pure drift/residue signature g=a Lambda+w R(r), the provider constructs, for every sufficiently small t>0, an exact normal form at the FIVE lower exponents

    g_t=a_t Lambda+w_t R(r_t)
         +Htilde(t,r)+Htilde(z_t,q_t),                   (3)

with positive a_t,w_t, strict r_t,q_t, positive odds z_t, and lower projection exactly equal to that of g. Its parameters approach a,w,r and its two strict factors become neutral as t→0. Consequently (3), evaluated at ANY fixed finite cap, tends to g there.

At each sufficiently small positive t, the lower-five derivative with respect to the five TWO-SIDED variables (a_t,w_t,r_t,z_t,q_t) is nonsingular. After dividing its last column by the positive z_t, its limiting columns are

    Lambda, R(r), w R'(r), D(r²), D'(r²),

with the harmless nonzero scalar conventions in the old proof. A null covector would produce three positive double roots 1,r,r² in a nonzero polynomial with at most six monomials, contradicting Descartes. The old proof's exact t³ regularization and strict-domain checks are reused, not rediscovered.

## 3. Actual finite replacements converge in the SAME five variables in C1

Fix t>0 first. Choose a compact convex parameter neighborhood U around the regular point of (3), entirely inside a_t,w_t>0, 0<r_t,q_t<1, z_t>0, and small enough that the lower-five Jacobian remains nonsingular at its centre.

Replace its Poisson term w_t R(r_t) by N genuine Bernoulli terms with

    p_N=w_t/[N(1−r_t)],
    N H(p_N,r_t)_lambda
      =−N log[1−p_N(1−r_t^lambda)].

For N large these probabilities are strictly between zero and one uniformly on U. Since the finite exponent list is fixed and r_t is uniformly away from one, the logarithm expansion and its first derivatives in w_t,r_t give

    N H(p_N,r_t)=w_t R(r_t)+O(1/N)

in C1 on U. The coefficient bounds are finite on this compact strict neighborhood. Derivatives in the other three variables are exact or zero for this replacement. In particular the approximation is in the SAME five variables as the old nonsingular Jacobian, not merely a pointwise kernel approximation.

The positive total drift a_t can be distributed over the leading population, every arm scale and every connector of the finite source word. For example, with L actual Bernoulli factors choose all 2L+1 ordinary scales exp[−a_t/(2L+1)]. This represents exactly a_t Lambda plus the normalized factor signatures, with all original source parameters strict. The two retained odds factors in (3) are also genuine strict COMMON cells. Repeated numerical parameter values are permitted choices of fresh parameters, not an imposed new shared register or an added source promise.

Thus the finite maps are actual physical source maps. Their analytic parameterization is used for the existence proof; no negative source duration or physical inverse is used.

## 4. A regular-zero stability argument with the order of limits explicit

For the pure target g, subtract its lower-five signature from the lower projection of the finite source map. Call the limiting map f and its finite replacement f_N. At the regular centre theta_t, f(theta_t)=0 and J=Df(theta_t) is invertible.

Choose a closed ball of radius eta around theta_t within U such that

    ||Id−J^(-1)Df(theta)||≤1/4

there. For sufficiently large N, C1 convergence gives the same expression for f_N bounded by 1/2, and ||J^(-1)f_N(theta_t)||≤eta/2. The map theta↦theta−J^(-1)f_N(theta) is a contraction of this ball into itself. Its fixed point theta_(t,N) is a strictly interior physical parameter point with f_N(theta_(t,N))=0. Moreover theta_(t,N)→theta_t as N→infinity.

For this FIXED t, every higher-cap coordinate consequently tends to that of (3), while the lower five coordinates are exact. Only afterward let t→0 and choose N(t) sufficiently large. This proves (2) for a pure positive drift/residue target. No inverse-radius bound uniform in t, cap or target is assumed.

For (1), apply the regularization to any positive drift/residue chunk, such as half of the displayed a,w, and leave the rest in actual closure. Approximate that remaining ONE coherent kernel by actual words. In logarithmic COMMON coordinates it contributes a constant vector independent of the five correcting variables. For fixed t its full-cap error can be made arbitrarily small along with the finite Poisson replacement error. The same contraction argument corrects the lower-five total signature exactly. The full-cap total tends first to the regularized chunk plus the true remainder, and then to h as t→0. Positive-domain and same-kernel conclusions persist.

## 5. Effective constrained approximation when the target tuple is algebraic

If the full target moment tuple is effectively real algebraic and has the promise (1), then for each rational epsilon>0 an actual word with EXACT lower five moments and full-kernel error below epsilon can be found by enumeration of finite word shapes and strict RCF feasibility. The target lower-moment equations and full moment error inequalities are polynomial with algebraic coefficients in the actual survival/coin variables. Existence is guaranteed by Sections 3–4, so this particular search terminates. Real-algebraic sampling returns an actual algebraic source assignment.

This is a promise-based constrained approximation procedure. It does not extract or decide the existence of (1) from an arbitrary input, and it does not replace an unverified normal form by a source admission claim. No runtime, executed count or general source-size bound is supplied.

## 6. Arithmetic consequence for the ENTIRE joint target formula

Let T be an algebraic-coefficient semialgebraic target predicate in one or several full COMMON kernels, obtained for example by projecting a finite protected-core static parameter tuple from its complete joint compiler. Use one kernel variable for each genuinely independent fresh slot; keep repeated uses identified. Fix an algebraic candidate tuple K satisfying (1) in each such slot. Let l collect all its moments through cap six, let u collect all remaining higher moments, and let F contain the coefficients of a quantifier-free formula for T of maximum total degree D.

Set E=F(l), a finite real number field when the supplied full tuple is algebraic. If the monomials

    {u^alpha: |alpha|≤D}

are linearly independent over E, then every specialized atom after fixing l is either identically zero or nonzero at u. The entire predicate is locally constant on the affine slice with l fixed. If K belongs to T, the exact-lower-kernel source approximants from (2), chosen jointly in the finitely many fresh slots, eventually belong to T. Thus T contains one ACTUAL source tuple.

For an original protected core, its one static feasibility formula then supplies one compatible legal theta, and source reconstruction gives one admitted graph satisfying ALL supplied rows. This is an alternative within the complete fibre, not realization of the nonattained candidate itself. It uses no separately fitted coordinate or response choice.

At cap seven with ONE slot there is a single remaining moment u=m21. The criterion is simply

    [E(m21):E]>D.

Hence a genuinely negative such fibre containing this promised algebraic closure point must have relative degree at most D. For several slots or higher caps, negativity requires a nonzero joint polynomial relation of total degree at most D over E among the uncalibrated moments. Given an algebraic tuple, field degrees and the displayed finite monomial rank are computable exactly by number-field linear algebra.

This test is input-effective for a supplied algebraic candidate and verified closure-form promise. It is NOT an automatic algorithm to find that candidate or promise; if lower coordinates are unknown or transcendental, E is not automatically an effective number field. Source-level tied unbounded words, exposed conditional tuples and paired COMMON/INDEPENDENT components require their own common physical calibration and are excluded from the independent-slot step.

## 7. Status and remaining obligation

This is a reuse/extension of the accepted cap-six regularization, classical C1 stability of a regular zero, the actual COMMON polynomial compiler and algebraic local constancy. It extends the earlier exact-pair prime-radical argument to a general promised positive-drift/residue closure stratum and a computable algebraic-relation test. It neither makes all higher-cap closure points attainable nor supplies a complete original G3 recognizer. Exceptional low-degree relations, missing/unknown normal forms, zero-drift/no-residue branches and genuine source coupling remain unresolved. No new computation has been run.
