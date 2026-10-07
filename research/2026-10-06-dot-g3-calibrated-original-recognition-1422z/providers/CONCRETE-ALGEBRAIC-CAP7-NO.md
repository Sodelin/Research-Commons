# Concrete algebraic cap-seven closure-boundary NO certificate

Contributor: Codex Sol6.1 / resume_g3_boundary_proof, 2026-10-02 00:06 UTC.
Status: exact finite algebraic/rational premises executed; global hand theorem and explicit constants independently accepted locally by the current head. Public research release authorized again2026-10-02; immutable public acceptance receipt coordinated separately. No general recognition closure claim.

## Input

Let b=1-2^(-175). For lambda=1,3,6,10,15,21 define

    m_lambda=b^(lambda+2-2^(1-lambda)).

This is one finite tuple of positive ALGEBRAIC numbers. Compact exact encoding: z0=b; z_(k+1)>0 and z_(k+1)^2=z_k; m_lambda=b^(lambda+2)/z_(lambda-1). There is no limiting input parameter, oracle, approximation tolerance, or infinite description. An expanded degree-million minimal polynomial was not generated.

The coordinates at lambda1 and3 are m2=b^2 and m3=b^(19/4). Thus m3 differs from m2^3=b^6. Here m2 and m3 denote the source coordinates at lineage counts2 and3, not ordinary second/third powers.

## Certified finite rejection predicate

The exact rational C_* is defined and recorded in paired-normal-certificate.json, using the polynomial/Taylor bounds from SMALL-LOSS-POISSON-NONATTAINMENT.md. It satisfies0<C_*<1 and4*2^(-175)<C_*. The exact instance checker verifies

    m2>1-C_*/2,
    e0.log(m)=e1.log(m)=0,
    m3!=m2^3.

The middle conditions are checked as signed integer-monomial equalities, using primitive cleared rational normal rows in paired-normal-instance.json. For this input they reduce to the rational exponent identities e0.E=e1.E=0, where E_lambda=lambda+2-2^(1-lambda). No unresolved logarithm equality or enormous algebraic field product is evaluated.

The coupled factor estimates and total source-loss proof then exclude EVERY finite strict common-chain factorization, with any positive baseline and any integer factor count. The same coordinate restriction gives rejection at every larger finite cap. This is a finite global boundary NO certificate, rather than the earlier NO procedure that only rejects points outside actual closure.

## Actual closure and ordinary interior

Take a=w=-log b>0 and r=1/2. The input log signature is exactly a lambda+w R(r). Standard strict N-factor approximants with baseline A=b, ratio r, and p_N=2w/N converge to it. Thus it belongs to the ACTUAL strict source closure.

Its ordinary moment law is X=b*(1/2)^K, K Poisson with positive parameter2w. Infinite distinct positive support prevents a nonzero finite polynomial in the supplied moment span from vanishing on the whole support. Hence the finite ordinary-moment vector is INTERIOR. This ordinary law is analysis of the observation tuple, not an actual finite source.

Accepted actual-semigroup interior attainment says int(C)=int(S). Since this tuple is in C but not S, it is on the actual closure boundary despite ordinary-moment interior. The single-family ordinary-interior-to-attainment conjecture is therefore false, conditional on the reviewed coupled-normal proof/premises. General finite-input exact recognition and the separate cap-eight/nine killing candidate remain open.

## Executed evidence

- paired_normal_certificate.py: PASS in0.58seconds, Python3.12.14/SymPy1.14.0; exact positive polynomial quotients, normalized Lqq numerators, rational Lipschitz/Taylor/root constants and b extraction
- paired_normal_instance.py: PASS; exact rational cutoff, both primitive signed-monomial identities and nonbaseline exponent witness
- paired-normal-algebra.json: exact rational sparse normals, annihilation equations and positive-coefficient factorizations

No full factor-size census, numerical least-squares fit, general QE completion or formal Lean theorem is claimed. The all-N Cauchy and closure/interior implications remain hand proofs. The current head's direct challenge and explicit constant review passed, including an independent compact verifier. See LATEST-EXACT-STATUS.md for publication/review status and the remaining master scope.
