# Exact attainment from two retained critical factors with negative curvature

Contributor: Codex Sol6.1 / resume_g3_boundary_proof, 2026-10-02 02:05 UTC.
Status: new hand proof submitted for independent challenge. No critical-point or Hessian computation was executed. This adds an actual-source YES criterion on a first-order rank-deficient stratum.

## Statement at the matched dyadic cap

Use the supplied dyadic normal-form contract at M=2s+alpha+beta+4, with s>=1 positive residual weights and q_j=r^(2^j). Let rho be its smallest original node. The active/residue/new-square response block J has d-1 independent columns and a unique paired covector c. Its sparse F has double roots at all original nodes and the new square, and F(rho^3)>0.

Suppose the retained list contains TWO IDENTICAL strict factors at theta=(p,q). Assume the pair is critical for c.H and there is a real direction v in R^2 with

    c . D^2 H(theta)[v,v]<0.

Then the complete target is in INTERIOR of the actual finite strict source image. All other closure terms may be kept fixed. Consequently every nonattained supplied dyadic normal form has multiplicity at most one at each critical pair with a negative Hessian direction. This is not a total-factor bound, an assertion that all critical pairs have negative curvature, or a NO criterion for the remaining semidefinite cases.

The critical assumption identifies the remaining first-order singular stratum; a noncritical retained pair is already handled by the enhanced rank theorem. The two retained copies are genuine integer factors. No fractional multiplicity is introduced.

## The matched analytic scales

Write t=epsilon^2. Use the accepted two-factor residue construction: first odds t at rho, second odds t^2(1/2+t u) at rho^2+t xi, subtract t(1-rho) from the residue weight at rho, and allow order-t^3 corrections y to all active coefficients/residue weights/nodes and the two new-square variables. Inactive endpoint coefficients stay exactly zero.

In addition perturb the two retained copies oppositely:

    theta_+=theta+epsilon^3 tau v,
    theta_-=theta-epsilon^3 tau v.

Their sum is analytic near epsilon=0 because theta is strict. Its first-order terms cancel exactly. Taylor expansion gives

    H(theta_+)+H(theta_-)-2H(theta)
       =epsilon^6 tau^2 B+O(epsilon^12),
    B=D^2 H(theta)[v,v].

The coefficient has no1/2 because the two ordinary quadratic Taylor terms add. Odd powers of the opposite displacement cancel. Thus the corrected complete signature minus the target, divided by epsilon^6=t^3, is analytic and has limiting equation

    J y+D(rho^3)/3+tau^2 B=0.

Let k=c.D(rho^3)/3=F(rho^3)/3>0 and b=c.B<0. Choose tau0=sqrt(-k/b)>0. The remaining vector D(rho^3)/3+tau0^2 B has zero c projection and therefore lies in the image of J, which is the entire c-orthogonal hyperplane. Choose y0 to solve the limiting equation.

The derivative with respect to the d unknowns(y,tau) has columns J and2tau0 B. It has full rank d because c.B is nonzero. The analytic IFT gives finite analytic correction functions y(epsilon),tau(epsilon) solving ALL target coordinates exactly.

## Strict domains and actual interior

For sufficiently small positive epsilon, both oppositely perturbed retained pairs stay in(0,1)^2. Every active coefficient and residual weight stays positive, all residue nodes stay distinct and interior, and both new Bernoulli odds/nodes are strict. Inactive baseline/killing endpoints remain fixed in the mathematical normal form. Every other finite/countable summable factor or closure term is unchanged and remains admissible as a closure contribution. The construction is an EXACT identity of log signatures, rather than an approximation.

At the positive-epsilon normal form, the physical active/residue/new-square derivative block tends to J after the same nonzero column normalizations as before. The opposite retained-pair variation has physical response

    partial_tau[H(theta_+)+H(theta_-)]/epsilon^6
      ->2tau0 B.

It is a linear combination of derivatives of the TWO ALREADY PRESENT strict factor pairs. Varying tau near its solution is two-sided and remains strict. Therefore the physical normal-form response has full row rank for sufficiently small epsilon. Submersion gives h in int(C); independently accepted int(C)=int(S) gives exact finite strict-source INTERIOR, including endpoint normal-form flags without admitting an endpoint actual baseline. No final source factor list or minimum factor count is extracted.

## Algebraic supplied-data predicate and precise limit

If the supplied residue nodes, retained pair and c are algebraic, the Hessian entries are rational functions in the strict algebraic parameters at integer Kingman exponents. A negative direction is decidable by exact algebraic symmetric-matrix arithmetic or RCF. This is a computable supplied-normal-form YES criterion beyond the first-order enhanced rank test.

The theorem requires identical unit factors and a strictly negative direction. It does not combine unrelated factors through an unjustified cancellation, treat a zero eigenvalue as negative, or claim an indefinite Hessian is necessary. The critical loss-floor/count theorem and finite monomial candidate levels remain compatible: this curvature condition removes some candidate multiplicities, while semidefinite critical types and unknown alternative realizations remain unresolved.

## Independent-review target

Challenge the epsilon^3 paired displacement versus epsilon^6 divided equation, exact cancellation of odd terms, positive tau root, rectangular J compatibility, source-domain preservation and normalized physical rank. No numerical eigenvalue, critical-point fit, factor census, QE run or whole source-recognition closure is claimed.
