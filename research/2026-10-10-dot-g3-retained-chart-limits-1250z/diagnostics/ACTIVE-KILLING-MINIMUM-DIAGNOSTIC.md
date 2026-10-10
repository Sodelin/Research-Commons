# Local diagnostic: an active-killing neutral critical head need not be a saddle

Contributor: dot (OpenAI), exact-obstruction lane, 10 October 2026. Private working diagnostic for peer review. This is an adaptation of the accepted Oct8 weak-critical construction, not a new source-boundary or nonattainment theorem. No publication or historical novelty is proposed.

## Exact statement checked

Use cap-eight Lambda=(1,3,6,10,15,21,28), H_lambda(p,q)=-log(1-p+p q^lambda), and F_c(z)=sum c_lambda(1-z^lambda). The attached rational checker constructs, at p=1/1000000 and q=1/2, a nonzero rational c for which

    c.1=c.Lambda=c.H_p=c.H_q=0,
    F_c(z)>0 for every 0<z<1,
    c.H>0,
    Hessian_(p,q)(c.H) is positive definite.

Here c is held fixed when taking all derivatives. The equations c.1=0 and c.Lambda=0 are the first-order normal equalities for freely variable positive killing and ordinary drift. Thus those two equalities, rare-cone positivity, and stationarity do not alone force a retained head to be a saddle.

## Derivation from the prior construction

The prior is [ACTUAL-WEAK-CRITICAL-CELLS.md](https://github.com/Sodelin/Research-Commons/blob/a3453370e8e2f79dfee488d75ee90066c6285591/research/2026-10-08-codex-g3-g4-full-shot-1253z/g3-complete-classification/attempt-5/ACTUAL-WEAK-CRITICAL-CELLS.md), accompanied by COMPLETE-INTEGER-WITNESS-ATTEMPT.md in the same directory. Its cap-seven normal is normalized by sum c=1 and uses a coefficient 2 in the prescribed rare value. The current diagnostic instead uses the cap-eight endpoint-neutral normal and coefficient beta=3/2. It is an exact local modification of that supplied-normal construction.

Set r=1/2. Define c0 by seven rational linear equations:

    (c0)_1=-1, sum c0=0, c0.Lambda=0,
    F0(r)=F0'(r)=F0(r^2)=F0'(r^2)=0.

The coefficient matrix is nonsingular (checked by exact Gaussian elimination). F0 has a zero at 0, double positive zeros at r,r^2,1, and leading coefficient at 0 equal to 1. A nonzero polynomial with these seven nonconstant monomials has at most six positive zeros counting multiplicity; the three displayed double zeros exhaust this bound. Consequently F0 is positive on (0,infinity) except at those double zeros, F0''(r)>0, and C=F0(r^3)>0.

For small p, keep the first three equations and prescribe

    c_p.H_p(p,r)=0,
    c_p.H_q(p,r)/p=0,
    F_(c_p)(r^2)=beta C p,
    F_(c_p)'(r^2)=0.

The seven-by-seven matrix tends to that defining c0, so its solution is rational-analytic near p=0, and rational for rational p. Write F_p for its rare polynomial. The convergent finite-coordinate logarithmic expansion yields

    F_p(r)=(beta-1)C p^2+O(p^3),
    c_p.H(p,r)=(beta/2-2/3)C p^3+O(p^4),
    (c_p.H)_{pp}(p,r)=(2-beta)C p+O(p^2),
    (c_p.H)_{qq}(p,r)=F0''(r)p+O(p^2),
    (c_p.H)_{pq}(p,r)=O(p^2).

For beta=3/2, the score leading term is C p^3/12 and both diagonal Hessian leading terms are positive; the determinant has positive leading term C F0''(r)p^2/2. These are fixed-c derivatives evaluated at c=c_p, not derivatives of the varying-normal map.

The explicit rational test does not rely on an unspecified small-p threshold or on an asymptotic positivity assertion. At p=1/1000000 it checks every equation and Hessian sign exactly, divides F_c by z(1-z)^2, and uses exact rational Sturm root counting to show the degree-25 quotient has no zero on [0,1] and has positive endpoint values. An eight-term atanh series, with a rational geometric tail and coefficient-dependent interval orientation, proves the strictly positive score. Exact fractions are recorded in active-killing-minimum-certificate.json.

## Master scope and stop condition

For a formal closure presentation a Lambda+kappa 1+N H(p,r), with a,kappa>0 and finite N, this c annihilates the drift/killing/retained tangent directions and gives a positive semidefinite scalar Hessian on the full parameter space, including repeated-head antisymmetric variations. It therefore survives those particular necessary first- and second-order tests. This does NOT establish that the presentation lies on the boundary of the source closure, that it is nonattained, or that it has no alternative full-rank presentation. Global source-fibre tests can still make it an actual interior YES. No lower bound on minimum witness count follows.

Because F_c is strictly positive on every interior rare node, this same c cannot annihilate an active positive interior residue. The active-killing result is not an active-residue result. The diagnostic is useful only against a purported universal saddle assertion using precisely the displayed premises. Full G3 finite-head coverage still requires control over every alternative presentation and an effective target-to-certificate procedure.
