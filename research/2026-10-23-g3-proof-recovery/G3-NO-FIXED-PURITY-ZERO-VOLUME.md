> Recovered authored source, 23 October 2026. Current disposition is in the package result catalogue. A completed hand proof is **PROVED (not Lean formalized)** at its stated scope; independent review is a separate field. Historical candidate/open headers below do not reopen a completed component or establish a broader endpoint. This publication is not a new proof or a new execution. Private local addressing/receipt locators are omitted; the original and public hashes and exact projection kinds are recorded in SOURCE-MANIFEST.json.

# No fixed zero-volume test for the rational logarithmic promise

22 October2026 UTC, existing G3 owner. HAND/self-audited, UNREVIEWED and
UNCOMPILED. No mathematical program, source tuple, QE or new model/native job
was run. Original all-input G3 remains OPEN; historical novelty is unassessed.

## Prior and successor comparison

The exact proposed receiver is ONE semialgebraic family whose nonnegative
volume vanishes exactly on the pure inputs of the retained logarithmic-cone
promise. Formula size, degrees, dimension and real constants may be arbitrary
but are fixed before the rational input is supplied.

The following actual sources were read before this argument:

- Commons8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6,
  research/2026-10-09-dot-log-cone-recognition-reduction-1508z/
  LOG-CONE-PURITY-TO-ORIGINAL-RECOGNITION.md,
  SHA256c0058ac6f854bc027d25c196b632d5312affed9bc973d1cf372936081173537d.
  Its cone, exposed rays and two-sided original-source reduction are REUSED.
  The later research/2026-10-10-dot-g3-three-log-purity-1210z/
  THREE-LOG-PURITY-REDUCTION.md, SHA256
  c99623631f972c3911f3dceba9f1b376ed2b135fd2dbc04aeae268633fcb33a9,
  and its INDEPENDENT-THREE-LOG-REVIEW.md retain the full promise and supply
  Phi. Neither supplies its zero test.
- [G3-WITNESS-BOUND-ROUTE.md](G3-WITNESS-BOUND-ROUTE.md),
  SHA256446727db5a89571342401147017198f57f848e39c4819486e9b57bef5af2210d:
  its fixed-intensity pure curve is already proved Zariski dense. That lemma
  and proof are REUSED. Its statement explicitly leaves classification on
  only encoded algebraic points open; real nonsemialgebraicity alone is not
  the additional rational-input conclusion below.
- [G3-PURITY-AS-TWO-BOUNDED-VOLUMES.md](G3-PURITY-AS-TWO-BOUNDED-VOLUMES.md),
  SHA256099c56eb95cabbb2ceb8f7e912b1ed0ddb871121be7680f5c67b9ebff89b50e5:
  exact two-volume reduction and one sign-changing-integrand control. It
  rejects that integrand as a zero-volume test, not every fixed alternative.
- The complete OLD NO-FIXED-SEMIALGEBRAIC-RATIONAL-CLASSIFIER.md and its
  complete INDEPENDENT-RATIONAL-CLASSIFIER-REVIEW.md, in
  research/2026-10-06-dot-g3-calibrated-original-recognition-1422z at that pin,
  SHA2563c89bb2d02f7166c8b9c8dc85c872ed348c95900ba8dc11404c7286f5879a0a6
  and85d7fbb2bd01211c599da559f087b00c21a616492d25b492c7282233042d23ab.
  They ALREADY exclude one fixed classifier on the original calibrated
  rational observation domain, without assuming invariance. The rational
  two-sided boundary method is REUSED. The14October copy at
  research/2026-10-14-dot-g3-coupled-effective-slice-0602z/primary/
  rational-classifier.md is byte-identical, not a new theorem.

The incremental use-site here is the arithmetic promise itself and the
single-volume receiver. It is not a new general fixed-classifier obstruction,
a reproof of the original all-core reduction, or a new undecidability result.

## Statement

Fix ANY j>=3. Put L={3,6,10,15,21}, J=[1/j,1-1/j], and

    D_n(r)=n-sum_(h=0)^(n-1) r^h,
    C=cone{D(r):r in J} subset R^5.

The promised input b is in Q^5, b_n>1, with log b in C minus{0}.
Call it pure if log b=w D(r) for some w>0,r in J.

There is NO semialgebraic set E subset R^5, even with arbitrary fixed real
coefficients, which accepts exactly the pure inputs on this rational promise
domain. A fixed finite RCF formula has the same limitation by elimination of
its real quantifiers. This concerns correctness only on promised rational
inputs; no correctness at irrational points is assumed.

## Rational labels force a whole curve onto the boundary

Let r0 be ANY point of the interior of J and put p=exp(D(r0)), coordinatewise.

Rational PURE inputs approach p. Choose rational r_k in J tending to r0.
Choose an integer A_k>=1 clearing all five denominators of D_n(r_k), so
e_n,k=A_k D_n(r_k) are positive integers. Choose rational t_k>1 such that
A_k log t_k tends to1; density of the rationals near exp(1/A_k) permits this,
with error less than1/k. Then

    b_n,k=t_k^(e_n,k)

is rational, its log vector is (A_k log t_k)D(r_k), and b_k tends to p.
Each is an actual promised pure input. No rationality of p is needed.

Rational NONPURE inputs also approach p. The five polynomials D_n have
distinct degrees2,5,9,14,20, hence their value vectors on rational nodes in J
span R^5. Select five independent such vectors. Their positive sum eta is
an interior point of their simplicial cone, hence of C. For every epsilon>0,

    D(r0)+epsilon*eta is in interior(C).

Indeed, add D(r0) to a suitably scaled open ball about eta inside C.
The old exposed-ray result implies that every pure ray is on the boundary
of this full-dimensional cone. Thus no interior point is pure.

Coordinatewise exp is a homeomorphism onto the positive orthant. The open
set exp(interior(C)) contains nonpure rational vectors arbitrarily close to
exp(D(r0)+epsilon*eta). Let epsilon decrease to zero and choose these rational
vectors closer still. They satisfy the SAME fixed-j, full-five promise and
tend to p. They are not approximate labels: every selected rational vector
lies in that open nonpure set.

If E classified the promised rational inputs, the pure sequence would be in
E and the nonpure sequence outside E. Therefore p is on the Euclidean
boundary of E. This holds for EVERY r0 in the interior of J.

## The reused Zariski-density contradiction

The old lemma says r -> exp(D(r)) on ANY nonempty open interval is Zariski
dense in R^5, including over real coefficients. Briefly, a polynomial in
these five coordinates becomes a finite sum of exp(P_alpha(r)). Differences
of the exponent polynomials are nonconstant: the D_n have distinct degrees
and all vanish at r=1. An identity on the interval extends analytically to
the real line. At positive infinity one exponent polynomial is eventually
strictly largest; division by its exponential contradicts its nonzero
coefficient. This is the retained proof, not a physical extension of J.

In a finite polynomial-sign description of a semialgebraic E, remove
identically zero atoms. At a boundary point some remaining nonzero atom
vanishes, since otherwise all signs are locally constant. The product of
these finitely many nonzero polynomials is nonzero and vanishes on the
entire curve exp(D(r0)). This contradicts that reused Zariski-density lemma.
The rational-input statement follows.

In particular there cannot be a fixed finite RCF certificate relation R(b,c),
with any fixed finite real-witness vector c, whose certificate exists exactly
for pure rational promised b. Projection over c would give such an E. This
permits arbitrary witness coefficients and does not require their selection
to be computable. A growing certificate language or a non-RCF verifier is
outside this fixed-checker conclusion.

## Consequence for the proposed volume certificate

Suppose K subset R^5 times R^k is ONE fixed semialgebraic family, k>=1,
and its fibre K_b has a nonnegative finite Lebesgue volume on promised inputs.
For a semialgebraic fibre, volume is positive exactly when it has nonempty
interior: lower-dimensional cells are null, and a full-dimensional cell
contains an open ball. The existence of a ball inside K_b is an RCF formula
in b. Thus

    {b:volume(K_b)=0}

is semialgebraic. It cannot agree with purity on all promised rational inputs.
In particular no such family can represent the nonnegative Phi(log b) with
the required exact zeros. The same obstruction applies to fixed semialgebraic
parameter changes or finitely many such zero tests combined by Boolean logic.

This rejects EVERY fixed SEMIALGEBRAIC-family version of the positive-volume
idea, rather than only the old direct integrand. The OLD two-volume adapter stays
valid: equality of two positive volumes is not the zero test just excluded.

## Limits and changed frontier

An arbitrary algorithm selecting a family from the encoded input is not
excluded. Its selection need not be semialgebraic in the input values, even
if the returned formulas have bounded size. Unbounded format complexity and
nonsemialgebraic parameter selection are BOTH outside this theorem's contract.
No individual rational pure input lacks a certificate by this proof; the known
rank-one cases remain decidable. No algebraic rank-five pure input is constructed
or excluded. The arithmetic promise is not dropped.

Remove fixed-family zero-volume/finite-RCF replacements from the arithmetic
receiver queue. A future period method must supply an actual exact equality
mechanism or a terminating input-dependent transformation whose zero case is
proved; positivity of Phi alone does not supply either. Original all-input
source H/complete NO, all mechanisms and original joint interfaces remain open.
All previous proofs and executed controls remain unchanged and unreplayed.
