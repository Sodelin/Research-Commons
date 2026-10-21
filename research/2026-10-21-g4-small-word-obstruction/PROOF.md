# No bounded-size all-small fair cap-six ordinary returns

21 October 2026. Contributor: dot (OpenAI), working with Nolan. Exact scalar expansion and analytic proof; separate assistant-context scoped review PASS. This extends the earlier necessary-scale obstruction, not the G4 master conclusion.

## Theorem and original-source scope

For each fixed integer N>=1 and finite H>0, there is epsilon(N,H)>0 such that no strict word of between 1 and N fair independently routed bigons, separated and padded by positive ordinary connectors, has BOTH:

1. Every mean arm duration a_i=(u_i+v_i)/2 is less than epsilon(N,H), with u_i,v_i>0.
2. Its complete six-root forest kernel equals E_h for some 0<h<=H.

All physical arm durations, routing assignments and chronology are those of the original source. One shared parameter tuple is used for all roots, arities and labelled forest observations. The complete six-root orbit representation retains all full-forest coordinates, not merely scalar diagonals. Existing target exterior, original IDs and protected controls are untouched; an insertion application still requires the inherited eligible bridge interface.

No analytic or common-rate parametrization is assumed. Arbitrarily unequal shrinking scales, colliding positive connectors and varying word parameters are covered. N and H must remain bounded, routing must remain fair, and every cell mean must be small. The theorem does not exclude general positive words with a non-small cell, unbounded cell count, nonfair routing or other architectures.

## 1. Inherited complete-forest estimates

Put b_i=(u_i-v_i)/2, z_i=b_i^2, A=max a_i,

    S3=sum a_i^3, S4=sum a_i^4,
    Z=sum z_i, T=sum a_i^2 z_i, M=sum a_i z_i.

Then 0<=z_i<a_i^2 and A^3<=S3<=N A^3, A^4<=S4. The reviewed necessary-scale proof gives the following estimates for any hypothetical exact complete-six return, uniformly as A tends to zero:

    Z=S3/6+O(A S3),
    T<=C A^3 S3.                                           (1)

Here C depends only on N,H and the fixed coordinate norm. These estimates precede its final same-cell extraction, so this proof uses their stronger aggregate form.

For completeness, the first estimate follows from exact additive K3=log q3-3log q2, whose local leading expression is -a^3/8+3z/4 with remainder O(a^4+az+z^2). The second uses the SAME rational full-six covector ell=P[:,14]: its single-cell normalized value at placement p is e^(-9p)a^2z/4+O(a^6+a^3z+z^2). Exact pair calibration puts all chronological placements in [0,H]. The full ordered product remainder is O((S3+Z)^2), not omitted. Exact full-law equality and e^(-9p)>=e^(-9H) yield (1), since S3<=N A^3. These are the uniform analytic estimates proved and separately reviewed in NECESSARY-SCALE.md, not numerical bounds from a sample.

Cauchy-Schwarz now gives

    M^2 <= T Z <= C A^3 S3^2,
    M <= C A^(3/2) S3 <= C N A^(9/2).                     (2)

The new point is that exact fourth diagonal calibration requires M to be larger than this permits.

## 2. Exact fourth diagonal source formula

For one fair cell with means a and half-difference b,

    q2=(1+e^(-a)cosh b)/2,
    q3=(e^(-3a)cosh(3b)+3e^(-a)cosh b)/4,
    q4=(e^(-6a)cosh(6b)+4e^(-3a)cosh(3b)+3e^(-2a))/8.

The last formula sums the actual 4+0, 3+1 and 2+2 independent arm assignments. Define the fourth logarithmic difference

    K4=log q4-4log q3+6log q2.

It is analytic in (a,z=b^2) near zero. Its exact physical-total-degree expansion through four is

    K4=3a^4/16-3az/2+15a^2z/4-3z^2/4
       + terms of physical degree at least five.

In particular, uniformly on 0<=z<a^2,

    K4=3a^4/16-3az/2+O(a^5+a^2z+z^2).                    (3)

Analyticity justifies the remainder: pure-a remaining monomials are divisible by a^5; remaining monomials linear in z by a^2z; terms quadratic or higher in z by z^2. This is an analytic ideal bound, not a truncation substituted for equality.

## 3. The contradiction

No-merger survival is multiplicative under chronological composition. An ordinary E_g contributes zero to K4, because its log no-merger survivals are -g,-3g,-6g. Thus exact complete-six equality necessarily gives sum K4_i=0.

Summing (3), and using (1), gives

    |3S4/16-3M/2|
      <= C[A S4+T+Z^2]
      <= C[A S4+A^3 S3+S3^2]
      <= C[A S4+A^6].                                     (4)

The constants absorb the fixed bound N. For sufficiently small A, absorb C A S4 into the left side to obtain

    3S4/32 <= 3M/2+C A^6.

Apply (2) and S4>=A^4:

    3A^4/32 <= C A^(9/2)+C A^6.

Division by A^4>0 gives 3/32<=C sqrt(A)+C A^2, impossible for sufficiently small A. This proves the theorem. No sign assumption on the ordered sixth-order terms, or on any analytic remainder, was made.

## 4. Consequences and limits

The previously allowed three-halves-scale asymmetric cells cannot cancel ALL the constraints: they may reverse the sixth-root covector, but they provide too little total az to satisfy the fourth diagonal equation simultaneously. The exact sign-reversal example remains correct; it only calibrated K3 and was never a complete return.

In particular, for fixed N there cannot be a sequence of fair complete cap-six ordinary-return words with total pair hazard tending to zero. Indeed each individual cell's pair hazard is nonnegative and its q2 satisfies q2<=(3+e^(-2a))/4. If the total pair hazard tends to zero, every a_i tends uniformly to zero, contradicting the theorem with any fixed H. This is a bounded-architecture statement, not a lower bound uniform over all N.

The accepted complete cap-four/cap-five vanishing-hazard suppliers are unaffected: they do not force this sixth-root covector to vanish. The accepted cap-five review explicitly retains a sixth defect. Accepted all-cap diagonal matching does not impose the complete-forest estimate T in (1). Nonordinary cap-six rank/interiority also supplies no counterexample to this local ordinary-return theorem.

An actual complete cap-six ordinary return, if it exists, must therefore leave this bounded-size all-small fair regime. The theorem does not prove that none exists. In particular it does not supply finite natural-INDEPENDENT forcing against every unknown-size finite strict rival, and it does not construct exact inequivalent rivals after every finite panel at one fixed target. Both G4 master alternatives retain their original quantifiers and remain unresolved.

## Sources and execution

Reviewed uniform estimates and exact sign example:
https://github.com/Sodelin/Research-Commons/blob/646fd682e3f62a615bf8d531289dbe937d4166c3/research/2026-10-21-g4-multiscale-scope/NECESSARY-SCALE.md
https://github.com/Sodelin/Research-Commons/blob/646fd682e3f62a615bf8d531289dbe937d4166c3/research/2026-10-21-g4-multiscale-scope/SIGN-REVERSAL.md

Actual cap-five supplier distinction:
https://github.com/Sodelin/Research-Commons/blob/ea5d72086ecc9de7faaf417df345f708602f5fd6/research/2026-10-07-cloud-independent-auditor-1616z/G4-WHOLE-GROUP-CAP5-INTERIORITY-HAND-REVIEW.md

The fixed projection and original source/insertion references are pinned in the earlier quotient checkpoint at commit 08001e2b298d461cade7bdcd2eda4079b5cd82c3. These inherited results are not claimed as newly proved here.

check_k4.py/log performs the exact scalar expansion with SymPy. The analytic contradiction is the hand proof above; a finite symbolic check is not a standalone proof of its uniform quantifiers. No numerical solve, source root or Jacobian claim was made.

## Earlier compact fair energy/hazard results

The accepted 8 October packet already gives complete cap-nine restrictions for compact common-scale fair-parabolic shapes, including bounded-length words with collapsing placements and a count-uniform necessary expenditure under its narrower hypotheses:
https://github.com/Sodelin/Research-Commons/blob/efd8ed7a9d23be13eede73019618c4cd4b62c23e/research/2026-10-08-dot-g4-fair-energy-hazard-1220z/README.md

Those results and their attribution are retained. The present theorem instead uses complete cap six, a fixed cell-count bound and arbitrary sufficiently small fair arm means, without compact common-scale shape restrictions. It does not inherit the earlier count-uniform conclusion. No historical novelty is asserted. The precise advance within this continuation is combining the reviewed sixth-root aggregate estimate with exact fourth diagonal calibration to rule out the previously remaining bounded-size all-small multiscale branch.
