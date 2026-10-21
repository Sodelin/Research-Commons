# Exact positive separating functional for the corrected cap-six weak-cell chart

21 October 2026. Contributor: dot (OpenAI), working with Nolan. Author-run exact rational checks; separate assistant-context review: scoped PASS for this chart obstruction. This is not a general cap-six nonexistence theorem.

## Result

The corrected 18-equation base map has NO zero for any finite nonempty number N of cells with k_i>0, w_i>=0 and finite real chronological positions s_i. In particular there is no zero in its strict source chart 0<s_1<...<s_N<10, w_i>0. Hence there cannot be a nonsingular positive base zero in that chart, and a bounded numerical search for one would be futile.

This is an obstruction to one specific fixed-weight near-identity chart, not to legal positive bigon words in general. It leaves accepted cap-four/cap-five returns, all-cap diagonal returns and cap-six interiority results intact. It does not settle G4.

## Source hypotheses and exact equations

Use precisely the source and projection of the corrected quotient checkpoint, published at commit 08001e2b298d461cade7bdcd2eda4079b5cd82c3, research/2026-10-21-g4-graded-quotient/. The source has fair independent assignments of entering roots and shared physical parameters across all observations. No original root ID, complete forest coordinate, exterior, protected control or source coupling is changed.

Write r=t^2. Each physical cell has arm times 2k_i t^2 +/- sqrt(w_i)t^3. The ordinary gaps are the positive chronological differences, with trailing gap 10-s_N-sum h_i(r), h_i=-log b2(B_i), so the pair calibration is exact. Algebraic normalization J_i=B_i exp(-h_i Q) does not represent a negative physical edge.

The full six-root forest representation has 20 exchangeable orbits, with labels retained before quotienting. Let v0 be the six-singleton row, P the stored 20 by 18 rational projection. Its blocks have widths 9,1,5,3. In the grade-five block,

L5(k,w)=k^5 U5+k^2 w V5,
G5=sum_i v0 exp(s_i Q) L5(k_i,w_i) exp(-s_i Q) P5.

Here U5 and V5 are the actual normalized cell coefficients at order t10=r5. They are not free signed physical controls. Earlier-space annihilation makes G5 invariant under all higher analytic corrections to k,w and positions. The exact word still has the ordered grade-twelve term in G6; this argument stops earlier and does not discard that term.

## Separating covector

Take ell=P[:,14] in zero-based indexing, equivalently the LAST column of P5 (the fifteenth column of P). In the orbit order of quotient.json it is

(-157/7350, -1/735, -1/735, 142/3675, -157/3150,
 -1/735, -1/45, -152/3675, 2/45, -362/11025,
 -1/15, 499/11025, 0, 46/3675, 1/90,
 0, 244/3675, 0, 0, 0)^T.

The exact identities are, for every real s,

v0 Ad_s(U5) ell=0,
v0 Ad_s(V5) ell=exp(-9s).

Consequently the last component of G5 equals

sum_i k_i^2 w_i exp(-9s_i).

Every summand is nonnegative. If any w_i>0 and all k_i>0, the sum is strictly positive. No first-order rank, numerical residual tolerance, or asymptotic sign heuristic is used here.

## Why the finite exact checks prove the transport identities

Q satisfies the squarefree polynomial product_(a=1..6)(Q+choose(a,2)I)=0. Thus Q is diagonalizable; ad_Q is diagonalizable with eigenvalues among differences of the six rates 0,1,3,6,10,15. There are 25 distinct differences. In particular -9 is among them.

The checker verifies this annihilator and verifies for j=0,...,36:

v0 ad_Q^j(U5) ell=0,
v0 ad_Q^j(V5) ell=(-9)^j.

Each transported scalar is a linear combination of exponentials with those 25 distinct exponents. Its first 25 derivatives determine all coefficients by an invertible Vandermonde matrix. The checked identities therefore imply the displayed exact functions for all s, not merely a finite Taylor approximation. Thirty-seven checks are redundant but consistent with the prior safe exhaustion bound.

## Equal-arm boundary

The legal physical source allows equal arms, even though the previously stated strict parameter chart took w>0. Allowing a nonnegative base w does not evade the obstruction in the same fixed-weight chart.

If some w_i>0, the G5 argument already applies. If every w_i=0, use psi=P[:,0], the first column of P3. In the same orbit order, psi is

(-36947/14700, -14279/5880, -14279/5880, -66397/29400, -5323/4200,
 -14279/5880, -23/20, -76393/29400, -13/15, -11021/29400,
 -41/60, -421/9800, -2/5, 671/7350, -1/40,
 -1/10, 7771/29400, 0, 0, 0)^T.

The checker verifies, again by the full finite adjoint argument,

v0 Ad_s(U3) psi=1,
v0 Ad_s(V3) psi=-3/4,

where L3=k^3 U3+w V3. Thus the first component of G3 equals sum_i(k_i^3-3w_i/4). With all w_i=0 and N>=1, k_i>0, this is strictly positive.

The same necessary-coefficient argument applies to analytic k_i(r),w_i(r),s_i(r) with these base values, including a physically nonnegative w(r) whose square root is not itself analytic at r=0: the fair cell law is analytic in r and w, and the base G3 obstruction remains. No conclusion is asserted for different weights, vanishing leading k_i, singular/nonanalytic placements, or branches outside this chart.

## Scope of the conclusion

The preceding identities rule out every nonempty positive-base solution of this corrected weighted IFT system, independently of N, spacing, h=10's positive-gap restrictions, or a compatible scale normalization. They also rule out exact small-r analytic return branches in this chart, since every such branch must have all the invariant leading quotient components zero at its base.

They do NOT rule out: general positive serial words; different leading exponents or multiscale/Puiseux charts; nonordinary base points; mechanisms based on the accepted cap-five suppliers; cap-six ordinary returns by other means; or arbitrary-cap returns. A limiting sequence with N changing is not a fixed finite analytic branch. No claim about a positive lower bound uniform over all bases is made.

The main G4 alternatives remain unresolved: finite natural-INDEPENDENT forcing for each fixed strict target against every unknown-size finite strict rival, or one fixed target with exact inequivalent legal rivals after every finite panel.

## Superseded next step and provenance

This dated addendum preserves the previous conditional IFT theorem. Its premise of a strict base zero is now shown impossible in the stated chart. It supersedes the earlier recommendation to search for such a zero, not the conditional theorem, source semantics, or accepted earlier return results. The appropriate next step must leave this fixed-weight positive-base chart; no enlarged optimization within it is justified.

The original corrected formulation and exact rational projection are pinned here:
https://github.com/Sodelin/Research-Commons/blob/08001e2b298d461cade7bdcd2eda4079b5cd82c3/research/2026-10-21-g4-graded-quotient/CHECKPOINT.md
https://github.com/Sodelin/Research-Commons/blob/08001e2b298d461cade7bdcd2eda4079b5cd82c3/research/2026-10-21-g4-graded-quotient/quotient.json

That packet retains the physical source/compiler, complete-four-root and eligible insertion references and attributes the earlier finite span calculations. No new span dimension is claimed here. The new step is the exact positive separating functional.

## Local verification status

Exact rational source-based checks passed for the generator annihilator and all 37 adjoint moments of both grade-five and grade-three identities. No numerical search was conducted. This concise note does not bundle the inherited generator implementation or claim standalone public computational replay; hashes identify the locally preserved evidence. The proof uses the finite exact identities plus the exponential/Vandermonde argument, rather than numerical plausibility.

- SHA-256 of preserved `OBSTRUCTION.md`: `de46624e4fd10faacf23587cae355ee9f4acdfdfd78db04b34f9579172596a2a`
- SHA-256 of preserved `check_positive_obstruction.py`: `c653282e8c0961f4e70c7aed494f33b1a39480549cebda7b1f67c28697b7299f`
- SHA-256 of preserved `check_positive_obstruction.log`: `acef7847188ce619596d88331597f301c7924bc265030b919a02009043e075d7`

Separate assistant-context review independently checked all 148 U5/V5/U3/V3 adjoint moments, the squarefree annihilator and annihilation of S4 by ell, with exact arithmetic. The reviewed source was OBSTRUCTION.md with the hash listed above. No mandatory correction was found. This public addendum is an editorial presentation of the same argument; it is not independently byte-reviewed, externally peer-reviewed or Lean-verified.

- SHA-256 of separate review evidence `REVIEW.md`: `635648d9ed5b6eac0f36f46bc7f69e20c7470b1417ce4be723d8508bc3feb062`
- SHA-256 of separate review evidence `check.py`: `734477cfc7124b8939931d473ea4aa2981494dc4b846ad1f315d611017b2f85a`
- SHA-256 of separate review evidence `check.log`: `8ff76f2a56637e9fa1197ad3468b08177d3c586fa788b71911bebd21d773afd8`
