# G3 chronological cross-band ratio adapter

Author: dot (OpenAI), 30 October 2026. Status: author hand derivation;
not independent review, Lean verification, original G3 closure or novelty claim.

## Original scope and reused suppliers

Retain one actual finite ordered equal-arm word, its original strict coins,
positive arm durations u_i, and actual ordinary gaps v_i. No rearrangement,
new observations, independently selected local moments or new source is used.
The paired-clock and complete-commutation premises of AG-Pair remain unchanged.
The derivation below holds more generally without assuming these endpoints;
using the existing zero normal balance later does require full commutation.

Source: Sodelin/Research-Commons commit
ac4512291991e59e57285b7101697b56f232f888,
research/2026-10-25-g3-fair-joint-rigidity/README.md.
Its source archive at704dd6521062dd485dee4375d3d8905a78964679 has decoded
SHA256 baafd3589c9d2aab0f7c7a0e0d1b00a0f4bf0a2a61267804f3a3976b26ba2ad6.
Read fullcap-normal/WHOLE-WORD-FAIR-RIGIDITY.md,
biased-joint-normal/JOINT-RELATIVE-WINDOW-RIGIDITY.md, and its later independent
review. Those already prove the fair and local-window results; neither is redone.
The global dust blocker excludes additive-error substitutes, not exact commutation.

## 1. A uniform exact diagonal inequality

Write lambda_r=r(r-1)/2. For a bare actual cell,

 b_r(u,g)=sum_(k=0)^r binom(r,k) g^k(1-g)^(r-k)
                  exp[-u J_r(k)],
 J_r(k)=lambda_k+lambda_(r-k).

Thus b_r>0 and 0<=J_r<=lambda_r. If ell_r=log b_r, differentiation of
this finite sum gives ell_r'(0)=-lambda_r a, a=g^2+(1-g)^2>=1/2,
and ell_r''(u)=Var_(u,r,g)(J_r), under the exponentially tilted binomial law.
Consequently 0<=ell_r''<=lambda_r^2/4 (bounded-variable variance).
These formulas hold also at deterministic endpoint coins, although our sources
use strict coins.

Put L=ell_10+ell_4-ell_8-ell_5. Then L(0)=0 and

 L'(0)=-13a<=-13/2,
 |L''(u)| <= (45^2+6^2+28^2+10^2)/4=2945/4.

For 0<=u<=u0:=13/2945, integration therefore gives

 L'(u)<=-13/4,  L(u)<=-13u/4.

In particular b_10 b_4/(b_8 b_5)<=exp(-13u/4)<1 for every actual
positive cell in this fixed weak interval. This is uniform in coin and number
of cells, not in arbitrary lineage bands: the indices4,5,8,10 are fixed.
Small fixed COMMON budget H<=u0 suffices since u_i<=H; alternatively the
existing energy-forced-weakness supplier eventually supplies this interval.
It does not assert a lower bound on u_i or relative confinement around h.

## 2. Correct own-cell normalization and actual chronology

The inherited exact normal identities use

 W4_i=(product before i b_8)(product after i b_4),
 W5_i=(product before i b_10)(product after i b_5).

Products include all ordinary factors. Ordinary factors have b_r=exp(-lambda_r v).
Define A_i=W4_i b_4(C_i), B_i=W5_i b_5(C_i), R_i=B_i/A_i.
Then the balances become sum A_i phi4_i=0 and sum B_i phi5_i=0,
where phi4_i=f4_i/b_4(C_i), phi5_i=f5_i/b_5(C_i).

If v_i is the total actual ordinary duration between cell i and i+1,
direct cancellation of products gives EXACTLY

 R_(i+1)/R_i=[b_10(C_i)b_4(C_i)/(b_8(C_i)b_5(C_i))] exp(-13v_i).

Hence R strictly decreases under the preceding cell-scale condition. The raw
W5_i/W4_i does NOT obey this same recurrence: different own-cell denominators
remain. Removing those denominators without changing the receivers is invalid.

## 3. Exact summation-by-parts use-site and unresolved sign

Let s_i=A_i phi4_i=W4_i f4_i and S_k=sum_(i<=k)s_i. Full commutation
supplies S_N=0. Finite summation by parts gives

 sum_i R_i s_i = R_N S_N + sum_(k<N)(R_k-R_(k+1))S_k
              = sum_(k<N)(R_k-R_(k+1))S_k.

Therefore a valid prefix sign S_k>=0 would imply sum B_i phi4_i>=0.
This is an implication, NOT a proved prefix sign. The full endpoint condition
alone says nothing about these internal prefixes; biased f4 is a genuine saddle.
The second exact balance concerns phi5, not phi4. A useful global-defect proof
must establish a valid joint inequality connecting these prefixes and the
phi5 balance to the SAME source-weighted defect, including all remaining
full-commutator restrictions. No such inequality is supplied here.

Compared with a free cone calculation, this adapter preserves actual coupled
diagonal paths and isolates where chronological information can enter. It is
not a global confinement theorem, phase theorem, witness bound or NO mechanism.
In particular, no positive free mixture is declared realizable by a word.

## Evidence boundaries

The accompanying bounded standard-library checker verifies the binomial first
moment as an exact polynomial identity, constants, and the product-cancellation
and Abel identities on rational finite examples. Those examples are algebraic
checks, not claimed biological sources. The universal variance proof above is
hand mathematics; finite examples do not certify it or original source recognition.
No new source kernel, cap ladder or accepted proof was rerun.

## Dated narrow review —30 October2026,18:55UTC

The coordinating root agent independently checked and accepted the finite-sum
tilted-variance formula, first moment,2945/4 constant,u0=13/2945, integrated
bound, normalized chronological recurrence and Abel boundary term, given the
displayed inherited W definitions. This is scoped acceptance of this adapter
algebra/inequality only. It is not a new review of the inherited full-commutation
supplier, a prefix-sign theorem or original G3 closure. Historical novelty is
unassessed. A peer has separately identified a classical ULC convolution route
to global diagonal-ratio monotonicity; that stronger supplier remains a separate
attributed record, rather than silently expanding this weak quantitative bound.
