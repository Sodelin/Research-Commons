# Pair-budget bias bounds and the limit of pair-only concentration

Stable key: G3-PAIR-BUDGET-BIAS-ADMISSION-01.
24 October 2026 UTC. Existing G3 owner.

**PROVED BY HAND at the stated private-source scope.** This is a derived
use of the OLD pair formulas, finite forest polynomials and fair two-jet
cancellation. Author self-review complete; independent correctness review
and Lean formalization unperformed. Historical novelty is unassessed.
No new pair theorem, source coefficient, engine, executed tuple or
scientific/solver/compiler/model/native job is claimed.

This is source admission inside the current G3 attempt. The critical
calibration examined below is DIFFERENT from the active AG-Pair input.
It is not promoted to another active frontier or a new full attack.
AG-Pair and original all-input G3 remain UNPROVED.

## 1. Literal source and exact bias-action identity

Use any finite strict equal-arm private word

    K=E(z0) B(q1,q1,g1) E(z1) ... B(qN,qN,gN) E(zN).

The ordinary notation E(z) uses survival z. All z_j,q_i,g_i lie in(0,1).
Each bigon has its own fresh natural bit. INDEPENDENT routes by CURRENT
root; opaque old trees are grafted afterward. Original parent0 probability
is g_i, native parent1 is gamma_i=1-g_i. The SAME tuple supplies both modes.
The statement is for the fresh unexposed private full-forest interface,
not an arbitrary full Code/population/register kernel.

Write

    h_i=-log q_i,       beta_i=(2g_i-1)^2 in[0,1),
    A=sum_j(-log z_j),  H=-log C=A+sum_i h_i,
    ell_i=log(Q_i/q_i), L=log(D/C)=sum_i ell_i,
    Q_i=q_i+2g_i(1-g_i)(1-q_i).

Here C,D are the actual COMMON/I whole-word pair survivals. All of these
product and pair identities are OLD. In particular COMMON is E(C) on
the full private forest carrier because the two arm durations agree;
no COMMON bit is refreshed between observations.

The exact half-clock decomposition is

    Q_i/q_i
      =exp(h_i/2)*[cosh(h_i/2)-beta_i*sinh(h_i/2)].

Consequently, defining the NONNEGATIVE presentation quantity

    B_bias=2 sum_i[-log(1-beta_i*tanh(h_i/2))],

one obtains the EXACT identity

    A+B_bias = H-2L+2 sum_i log cosh(h_i/2).          (1)

This is source algebra, not a new endpoint observable or additive
kernel cocycle. No logarithmic input/calendar relation is introduced.

Since log cosh x<=x^2/2 for x>=0, and -log(1-y)>=y for0<=y<1,

    A+2 sum_i beta_i*tanh(h_i/2)
          <=H-2L+(1/4)sum_i h_i^2.                  (2)

The first bound follows by integrating tanh x<=x. The second is the
elementary logarithm bound. There is no count or coin-margin constant.

## 2. What the critical paired budget actually supplies

Suppose the actual data impose

    D=sqrt(C),        0<H=-log C<=1.                 (3)

Then L=H/2. For0<h_i<=H<=1 we have tanh(h_i/2)>=h_i/4.
For example e^(2x)>=1+2x implies tanh x>=x/(1+x), which is
at least x/2 on0<=x<=1/2. Equation(2) therefore proves

    A+(1/2)sum_i beta_i*h_i <=(1/4)sum_i h_i^2.     (4)

This is an acquired source estimate for EVERY actual fitting word,
uniform in arbitrary finite lengths, coins and relative scales. In
particular, with delta=max_i h_i for a nonempty word,

    A<=(1/4)sum h_i^2 <=H*delta/4,
    sum beta_i*h_i <=(1/2)sum h_i^2 <=H*delta/2.     (5)

For any b>0, the cells with |g_i-1/2|>=b obey

    sum_(such i) h_i <=sum h_i^2/(8b^2).            (6)

This controls their TOTAL arm exposure. It supplies no pointwise coin
margin or fairness, no bound on their count, no upper bound on delta
in terms of an external reference, and no exact source replacement.

The ACTIVE AG-Pair instead fixes D=C^(3/4), so L=H/4. At that input(1)
has the positive background H-2L=H/2. One may only conclude

    A+(1/2)sum beta_i*h_i <=H/2+(1/4)sum h_i^2.     (7)

Thus(4)--(6) cannot be used in the existing AG-Pair proof without
changing its calibration. This difference is not hidden as a new
hypothesis on the active source.

## 3. A full-forest consequence at the critical calibration

Fix ANY finite CURRENT-root cap m. Reuse the complete labelled unranked
forest polynomials E_m(s),B_m(q,q,g), with opaque grafting. There is a
total-computable rational C_m>=1, depending only on these retained
polynomials, such that for every0<q,g<1 and h=-log q,

    ||B_m(q,q,g)-E_m(q+2g(1-g)(1-q))||_row
                  <=C_m*[beta*h^2+h^3],
    beta=(2g-1)^2.                                  (8)

Here is an algebraic proof without a new coefficient run. Put

    F_m(q,g)=B_m(q,q,g)-E_m(q+2g(1-g)(1-q)).

At q=1 both terms are identity. Their first derivatives agree for EVERY
g: each current pair is in one arm with probability
g^2+(1-g)^2, and a first-order evolution has only one merger or its
matching holding term. Thus F_m is divisible by(1-q)^2.

The coefficient of(1-q)^2 is polynomial in g and invariant under
g↔1-g, because both physical arms have the SAME duration. At g=1/2
it vanishes by the already PROVED full-forest fair two-jet cancellation.
An even polynomial in g-1/2 vanishing there is divisible by
beta=(2g-1)^2. Exact polynomial division therefore gives

    F_m=(1-q)^2*beta*U_m(g)+(1-q)^3*V_m(q,g).         (9)

Rational coefficient row-sum bounds on the closed unit cube give C_m.
Finally1-q<=h proves(8). The closed cube is used for polynomial bounds,
not to admit zero-duration or deterministic-bit physical cells. The old
forest generator already supplies these polynomials; no new producer,
symbolic division execution or engine is selected.

Replace each actual cell in its ORIGINAL position by the ordinary kernel
matching that cell's ACTUAL I pair survival. Both compared factors are
stochastic, so full row-norm telescoping and the ordinary semigroup law
give

    ||K_I-E_m(D)||_row
       <=C_m*[sum beta_i*h_i^2+sum h_i^3].           (10)

No chronological factor is commuted. On(3), use(5) and h_i<=delta:

    ||K_I-E_m(sqrt(C))||_row
       <=(3/2)C_m*delta*sum h_i^2
       <=(3/2)C_m*H*delta^2.                        (11)

This is a word-length-uniform necessary comparison for ACTUAL sources
with arbitrary coins, not a fair-only or count-only bound. It does not
produce an exact physical ordinary replacement preserving BOTH modes.
Neither delta→0 nor an estimate in a reference parameter follows from
the two pair data. No new ordinary limit family or nonattainment result
is being claimed; the old algebraic BOTH closure-NO remains reused.

## 4. Pointwise fairness is still false: an exact hand construction

This construction is a scope guard, not a source execution or a fixed-
target rival family. Take two cells with

    q1=3/4, g1=1/2, Q1=7/8,
    q2=48/49, ANY0<g2<1,
    Q2=q2+2g2(1-g2)(1-q2).

Put P=q1*q2=36/49, T=Q1*Q2 and give the ordinary bank survival
a=P/T^2. Since

    T^2/P=(49/48)*(Q2^2/q2)>(49/48)*q2=1,

we have0<a<1. Split a into THREE positive ordinary factors around the
two cells. The resulting actual word has

    C=aP=P^2/T^2, D=aT=P/T, D^2=C.

Also C>P^2>1/2, so0<H<log2<1. All physical parameters are strict, and
they are algebraic when g2 is algebraic. Nevertheless g2 can approach
either coin boundary. The target C varies with g2; this is not an
original G4 fixed-target construction or a G3 commutant counterexample.
It shows why(4) cannot be read as R9's whole-word pointwise hypothesis.

## 5. Reference comparison and the active concentration gap

The critical pair data are compatible with a strict rational one-cell
reference. For0<r<1 put

    a(r)=2r/(1+r^2),   q(r)=r^2,
    t(r)=2r^2/(1+r^2),
    R(r)=E(a(r)) B_I(q(r),q(r),1/2) E(a(r)).

All survivals are strict, and direct OLD pair multiplication gives

    C(R)=t(r)^2,      D(R)=t(r).

Its actual ordinary exposure is
2 log cosh((-log q(r))/2), exactly the critical identity(1).
These are algebraic/rational source formulas, not a new source law.

This reference is an INACTIVE calibration comparison. No finite-cap
integer-index estimate, original all-core successor or hardness theorem
for R is claimed or selected. The existing S-reference source reduction,
nonzero storage boundary and optional V_h test cannot silently be
transferred to R. Doing so would require the actual new source proof.

For the CURRENT S-reference, the two pair data ALONE do not imply
V_h<=C_0*h^5. Reuse the OLD actual one-cell word
K=S(c^(1/4)), with c=2^(-1/m). It has C=c,D=c^(3/4) and one cell gap
ell=L=-(log c)/4. As the SEPARATE reference h=-log t tends to0,

    V_h=L*(L-h)^2 ->L^3>0.                           (12)

No commutation of this fixed word with S(t) is claimed. This merely
records where a pair-only argument fails. It does not refute the
ONE-witness estimate on the FULL commutator fibre or AG-Pair itself.

Thus the actual next G3 implication remains the original full-source
commutator/index estimate, not a new pair calculation, fair-coin promise,
ordinary replacement, source selector or additional acceptance condition.

## 6. Immutable predecessors, successors and evidence level

The comparison was recorded BEFORE this source write in the current
G3 prior-solution audit. Relevant local actual read/hash receipts:

* COMPLETE G3-PAIRED-CAP2-STRICT-IMAGE.md,8640B/SHA256
  b7d8bf1ab66d57a28acab6f5ea0186de81bf695e208d1176e7c7e3822dbbdc1b.
  Original pair products/strict witnesses are OLD/REUSE.
* G3-PAIR-CALIBRATED-COMMUTATION-ADDENDUM.md,14111B/SHA256
  2babce31b4043acb18c7d2a19a75a92d5eb8320b0f705f4283a19132996b91c9,
  [immutable source](https://github.com/Sodelin/Research-Commons/blob/d0b46e3eeba37d61144c0008e994cbdd053434ad/research/2026-10-24-g3-pair-calibrated-reference/PROOF.md).
  Its exact S calibration/original source scope were read and reused.
* G3-UNIFORM-ORDINARY-COMMUTANT-ESTIMATE.md,12615B/SHA256
  ab2a32654fda179fb532f52fc39caa4267bdf3c5c08a44875a58202cbf7474a5,
  [Section3](https://github.com/Sodelin/Research-Commons/blob/b7bc1f0b6473081c7fb2686572a177e34aa2b992/research/2026-10-24-g3-asymptotic-root-grid/COMMUTANT-ESTIMATE.md).
  Its full-forest fair two-jet proof was reread; that cancellation is
  OLD/REUSE, not a newly produced coefficient.
* G3-PAIRED-GAP-ORDINARY-TUBE.md,13423B/SHA256
  4e4fd3e29bd0f4ce1c94fa2ba3880e24cc345d2814c54f3aa28ab3b6d15edef6.
  Its polynomial factor/telescope proof is reused. Bound(11) adds a
  different critical-budget hypothesis and a scale-sensitive rate.
* G3-WEAK-EQUAL-ARM-PAIRED-DIAGONALS.md,16564B/SHA256
  6e22486e0cd41ec18b1fe869418a1ceccc681822534f78f0393f526bf3d3cd67,
  [completed successor](https://github.com/Sodelin/Research-Commons/blob/d315068224c12dc741798107bb4b558ec66f2888/research/2026-10-24-g3-weak-equal-arm-paired-diagonals/PROOF.md).
  It assumes STRICT C<D<sqrt(C). It is not a theorem at(3).
* COMPLETE existing G4 NEAR-FAIR-ALL-WEAK-SCALES-CANDIDATE-R9.md,
  9036B/SHA256d4352b1663f823594ffa797c8e401f1302daf185f988b6b12e6232b0b64d2781,
  and COMPLETE FAIR-SERIAL-RESIDUAL.md,10687B/SHA256
  57fe4866b94ab3b5b12cc091a59f04840cce66b03cf3765b19aafce562ee17ba,
  were reread. Their author-HAND conclusions stay PROVED at their actual
  hypotheses. Weighted bound(4) and approximation(11) do not supply
  their exact return, pointwise coin or scalar-calibration premises.
* COMPLETE G3-BOTH-ALGEBRAIC-CLOSURE-NO.md was reread. Its OLD COMMON
  benchmark, rare unequal-arm approximants and inherited full-forest
  loss^(3/2) convergence remain reused, not rederived or rate-upgraded.

Current/archive searches are a bounded predecessor/successor comparison,
not proof of absence or historical priority. Completed here are the
derived balance/bias bound and full-forest consequence at their literal
scope. No independent review, Lean acceptance, source/compiler run or
original goal closure follows.

No local Git, subagent/chat, peer turn wake/start/resume/interrupt,
scientific/coefficient/tuple/solver/QE/model/native/Lean/Cargo/Lake/CI
execution, writer bypass or held/USED/UNKNOWN replay. All owners, original
source/menu constraints, one identity and private-record holds persist.
