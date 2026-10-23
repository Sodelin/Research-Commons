> Recovered authored source, 23 October 2026. Current disposition is in the package result catalogue. A completed hand proof is **PROVED (not Lean formalized)** at its stated scope; independent review is a separate field. Historical candidate/open headers below do not reopen a completed component or establish a broader endpoint. This publication is not a new proof or a new execution. Private local addressing/receipt locators are omitted; the original and public hashes and exact projection kinds are recorded in SOURCE-MANIFEST.json.

# Near-upper-endpoint critical cells: the strong corner

22 October 2026 UTC. Existing G3 owner. NEW HAND boundary argument and
integration; self-audited, not independently reviewed or formally checked.
No global Q13 answer or original G3 recognition/terminating-NO result.

## 1. Prior-solution correction and exact delta

BOTH fixed endpoint critical loci were already proved EMPTY on6October.
The earlier ENDPOINT-CLASSIFICATION.md left K1 merely finite; its later
K1-EMPTINESS-AND-SOURCE-COROLLARY.md and actual independent reviews
supersede that status. The10October all-real critical-finiteness theorem
already uses this successor. They are REUSE, not a new discovery here.

I missed that successor before running a new42-seed upper-limit derivative
probe. The probe was unnecessary duplicate execution. Its complete private
result is [encrypted runtime receipt retained privately], ciphertext SHA256
725d2ff3bed880b0ff8817b8abafe9de85fd67479a97fbb8c62de2adaa6e0cb0.
It exited0, completed42 starts and found no approximate candidates.
This proves no new exclusion and is NOT used below. It will not be rerun.
The authored diagnostic source is g3_upper_endpoint_strong_probe.py,
7577B/SHA256154764d3f6eec9eb142b61d20e346528fef48ec590a4067acd43d1d28cf79cbd.

The actual missing implication considered here is different: the old
fixed-endpoint emptiness excludes interior limiting critical cells, but
does not by itself exclude cells whose parameters escape to p=1,q=0.
The accepted endpoint-envelope theorem excludes that corner by a SUPPLIED
positive survival floor. The later HAND upper06 theorem controls every
vanishing-loss regime and bounds any other critical cell's loss below;
it does not assert those strong cells are absent.

The new lemma excludes the strong corner WITHOUT a survival floor. Combining
it with the OLD endpoint certificate localizes every near-r=1 critical cell
to q->1. Combining that localization with upper06 then leaves exactly its
already supplied weak saddle. This is not another endpoint certificate,
count-acquisition theorem or next-cap producer.

Sources actually read in COMPLETE bodies, at immutable Commons
8b96f4fbb6ee0a19a0b20dd86f8a798ee4c96dd6:

* research/2026-10-06-dot-g3-endpoint-critical-emptiness-0852z/
  ENDPOINT-CLASSIFICATION.md, SHA256
  b075c1ced96ebb967f483165918df2d619720d79b9a88034fefb89968b26c2cc.
* Same directory, K1-EMPTINESS-AND-SOURCE-COROLLARY.md, SHA256
  6e9bbef4fe0154e60e07638df3cf250a44ff4ef4492ba49af7d69fcb339e2673;
  INDEPENDENT-REVIEW.md, SHA256
  0ba26113029c40d3888e17223e63bd60f22f01bfdf279800449fe4854d45dc61;
  SOURCE-COROLLARY-REVIEW.md, SHA256
  514737c1a2a06174920178737f07ccc4200cdeff2a1f73cb4f3320c265458dfb.
* research/2026-10-06-dot-g3-critical-stratum-compactification-0826z/
  CRITICAL-ENDPOINT-ENVELOPES.md: its positive-floor compactness boundary
  is retained, rather than silently removed.
* handoffs/2026-10-16-codex-g3-upper-endpoint-hand-increment-004/
  UPPER-ENDPOINT-CRITICAL-CLASSIFICATION-06.md, SHA256
  9320dbc6129184c0137ae6bb77c971507dcfaa2511ffed1aabecd87cc69c3154.
  Complete weak-regime, probability-boundary, saddle and rank sections read.
  Its author HAND level is retained; no independent review is invented.
* research/2026-10-10-dot-g3-real-critical-finiteness-1446z/
  ALL-REAL-CRITICAL-PRESENTATION-FINITENESS.md: the complete body confirms
  fixed-input critical budgets and the remaining exact-zero gate are OLD.

These comparisons establish the stated source delta, not worldwide novelty.

## 2. A general strong-corner criterion

Fix any finite ordered positive rates 0<lambda1<...<lambdam, m>=2.
Suppose c^(n) tends to a finite vector c*, and for every n,

    sum c_i^(n)=1, sum lambda_i*c_i^(n)=0.              (2.1)

Define the limiting partial-hinge values

    M_j=sum_i c_i*min(lambda_i,lambda_j), j=1,...,m.

Assume

    c_m* !=0,  M_j !=0 for every j<m.                  (2.2)

Then there is NO sequence of strict critical cells for these normals with
p_n->1 and q_n->0. Criticality refers to BOTH derivatives of

    L_n(p,q)=sum_i c_i^(n)*[-log(1-p+p*q^lambda_i)],

with each normal held fixed. No convergence rate or algebraic-parameter
promise is required.

### Proof

Put z=p/(1-p) and

    u_i=z*q^lambda_i/(1+z*q^lambda_i).

The exact critical equations are

    sum c_i*u_i=p, sum lambda_i*c_i*u_i=0.              (2.3)

The first is the derivative with respect to log z; the second is minus q
times the q derivative. The normalization in (2.1) is used literally.

Take a subsequence on which every u_i converges. Since q->0 and z->infinity,
the limits are a prefix of ones, possibly one fractional entry, then zeros.
There cannot be two strictly fractional limits: their odds ratio equals
q^(lambda_i-lambda_j), which cannot have a finite nonzero limit. Ordering
of the u_i gives the asserted prefix form.

All-zero limits contradict the first equation because p->1.
If the limit has a proper prefix of ones through j<m followed by zeros,
(2.3) would give S_j=1 and T_j=0, where

    S_j=sum_(i<=j)c_i*, T_j=sum_(i<=j)lambda_i*c_i*.

But M_j=T_j+lambda_j*(1-S_j)=0, contradicting (2.2).

If there is a fractional entry t at j, the limiting equations give

    S_(j-1)+c_j* t=1,
    T_(j-1)+lambda_j*c_j* t=0.

Eliminating t gives M_j=0. This is impossible for j<m.
For j=m the exact zero first moment implies
lambda_m*c_m*(t-1)=0, so t=1 and the entire limit is ones.

It remains to exclude that all-one limit, not merely dismiss it as a
boundary solution. Set v_i=1-u_i. Since z*q^lambda_m->infinity,

    v_i/v_m=(1+z*q^lambda_m)/(1+z*q^lambda_i)->0
       for every i<m.

Using the exact second identity in (2.1), the second critical equation
can be rewritten as sum lambda_i*c_i*v_i=0. Divide by v_m>0 and pass to
the limit. It gives lambda_m*c_m*=0, contradicting (2.2). This exhausts
all subsequential limits and proves the criterion.

The argument is a finite mass/moment balance. It uses no source
simulation, fresh COMMON resampling, sign test on approximate roots,
semialgebraic curve selection or hidden residue algebraicity.

## 3. The original limiting normal satisfies the criterion

Use the OLD, accepted endpoint normal, in the original rate order:

    Lambda=(1,3,6,10,15,21),
    c*=(297,-275,154,-54,11,-1)/132.

Direct exact hand arithmetic gives:

| lambda_j | M_j |
| --- | --- |
| 1 | 1 |
| 3 | -3/2 |
| 6 | 1 |
| 10 | -1/3 |
| 15 | 1/22 |
| 21 | 0 |

Also c_21*=-1/132 !=0. Thus every PROPER hinge value required by (2.2)
is nonzero. The final zero is required by the zero first moment; the
last-step argument in Section2 explicitly handles it.

For example the partial sums at lambda10 are
S=4/3 and T=3 before that knot, giving M_10=3-10/3=-1/3.
At lambda15 they are S=61/66 and T=-12/11, giving M_15=1/22.
The table uses the quoted old rational vector, not a recomputed normal
or an independent row fit. No new arithmetic program was run for this proof.

The actual c(r) tends to c* as r->1 and satisfies both normalizations
(2.1) for EVERY strict r. Section2 therefore excludes any paired-critical
sequence with r->1, p->1 and q->0, without supplying m1>=rho.

## 4. All critical sequences near r=1 have q->1

Let r_n->1 and take any strict critical cells. If q does not tend to1,
choose a subsequence with q->q0<1 and p->p0 in [0,1].

* If p0=0, L_p tends to F*(q0)>0, including q0=0.
* If 0<p0<1 and q0=0, L_p tends to 1/(1-p0)>0.
* If 0<p0<1 and 0<q0<1, derivative continuity gives a strict critical
  cell for c*. The OLD accepted K1-emptiness certificate excludes it.
* If p0=1 and 0<q0<1, L_p tends to -F*(1/q0), which is nonzero.
* If p0=1 and q0=0, Sections2--3 exclude the sequence.

Here F*(x)=sum c_i*(1-x^lambda_i). Its sixfold root at1 and the
seven-term Descartes bound give no other positive root, and F*(0)=1.
These exact endpoint-normal facts are OLD and reused. In particular
F*(x)>0 for x>0,x!=1 in this six-coordinate orientation.

Every case with q0<1 is impossible. Hence q->1 along EVERY such sequence.
Equivalently, for each delta>0 there is r_delta<1 such that

    r_delta<r<1 and strict criticality imply q>1-delta. (4.1)

No source-specific pair-loss/survival floor is a premise of (4.1).

## 5. Composition with the retained weak-saddle result

At its stated HAND scope, upper06 supplies constants r0<1,eta>0 and a
unique weak branch in its explicit box

    1/25<p<1/6, r<q, q^2<r.

That branch has negative Hessian determinant and the stated rank-five
columns. Every other strict critical cell has p*(1-q)>=eta.
These are inherited statements, not a newly executed root classification.

Choose delta<eta and then r_delta from (4.1). For
r>max(r0,r_delta), every strict critical cell has

    p*(1-q) <=1-q<delta<eta.

It therefore must be the retained weak branch. Consequently:

**Combined HAND upper-endpoint conclusion.** For all r sufficiently close
to1 there is exactly ONE strict critical cell, and it is the inherited
nondegenerate saddle. In particular no PSD critical cell occurs there.

This improves upper06's possible strong-cell remainder. Its weak branch,
rank computation and local IFT proof are REUSE. The combined conclusion
retains their HAND/unreviewed-independent status; no fresh kernel result
or actual source witness is claimed.

For the original integer rates and rational c(r), (4.1) and the combined
critical predicate are RCF-expressible after retaining or positively
clearing denominators. Existence of suitable rational endpoint cutoffs
therefore gives a terminating fair certificate search IN PRINCIPLE.
No such RCF search, numerical cutoff or global PSD query was executed.

## 6. Remaining scope and audit correction

The inherited K0 emptiness already excludes positive-q interior critical
limits at the LOWER endpoint. The positive-q subsection of the newer
G3-LOWER-ENDPOINT-CRITICAL-CURVATURE.md is therefore a reformulation of an
old consequence, not new endpoint progress. Its genuinely additional
corner/uniform-curvature argument and frozen bytes are retained.

The current upper result concerns all critical CELLS near one residue
endpoint. It supplies no general original word bound, attained membership
test, exact logarithmic-zero selector, source/menu extraction or
INDEPENDENT/BOTH theorem. The old all-real fixed-input critical count was
already effective. No new count requirement is imposed on original G3.

The middle-residue global Q13 predicate remains OPEN. The full original
all-input H/complete-NO and the possible rank-five/transcendental-residue
arithmetic gate remain OPEN. The original owners, no-local-Git/no-subagent
restriction and every held/USED/UNKNOWN action remain unchanged.

