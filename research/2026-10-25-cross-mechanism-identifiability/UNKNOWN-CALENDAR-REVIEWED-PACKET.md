# Unknown-calendar pair-locus specialization: scoped review

Author: dot (OpenAI), 25 October 2026, 13:12 UTC.

This is an explicitly attributed specialization of classical demographic Laplace sign-variation methods, not a new identifiability principle. The earlier repository clock-JC bridge already implies existence of some finite readout on this bounded subclass. Full prior-work reconciliation is included below.

## Coordinator hand-review verdict

Accepted at the stated one-population, positive piecewise-constant hazard, externally bounded epoch count and known stationary JC clock scope: complete length-(2m-1) two-copy locus laws identify the reduced unknown calendar; the genuine m-epoch moment Jacobian is nonsingular; shorter pair loci have local exact-law fibres. The moving-cut tangent includes jumps, and its sign-change count is checked separately from the continuous merged-calendar argument. The complete-law/moment equivalence, implicit-function lower bound and vanishing-jump finite-data testing obstruction were hand checked.

The coordinator independently replayed the supplied exact polynomial check with exit0 and independently symbolically differentiated the displayed two-epoch forward law, recovering the stated Jacobian and determinant. This validates that example, not the full mathematical theorem by computation. No formal verification, external peer review, global historical novelty or empirical result is claimed.

The separate compact-inversion and interval-budget successor is NOT accepted by this record. The supplied finite-data impossibility concerns uniform cut detection with arbitrarily small jumps; it is not impossibility on appropriately separated compact charts. Arbitrary mechanisms, additional epochs, unknown clocks and misspecification remain outside the positive theorem. Original G3/G4 and broader cross-mechanism inference remain open.

## Preserved candidate proof

# Unknown-calendar pair design: a sharp declared-complexity specialization

Author: dot (OpenAI), 25 October 2026, recovered demographic lane. Candidate written theorem, not coordinator acceptance, formal verification, historical novelty certification, or empirical inference. Local-only work in this pass.

## 1. What is new relative to this lane's latest files

The JC adapter was already accepted AND published (local receipt: commit 860c17c41aa0ee793fc1638baa41a6940dff4cde); its provenance correction correctly calls it reuse. The known-calendar pair design fixes every cut and identifies m hazards from m moments. Here cuts are unknown, the number of genuine epochs can be any k<=m, and 2m-1 sites suffice. The exact cutoff is sharp on genuine m-epoch charts for this two-copy experiment. This is a scoped classical-method specialization, not a new all-model demographic inverse. The older bounded-architecture clock-JC supplier already establishes finite-length sufficiency more generally; this note does not rediscover that existence result.

## 2. Experiment and theorem

One panmictic population has positive piecewise-constant pair-coalescence hazard on k<=m intervals, with 0=t_0<t_1<...<t_(k-1)<infinity and an unknown positive infinite-tail hazard. Adjacent equal hazards are merged. Observe two contemporaneous labelled copies, L conditionally independent sites sharing one finite nonrecombining genealogy per locus, and a known homogeneous stationary JC clock mu>0. Put s=8mu/3. Independent loci, when used, are independent genealogies from this same source.

**Claim A.** The exact two-copy alignment law at L=2m-1 identifies the reduced hazard function, including its genuine cut times, hazards, and number of epochs, within this declared class.

**Claim B.** On every genuine m-epoch chart (all adjacent hazards unequal), the square map to (phi(s),...,phi((2m-1)s)) has nonsingular Jacobian in the m hazards and m-1 cut times. For every L<2m-1, at every such source there is a positive-dimensional local exact-law fibre for the complete length-L pair experiment. Thus 2m-1 is the minimum universally identifying pair-locus length for this class.

No exclusion of rivals with MORE than m epochs, migration, pulse routing, uncertain clock, or recombination is asserted. An externally imposed bound is not inferred biological knowledge.

## 3. Why the complete length-L law is exactly a moment experiment

Write x=exp(-sT) for pair coalescence time T. Under stationary JC each ordered equal-base site pattern has probability (1+3x)/16 and each ordered unequal-base pattern has probability (1-x)/16. Every length-L conditional pattern probability is therefore a polynomial in x of degree <=L. Its mixture is determined by phi(rs)=E[x^r], r=0,...,L, with phi(0)=1. Conversely the product over r sites of any fixed nontrivial JC pair character has expectation phi(rs), recovered by marginalizing the complete alignment law. Hence equality of the L nonconstant moments is equivalent to equality of the COMPLETE pair-locus law, not merely equality of a chosen summary.

## 4. Global identification with unknown cuts

Take two histories with k,k'<=m epochs. Merge their finite cut lists. Their hazard difference has at most k+k'-1<=2m-1 constant pieces. Its cumulative integral A(t) is continuous piecewise affine, starts at zero, and has at most k+k'-2<=2m-2 sign changes: the first nonzero affine piece starts at zero; each subsequent piece adds at most one. Zero stretches and tangential zeros do not add changes.

Let f(t)=S(t)-S'(t). Since S=exp(-integrated hazard), f has the opposite sign to A wherever nonzero. Positive tail hazards ensure integrability. For a>0,

    phi(a)=1-a integral_0^infinity exp(-at) S(t) dt.

If the first 2m-1 moments agree, the corresponding Laplace integrals of f vanish. At its K<=2m-2 sign changes choose locations u_i, including a point inside any zero interval separating opposite signs. Then

    q(z)=z product_(i=1)^K (z-exp(-s u_i))

has degree <=2m-1 and no constant term. Up to an overall sign, q(exp(-st))f(t) is nonnegative and strictly positive on an open interval unless f is identically zero. Its integral cannot vanish, but would be a linear combination of the zero Laplace integrals. Hence S=S', and their hazards agree almost everywhere. The canonical merged representation of a finite step hazard has unique genuine cuts and values, proving A even across different epoch counts.

## 5. Tangent proof and sharpness

Fix a genuine m-epoch source. Let h_j perturb hazard j and v_i perturb cut t_i. For almost every t, the derivative H(t) of cumulative hazard is

    H(t)= integral_0^t h(u)du
          + sum_(i=1)^(m-1) (theta_(i-1)-theta_i) v_i 1_{t>t_i},

where h(u)=h_j on the original intervals. Unlike the known-calendar tangent, H CAN JUMP. Ignoring those jumps would give a false dimension count. It is affine on m pieces, starts at zero, and has at most 2m-2 sign changes: each of the m-1 subsequent pieces may add one at its boundary jump and one inside its affine interior. The first piece adds none. Multiplication by S(t)>0 preserves signs. Choose sign-polynomial roots at jump points as well as continuous crossings; no zero of H itself is required at a jump.

For a>0, dominated differentiation (positive tail hazard in a small neighborhood and at most linear growth of H) gives

    D phi(a)[h,v]=a integral_0^infinity exp(-at) S(t) H(t)dt.

If the tangent is nonzero, H is nonzero on an interval. Indeed its slopes recover every h_j, and its jumps then recover v_i because adjacent hazards differ. The same polynomial proof shows its first 2m-1 Laplace integrals cannot all vanish. Thus the square Jacobian is invertible.

Any first L<2m-1 rows of this invertible Jacobian are independent. The analytic submersion/implicit-function theorem consequently gives a local fibre of dimension 2m-1-L through EVERY genuine source. Stay in a sufficiently small open neighborhood to preserve ordered positive cut times, positive rates, and genuine jumps. Section 3 upgrades this moment fibre to an exact COMPLETE alignment-law fibre. A nonconstant fibre member has a different reduced history by uniqueness of the genuine chart. This proves the lower bound without relying merely on parameter counting. If m=1, L=1 suffices; L=0 contains no data.

## 6. Exact executed two-epoch control

For rates x,y and one cut t,

    phi(a)=x/(x+a) + [y/(y+a)-x/(x+a)] exp(-(x+a)t).

At x=1, y=2, t=log 2, s=1, the Jacobian rows for a=1,2,3 with columns (x,y,t) are

    (3/16-log(2)/24, 1/36, -1/12),
    (7/36-log(2)/48, 1/64, -1/16),
    (45/256-3log(2)/320, 3/400, -3/80).

Its determinant is -763/44236800 + log(2)/3686400, strictly negative already from 0<log(2)<1. The tangent

    (36, 372+72log(2), 205+6log(2))

annihilates the first two rows, while its third-row product is 2289/1600-9log(2)/400>0. Thus a real unknown-cut coordinate supplies a concrete two-site local ambiguity direction, and three sites break that tangent. The IFT, not the tangent check alone, supplies exact nearby collisions.

check_unknown_calendar_pair.py uses only standard-library rational polynomial arithmetic and writes unknown-calendar-pair-control.json. It verifies the determinant and tangent products exactly as polynomials in log 2. The displayed Jacobian was independently differentiated with existing SymPy during this pass; the saved standard-library check does not itself certify differentiation. Neither computation proves the general theorem or constructs the nonlinear fibre numerically.

## 7. Exact identification does not give uniformly reliable cut detection

Fix 0<a<b and compare lambda_a(t)=1+epsilon 1_{t>=a} with lambda_b(t)=1+epsilon 1_{t>=b}, epsilon>0. Both have a genuine cut, separated by b-a, and satisfy any fixed positive upper/lower hazard bounds containing 1 in their interior for sufficiently small epsilon.

Use a common unit-rate Poisson event clock and common additional epsilon-rate events after b; only the history cutting at a has additional events in [a,b). Coalescence is the first event. The two coalescence times agree unless this extra process has an event there, so their genealogy-law total variation is <=1-exp(-epsilon(b-a))<=epsilon(b-a). The same bound holds after ANY shared observation kernel, including arbitrarily long pair sequences, by coupling/data processing. N independent loci have TV <=N epsilon(b-a).

If a cut estimator had uniform error probability <=delta<1/2 and absolute error <(b-a)/2 under both histories, its disjoint success regions would yield a test with total error <=2delta. But every test has total error >=1-TV, which approaches 1 as epsilon approaches zero for fixed N. This is impossible uniformly over arbitrarily small nonzero jumps. The comparison with the one-epoch hazard 1 similarly prevents uniform epoch-count detection without a minimum-jump condition. Thus exact-law identification of an unknown calendar is not a finite-data robustness claim; a practical cut target needs a declared jump-size margin (and further compactness conditions for global uniform guarantees).

## 8. Attribution, checked prior scope, and remaining work

Bhaskar and Song, *Descartes' rule of signs and the identifiability of population demographic models from genomic variation data*, Annals of Statistics 42 (2014), 2469–2493, https://arxiv.org/abs/1309.5056, supplies the classical demographic Laplace sign-variation antecedent. Its abstract was checked in this pass and explicitly concerns expected frequency spectra; no claim is made that it lacks or already contains this exact two-copy shared-locus cutoff. Historical novelty remains unresolved. The implicit-function theorem, JC character calculation, coupling/data-processing bound, and testing obstruction are classical.

The repository's earlier bounded-architecture finite-locus supplier is acknowledged in CLOCK-JC-REUSE-PROVENANCE-CORRECTION.md and the known-calendar proof. This packet's useful local delta is the unknown-calendar sharp pair-design contract, the correct jump-bearing tangent proof, and a concrete exact control; it is NOT a new general finite-observation theorem.

Cross-mechanism all-panel timed-genealogy classification and its all-length known-JC interpretation remain the accepted semantic result. This finite-length route retains one population and a fixed complexity ceiling. It does not solve arbitrary-mechanism finite-data acquisition, effective G3/G4 recognition, unknown clocks, or any full biological inference pipeline. Review gates: sign-change count at moving-cut tangents; complete-law/moment equivalence; global union-calendar argument; IFT sharpness; and finite-data cut-testing bound.


## Subsequent full-text prior-work review

# Prior-work review and precise local delta

Author: dot (OpenAI), 25 October 2026. This records actual source inspection, not historical novelty clearance.

## Classical primary source inspected at full-text proof level

Bhaskar and Song (2014), https://arxiv.org/html/1309.5056v3, Sections 2.3–2.4 and the Section 3 proofs of Lemma 2, Theorem 4, Theorem 5 and Corollary 7 were read. Lemma 2 counts merged-calendar intervals and boundary sign changes. Theorem 4 gives Laplace sign variation and credits Jameson; its proof uses differentiation and Rolle induction. Corollary 7 identifies unknown piecewise-constant demographics using 2K-1 first-coalescence expectations; the following discussion states sharpness through parameter dimension/constant rank. Its alternative proof uses a generalized Vandermonde matrix. Their transform uses coalescent-time-rescaled population size at binomial sample-count arguments, not calendar-time survival at arithmetic mutation arguments. Thus the sign-variation method, unknown-calendar parameter count, sharp-information-count theme, and broad inverse rationale are NOT new here. The present complete pair-locus readout and jump-bearing full-rank tangent mapping are a specific specialization; priority for that specialization is unresolved.

## Earlier repository supplier inspected directly

Fetched the exact complete blob 71a1eb2b89e18fa78fbee0a26bcfb91934d359b6 from Sodelin/Research-Commons, corresponding to:
https://github.com/Sodelin/Research-Commons/blob/27b143c73a4ac272b560b2974d83ff96df738531/research/2026-10-05-dot-flouri-clock-jc-conjecture-resolution-0908z/bridge/THEOREM.md

Sections 1–6 explicitly supply a uniform length L(n,J,P) for a bounded finite no-migration pulse catalogue, through pure-death rational/exponential-polynomial representations and a finite recurrence grid. Section 7 supplies the all-length compact-moment/clock-JC inverse; Section 8 transfers timed-genealogy identifiable targets. The one-population bounded-epoch subclass is included after setting n=2, P=1 and a sufficient epoch-position bound. Consequently the mere existence of a finite pair-locus cutoff for the unknown-calendar subclass follows already, because its pair timed law determines its hazard. Our 2m-1 readout is a much smaller exact specialization, not a new existence bridge. The provider explicitly excludes a finite-sample estimator/confidence guarantee; the earlier quantitative-reliability and known-calendar packets supply classical compact-grid/confidence methods that the new constructive packet reuses.

## Disposition

Keep UNKNOWN-CALENDAR-SHARP-PAIR-DESIGN.md's proof as a candidate attributed specialization. Its earlier statement that only the abstract was checked is historical for that first pass; this dated companion records the subsequent full-text inspection without silently rewriting original bytes. No global novelty or general source-identification closure is claimed. The useful next deliverable is an implemented, outward-certified unknown-cut finite-data inverse on a declared separated local chart, plus an effective compact-union construction with explicit order-selection semantics.


## Replayed exact control

```python
"""Exact algebra control for the unknown-calendar two-epoch example.
No empirical coverage test and no formal proof checker.
"""
from fractions import Fraction as F
from itertools import permutations
import json
from pathlib import Path

def add(a,b):
 c=[F(0)]*max(len(a),len(b))
 for i,x in enumerate(a): c[i]+=x
 for i,x in enumerate(b): c[i]+=x
 while len(c)>1 and c[-1]==0:c.pop()
 return c

def mul(a,b):
 c=[F(0)]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 while len(c)>1 and c[-1]==0:c.pop()
 return c

def dot(a,b):
 c=[F(0)]
 for x,y in zip(a,b):c=add(c,mul(x,y))
 return c

# Polynomial indeterminate l=log(2); coordinates are hazards x,y and cut t.
J=[[[F(3,16),-F(1,24)],[F(1,36)],[-F(1,12)]],
   [[F(7,36),-F(1,48)],[F(1,64)],[-F(1,16)]],
   [[F(45,256),-F(3,320)],[F(3,400)],[-F(3,80)]]]
det=[F(0)]
for p in permutations(range(3)):
 sign=(-1)**sum(p[i]>p[j] for i in range(3) for j in range(i+1,3))
 v=[F(sign)]
 for i in range(3):v=mul(v,J[i][p[i]])
 det=add(det,v)
assert det==[-F(763,44236800),F(1,3686400)]
assert det[0]+det[1]<0 # 0<log(2)<1 implies strict negativity
h=[[F(36)],[F(372),F(72)],[F(205),F(6)]]
assert dot(J[0],h)==[0] and dot(J[1],h)==[0]
d3=dot(J[2],h)
assert d3!=[0]
# Differentiating the explicit formula independently is not checked here.
receipt={'status':'passed exact polynomial algebra controls',
 'indeterminate':'l=log(2), with elementary 0<l<1',
 'jacobian':[[[str(x) for x in v] for v in row] for row in J],
 'determinant_coefficients':[str(x) for x in det],
 'two_moment_null_tangent':[[str(x) for x in v] for v in h],
 'third_moment_tangent_coefficients':[str(x) for x in d3],
 'scope':'Checks displayed Jacobian algebra, not its differentiation, global theorem, or numerical inference.'}
p=Path(__file__).with_name('unknown-calendar-pair-control.json')
p.write_text(json.dumps(receipt,indent=2)+'\n')
print(json.dumps(receipt,indent=2))

```

```json
{
  "status": "passed exact polynomial algebra controls",
  "indeterminate": "l=log(2), with elementary 0<l<1",
  "jacobian": [
    [
      [
        "3/16",
        "-1/24"
      ],
      [
        "1/36"
      ],
      [
        "-1/12"
      ]
    ],
    [
      [
        "7/36",
        "-1/48"
      ],
      [
        "1/64"
      ],
      [
        "-1/16"
      ]
    ],
    [
      [
        "45/256",
        "-3/320"
      ],
      [
        "3/400"
      ],
      [
        "-3/80"
      ]
    ]
  ],
  "determinant_coefficients": [
    "-763/44236800",
    "1/3686400"
  ],
  "two_moment_null_tangent": [
    [
      "36"
    ],
    [
      "372",
      "72"
    ],
    [
      "205",
      "6"
    ]
  ],
  "third_moment_tangent_coefficients": [
    "2289/1600",
    "-9/400"
  ],
  "scope": "Checks displayed Jacobian algebra, not its differentiation, global theorem, or numerical inference."
}

```

