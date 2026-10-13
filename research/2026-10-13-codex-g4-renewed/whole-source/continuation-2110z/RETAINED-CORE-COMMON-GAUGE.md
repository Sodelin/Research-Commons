# A strict retained-core gauge inside one full COMMON fibre

Contributor: Codex whole-source lane, 13 October 2026, continuation 2110z.
**Hand-derived example with separate exact finite controls.** No independent
review, Lean verification, or general G4 impossibility is claimed.
This makes the finite private-factor ambiguity in the earlier
[normalized invariant theorem](../continuation-1900z/ANCHOR-AND-MEETING-INVARIANT.md)
explicit in an original source with a retained two-hybrid blob. It is a
scope test for that bridge, not a new finite-forcing theorem.

## One source graph and a strict one-parameter family

Take root R; tree vertices U,P0,P1,Q; hybrids HA,HC; and the four labelled
leaves A,B,C,D. The arcs are

    R->U, R->Q,
    U->P0, U->P1,
    P0->HA, P0->HC,
    P1->HA, P1->D,
    Q->HC, Q->B,
    HA->A, HC->C.

All unspecified edge survivals are 1/2. Set

    x(P0->HA)=s/2,  x(P1->HA)=s/3,  x(HA->A)=1/(4s),
    gamma_HA=2/5,   gamma_HC=3/7,
    1/4 < s < 2.

Every finite edge then has strictly positive finite exposure and every
coin is interior. The degrees are the original binary degrees; hybrid
child edges are leaf bridges. R is the LSA because every root path to D
uses U while every root path to B uses Q. For the outer-labelled embedding,
use the cycle R,Q,HC,P0,HA,P1,U,R and the chord U,P0, with the four labelled
leaf edges outside. Thus the full graph is admitted. Its two cycles share
U--P0 and belong to one retained blob; no private-source replacement or
extra actuator is used.

## Entire COMMON law unchanged

Fix either original COMMON bit at each hybrid. After the resolution, the
path from the retained parent of HA to A has survival

    (s/2)/(4s)=1/8, or (s/3)/(4s)=1/12.

HA is unary in that displayed tree and disappears under suppression.
Every other edge, and every routing weight, is independent of s. Hence
the entire conditional ordinary population profile is independent of s
for EACH of the four full COMMON assignments. This proves equality of
the whole COMMON law at all allocations, with shared tuples, not just
equality of one observed moment or one displayed topology.

The four profiles have no common nonsingleton proper clade. In particular
A,B are eligible distinct maximal-cluster anchors in the earlier theorem.

## Entire A/B normalized table unchanged, with a nonconstant gauge

Prune the selected-lineage calculation to A,B, retaining one sample from
other original taxa when obtaining these legal marginal probabilities.
The opened meeting tree has A0,A1 as sisters below U, and B on the other
side of R. The two A-arm survivals from HA up to U are s/4 and s/6.
Put g=2/5, lambda_n=binom(n,2), and

    d_n(s)=sum_(r=0)^n binom(n,r) g^r(1-g)^(n-r)
                               (s/4)^lambda_r (s/6)^lambda_(n-r).

For every allowed Omega_(n,m) topology tau, no A-only merger can occur
before reaching R, and likewise no B-only merger. The exact meeting
response is therefore

    V^s_(n,m)(tau)=(1/2)^lambda_n d_n(s)
                         (1/4)^lambda_m Q_(n+m)(tau).       (1)

Here Q is the ordinary infinite completion law. This is the original
per-current-root INDEPENDENT law. Natural COMMON is used separately in
the preceding section.

For the fixed labelled comb references, Q_(n+1)(C_(n,1))=kappa_(n+1),
where kappa_k=product_(j=2)^k binom(j,2)^(-1). Consequently

    R^s_(n,m)(tau)=Q_(n+m)(tau)/(kappa_(n+1) kappa_(m+1))

for every s,n,m,tau. The exact scalar gauge relative to s=1 is

    a_n(s)=d_n(s)/d_n(1),  b_m(s)=1.

It is a quotient of two genuine finite unequal-cell diagonal sequences.
Its arm difference is fixed, but the common arm baseline changes
continuously. If a=log(4/s), b=log(6/s), then a-b is fixed while the
balance a/(a+b) is nonconstant; the fibre thus includes unrestricted
irrational balances. Neither the complete COMMON law nor this complete
anchor invariant forces a rational-saddle case.

## This is not an indistinguishable-rival construction

The younger A pendant has diagonal (1/(4s))^lambda_n. For the legal
crossed cherry with two A copies and one B copy the actual probability is

    P^s_(2,1)= (1/(4s)) (1/2) d_2(s)/3.

It equals 29/1200 at s=1 and 41/1200 at s=2/3, so one additional legal
INDEPENDENT observation distinguishes these sources. Other anchor pairs
may also detect the shift. The example does not refute an all-pairs
meeting theorem, the bounded finite-physical-gauge conjecture, or G4.
It refutes only an inference of discrete/rational gauge parameters from
the full COMMON law and one complete anchor table R.

## Actual verification

[The exact control script](retained_core_gauge_check.py) reuses the
inherited original source validator/compiler. It checks source admission
at s=1,2/3; equality of all four decorated displayed profiles; the stated
common clade intersection; equality of the whole five-copy COMMON law;
and the two projected INDEPENDENT probabilities above against formula
(1). The [receipt](retained-core-gauge-check.json) records success and
the exact upstream hashes. This is finite rational computation. The
all-arity claims are supported by the hand argument, not by those checks.

Replay from the repository root requires NetworkX; the default Python
environment initially lacked it. The exact successful setup and command
are recorded in the receipt's `execution` field. The dependency was
installed only into `/tmp/g4-whole-source-2110-deps`, then supplied through
`PYTHONPATH`; no repository or global environment dependency was changed.
The lead independently replayed the same command successfully. The initial
missing-dependency failure is an environment issue, not a changed hand-proof
claim.

The original master still requires a finite legal certificate for one
fixed arbitrary admitted target against every unknown-size finite rival.
The accompanying [conditional meromorphic gauge criterion](MEROMORPHIC-GAUGE-CRITERION.md)
identifies an analytic route that would bypass full core reconstruction;
its whole-source hypotheses are not established by this example.
