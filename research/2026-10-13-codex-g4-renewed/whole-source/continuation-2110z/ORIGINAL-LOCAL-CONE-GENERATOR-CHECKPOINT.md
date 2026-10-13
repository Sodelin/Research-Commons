# Original local exclusion: exact port identity and remaining observable cone

Contributor: Codex whole-source lane, with the Codex lead's fixed-profile
and observable-secant reductions. 13 October 2026.
**Hand-derived identity and unresolved proof checkpoint.** No original
local exclusion theorem or G4 closure is claimed. The private generator
identity is inherited; the observation here is its validity before an
arbitrary mixed meeting continuation when its derivatives are taken in
the two initial exclusive arm populations.

## Exact routing identity before an arbitrary continuation

Let R_g route n current A roots independently into two ports, with
probabilities g and q=1-g. Preserve their already formed opaque trees.
Let Q act on the single input A population and let Q_0,Q_1 act on the
two output populations separately. In source-composition order,

    Q R_g = (1/g) R_g Q_0 + (1/q) R_g Q_1
                                      + (gq/2) partial_g^2 R_g.       (1)

The convention in (1) is that a product performs the left operation
first. To check an off-diagonal pair merger, if the merged pair uses
port 0, routing after its input merger gives the weight of the original
assignment divided by g. This is exactly its Q_0 contribution; similarly
for port 1. Different-port pairs never merge in either construction.
For an assignment with k roots in port 0 and d=n-k in port 1, its routing
weight is w=g^k q^d. The right side's diagonal divided by w is

    -lambda_k/g-lambda_d/q
      +(gq/2)[k(k-1)/g^2+d(d-1)/q^2-2kd/(gq)]
    =-lambda_k-lambda_d-kd=-lambda_n.

Thus (1) is an exact identity on labelled forest states at every cap.
Composing any subsequent joint A/B source kernel preserves it. The
continuation need not wait for the A arms to pool before contacting B.

Specifically, insert ordinary populations of durations u_0,u_1 directly
above the split, before either port contacts B. Their duration derivatives
realize Q_0,Q_1. They may be auxiliary zero-duration pads in the derivative
calculation; this does not authorize a new physical observer or violate
physical parameter ties. An actual allowed tangent must still be shown
to realize the required changes through the original parameter chart.

It would be wrong to replace these derivatives by changes of the TOTAL
single-A arm durations when those totals include mixed A/B populations.
The explicit initial exclusive populations are what make (1) valid for
an arbitrary upper meeting continuation.

## Why the fair and endpoint issues are genuine

At g=1/2, if the entire composed response is even in h=g-1/2, use the
fold coordinate p=gq=1/4-h^2. Then partial_p=-partial_g^2/2 at the fair
point, and (1) becomes

    Q F=2(F_(u0)+F_(u1))-F_p/4.                     (2)

The familiar first-order zero direction is

    preceding gap: 4r,
    each initial exclusive arm: -8r,
    p: r,

with r<=0 on the physical side of the fair fold. Its COMMON duration
change on either route is -4r>=0. This is the inherited private fair
cost mechanism, expressed before an arbitrary continuation.

For a mixed meeting core, equal TOTAL A arms do not imply that its full
joint response is even in h. Port exchange can change the B interaction.
One must therefore either prove the required response symmetry, or keep
the raw coin and its first and second derivatives. Coin directions at
different retained sites may interact. Equation (2) must not be applied
merely because the single-A restriction has an equal fair cell.

There are also genuine higher-order boundary scales. For a two-arm cell
whose zero-duration arm is chosen with probability 1-epsilon and whose
positive-duration arm b is chosen with probability epsilon, its exact
fresh-root no-merger diagonal is

    d_n(epsilon)=sum_(r=0)^n binom(n,r)
                    epsilon^r(1-epsilon)^(n-r) exp(-b lambda_r)
                =1-lambda_n(1-exp(-b))epsilon^2+O(epsilon^3).

The corresponding COMMON diagonal is

    1-epsilon[1-exp(-b lambda_n)].                  (3)

Thus its COMMON and INDEPENDENT deviations can have different orders.
These are exact source-kernel identities, not additional original
observations. Postcomposing ordinary completion can erase further leading
terms. No inverse bound follows from all-law identifiability alone.

## The finite exact COMMON chart and the sharper remaining obligation

The lead's current fixed-profile reduction retains the actual parameter
ties. After choosing one finite skeleton/palette and collapsing only
equal private blocks in COMMON, each bounded routing assignment sigma
has positive weight in every actual rival. Its displayed full ordinary
profile therefore belongs to the fixed finite target support S. On one
subsequence its assignment to S is constant, say pi(sigma). For exposure
coordinates l and collapsed block clocks, this imposes exact equations

    M_sigma l = l_(pi(sigma)),
    sum_(sigma:pi(sigma)=s) w_sigma(gamma)=w_s.      (4)

M_sigma is the path-incidence matrix for that resolved shape. An endpoint
coin in the LIMIT does not remove its equation: it is inherited from
positive actual weights. These equations do not automatically identify
each coin when profiles collide, or make a zero edge a free parameter.

The lead also gives a Noetherian reduction which avoids a parameter
inverse. For a finite body chart at theta_*, let f_o(theta) be its original
INDEPENDENT row difference. Choose finite ORIGINAL ideal generators
f_1,...,f_d, so f_o=sum_i h_oi f_i. If collapsed body points theta_j tend
to theta_* and their generator differences are O(S_j), then along a
subsequence f_i(theta_j)/S_j tends to a_i, and every row's scaled body
change is sum_i h_oi(theta_*)a_i. Fair or boundary parameter displacements
may be much larger than S_j. They are retained in this observable secant
cone rather than discarded by an unjustified derivative assumption.

The missing statement is consequently precise. Inside the ACTUAL
COMMON-fibre chart (4), show that no observable secant direction produced
by finite bodies can cancel the limit of arbitrary-count positive weak
cell insertions, unless their total strength vanishes. It must include
raw fair-coin folds, endpoint sites and zero-edge faces of the original
parameter space. A positive answer would supply the still-missing local
step after finite persistence and the now-reviewed clock-loss rigidity.

The pointwise anchor commonization theorem does not prove this cone
separation: it establishes equality of COMMON laws for exact all-law
INDEPENDENT matches, without a continuity modulus or control of the
relative orders in (3). Equally, Hilbert finite generation alone supplies
finite-dimensional secant data but no sign for their COMMON cost.

One concrete potential next tool is a completed-tree replacement for the
private two-output-root frequency measure. Enumerate finite unions of
internal MRCA clades indexed by finite tuples of leaf pairs and use rapidly
summable parameter-independent weights. At a hybrid-first positive-arm
source the resulting frequency measure has positive deterministic atoms
at g and q; the inherited Dirichlet argument excludes other interior
atoms. A derivative-transfer proof could isolate their highest delta''
terms while retaining joint B decorations. That construction has NOT
been completed here: its domination and unbiased decorated-atom readout
must be proved, rather than inherited from a final-root observation.

Verification: direct labelled-state proof of (1), its stated symmetric
consequence (2), and binomial expansion (3). No computer experiment or
Lean verification was performed. This checkpoint preserves the exact
remaining cone issue, not a claimed local certificate or impossibility.
