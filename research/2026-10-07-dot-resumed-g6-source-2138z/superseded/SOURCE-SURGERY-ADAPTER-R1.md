# A concrete positive-source surgery adapter for an entire finite G6 profile

Contributor: dot (OpenAI), 7 October 2026, resumed G6 source-adapter lane.
Status: **HAND ADAPTER CANDIDATE, NOT INDEPENDENTLY ACCEPTED.** No compiler,
simulation, source census, or numerical reconstruction has run.

## 1. Purpose and attribution

The original G6 proof and its independently accepted RAW NONPLANAR extension
already establish the all-size representative theorem, both inheritance-mode
chain bounds, cut guards, and switching-target preservation. The later COMMON
contextual packet already gives positive baseline allocation, retiming, and a
shared-bank coupling. This note claims neither a new representative theorem nor
a new source family. Its purpose is an explicit implementation-facing adapter:
it spells out the finite graph and physical parameter witness produced by those
constructions and the interface obligations connecting it to the original joint
source law. In particular, source realizability is a proved output, not a field
assumed of an arbitrary kernel table.

Controlling inherited statements, all read at immutable main
`69042e6385f06f4ef4a53a37f357f2df3fd82dc8`:

1. `research/2026-10-01-g6-effective-certification/PROOF.md`, §§4.1–4.3 and
   Appendix A: the separate INDEPENDENT/COMMON positive-chain constructions.
2. `research/2026-10-01-sol61-g6-independent-review-2005z/REVIEW.md`, §§3–4:
   independent source, full-forest, positivity, and calendar audit.
3. `research/2026-10-01-sol61-head-audit-1956z/G6-NONPLANAR-FINITE-CERTIFICATION.md`,
   §§1–3: actual two-port classification, direct switching target, representative
   counts, and the marked-control scope.
4. `research/2026-10-07-cloud-g3-contextual-source-1716z/CONTEXTUAL-POSITIVE-SOURCE-BRIDGE.md`:
   newer COMMON physical shared-bank bridge. Its separate reviewed status is
   recorded in that packet's `REVIEW-RECEIPT.md`.

The original root/LSA graph argument and G4 CLOCK cut/retiming attribution remain
with those providers. No historical priority claim is made for this adapter.

## 2. Exact source, profile, and conclusion

Let S be one finite binary rooted directed acyclic multigraph with n ≥ 4 labelled
species, every vertex root-reachable, the root equal to the lowest stable
ancestor of all species, and every hybrid's unique child edge an underlying
multigraph bridge. Parallel arms are allowed. The planar outer-labelled source
is a subclass; the RAW NONPLANAR theorem imposes no embedding requirement.

Every edge has strictly positive calendar duration and one strictly positive
finite pair rate, constant over that entire physical edge. Tips are at age zero.
The positive-rate unbounded ancestral population is retained. Each hybrid's
inheritance is strictly between zero and one. Choose ONE declared mechanism:

- COMMON: one natural bit per hybrid per locus, shared by all current roots
  arriving there; different private hybrids and fresh loci use independent bits.
- INDEPENDENT: each current root chooses a parent independently at its hybrid;
  choices at different private occurrences and fresh loci have the original
  source independence.

No comparison below changes that mechanism. An unknown-mode image can later be
a union of separately constructed mode-specific images; it is not a new mixed
mechanism inside one source.

A finite profile has finitely many original experiment rows, a finite maximum
total copy count M, and the union of J finite rational calendar cuts. Within a
row, all records from one locus are deterministic coordinates of ONE complete
rooted genealogy with its merger-bin labels. Relative ordering of unrelated
mergers within one bin is not observed. Rows have one shared graph and parameter
bank; they are not fitted separately. The profile distance is maximum row TV.
This is not a claimed joint distribution of incompatible same-locus
counterfactual interventions.

For natural rows and rational 0 < epsilon < 1, the adapter constructs one
admitted S' with the same target Z=(Q,Splits), the same species, and

    max_row TV(Law_S(row), Law_S'(row)) ≤ epsilon,

with at most

    r0 + E0[2J + (2J+1) B_mode(M, epsilon/(E0(2J+1)))]

hybrids, where r0=2n−2 and E0=8n−8. The original S can have arbitrarily many
hybrids. Endpoint ages, rates and IDs of retained physical primitives are
unchanged. Every new edge has an explicitly assigned positive finite constant
rate. The target is computed by actual graph switchings, not by a stochastic
matrix or circular-order decoder.

For a finite marked-control menu, use the additional unchanged-run condition in
§8 and its separate count. No unrestricted control statement is inferred.

## 3. Concrete structural input: two ports are not a free kernel

Use the accepted bridge quotient of the ACTUAL graph. Its root component and
all branching components are retained. A nonroot two-port nontrivial component
has exactly one ordinary entry and one hybrid, joined by two parallel arms.
This classification follows from root reachability, the child-cut condition,
and binary degree counting; no other internal taxon/population port exists.

Thus each suppressed slot is a finite explicit list of bigons and ordinary
connectors, with its actual parameter list. Retaining the root and branching
components leaves at most r0 hybrids and E0 slots. These counts bound a decorated
core, not the original network's physical size. Core hybrid bits and every
retained original primitive remain in S'.

On each slot, mark a bigon when its closed age interval meets a cut. A cut
strictly inside a connector marks both adjacent bigons when present. Retain that
whole original connector with its single original rate. A cut at a core endpoint
already has a retained endpoint. At most 2J bigons per slot are marked.

The maximal unmarked runs have genuine retained vertices as endpoints. Their
open endpoint intervals contain no cut: a cut in an arm, internal endpoint, or
included connector would have marked an incident unmarked bigon. Components
with no unmarked bigon need not be altered. There are at most E0(2J+1) nonempty
unmarked runs. Distinct runs have disjoint private interiors.

This is the inherited guard construction, instantiated on S. It is not a
subdivision of a cut-crossing physical population into independent-rate epochs.

## 4. Output of the local chain construction, separately by mode

Fix a run R, with endpoint ages t_v < t_u and gap Delta=t_u−t_v>0, in one
bin b. Its ACTUAL connector durations, arm durations, and inheritance values
give a finite positive chain description. Apply the inherited construction at
eta=epsilon/[E0(2J+1)], with full-copy cap M.

The resulting description is a finite sequence of positive connector hazards,
positive arm-pair hazards, and strict inheritance values. It specifies a graph,
not a matrix awaiting an unspecified realization theorem. The chain estimate
holds for every labelled entering forest with at most M current roots.

### 4.1 INDEPENDENT: preserve the order of the strong cells

For an actual bigon with arm survivals x,y and routing g, its specified-pair loss
is q=g²(1−x)+(1−g)²(1−y). It is strictly between zero and one. The inherited
full-forest estimate compares it with the ordinary positive edge of survival
1−q at TV cost at most D_M q^(3/2). That estimate is about complete merger
forests, including their binary shapes; it is not merely a pair-moment match.

Use the inherited shortest small-survival clipping prefix. Replace each weak
bigon by its ordinary pair-matched edge. Keep EVERY retained strong bigon in
its original serial order, with its actual arm survivals and routing value.
Merge only consecutive ordinary pieces by adding their positive coalescent
hazards. Do not commute an ordinary piece through a retained strong INDEPENDENT
cell or reorder the strong cells. The inherited connector repair, if needed,
adds an explicitly budgeted positive hazard; it does not insert a zero-rate
physical edge.

This produces positive connectors interleaved with at most B_ind strong
bigons. If none survive, the result is one ordinary positive edge. The
clipping/weak-replacement/connector budget bounds the resulting FULL FOREST
kernel uniformly by eta. Its local coins remain independent per CURRENT root;
old leaves within one previously coalesced subtree do not receive new separate
routing draws.

For specificity the accepted conservative bound is

    C = binom(M,2),
    W = 1 + ceil(log2(6C/eta)),
    A_M = max(1, (3/2)binom(M,3) + 27binom(M,4)),
    D_M = 2 C A_M,
    delta_ind = min(1/2, [eta/(3 D_M W)]²),
    B_ind = ceil(W/delta_ind).

Here M≥n≥4. No M=0 division is introduced. A more general isolated run with zero
or one incoming root has no mergers and is automatically included in the same
uniform cap-M bound.

### 4.2 COMMON: realize the aggregate, never an identity arm

Use the inherited baseline/strong-factor/weak-generator construction. COMMON
chain operators are functions of the SAME full-forest Kingman generator, so
the permitted commutations in this step are specific to this mechanism.
Clipping, Poissonization, finite positive generator compression, near-one drift
replacement and finite Bernoulli reconstruction yield

    K_X product_i [(1−p_i) I + p_i K_(z_i)],
    0<X<1, 0<p_i,z_i<1,

within the inherited eta budget. The finite product has L≤B_com factors. Its
bare identity arms are not admitted physical source edges.

For L>0 set

    a = 1−(1−X)/(4L+1),       X_res=X/a^(2L).

Bernoulli's inequality gives a^(2L)>X, hence 0<a,X_res<1. Construct one leading
connector of survival X_res; factor i has arms a and a z_i, its strict COMMON
coin p_i, and a following connector of survival a. Its exact aggregate kernel is

    K_(X_res) product_i [K_a ((1−p_i)I+p_iK_(z_i)) K_a]
      = K_X product_i [(1−p_i)I+p_iK_(z_i)].

Every physical hazard is positive and finite. For L=0 use the one ordinary edge
K_X. No positive baseline, drift, or killing term is silently deleted; the
required strict baseline is furnished by the original positive chain and its
accepted construction, not assumed for an arbitrary closure operator.

One inherited conservative bound, sufficient here, is

    d=M−1,
    delta_com=min(1/2, eta/(6 C² W)),
    h=min(1/2, eta/(3 R_M W)),       U0=W/h,
    B_com=ceil(W/delta_com)+3d+ceil(U0)+ceil(6d U0²/eta).

R_M is the explicit rational pure-death coefficient bound from Appendix A.2.
The newer second-order COMMON reconstruction can replace its Euler substep
after retaining all other budgets; no such improved count is needed or newly
claimed here.

## 5. Graph and physical witness: a finite recipe

Let the selected positive chain description have L bigons, connector hazards
c_0,...,c_L>0, arm hazards a_i^0,a_i^1>0, and inheritance p_i∈(0,1).
Number intervals from the younger retained endpoint v toward the older u, and
put d=Delta/(2L+1).

For i=1,...,L create a fresh hybrid h_i at age t_v+(2i−1)d and a fresh ordinary
splitter s_i at age t_v+2i d. In forward graph orientation add:

- two parallel arms s_i→h_i, rates a_i^0/d and a_i^1/d;
- the youngest connector h_1→v, rate c_0/d;
- middle connectors h_(i+1)→s_i, rate c_i/d, for 1≤i<L;
- the oldest connector u→s_L, rate c_L/d.

Attach the inherited strict p_i to h_i, respecting the arm labels. For L=0
add the single edge u→v at rate c_0/Delta. Remove only the old unmarked private
interior and its original incident slot pieces. Retained endpoints and all
retained original edges are outside this operation.

All inserted ages are strictly between t_v and t_u. Every edge's duration is d
when L>0, so its pair hazard is exactly the prescribed c_i or a_i^j. Parallel
arms have the same endpoint ages and may have different constant rates, as the
original model permits. There is no degree-two demographic vertex. Each new
hybrid is (2,1), each new splitter (1,2), and the original endpoint degree is
unchanged because one incident slot connection is replaced by one.

The directed age decrease proves acyclicity. Reachability is preserved through
the same slot endpoints. Every new hybrid child connector is an underlying
bridge: the slot has no third exterior port, and its only internal cycles are
the parallel arm pairs. Existing child-bridge cuts remain cuts after replacing
one connected two-port interior. There are no new tips or tip labels.

For the root-LSA condition, contraction of any inserted chain to its slot gives
the same root-to-species reachability alternatives at every retained vertex.
A new internal vertex lies over a proper descendant bridge subtree. That
subtree cannot contain all species, since the original bridge's downstream
endpoint would then have been a stable ancestor below the original LSA root.
Thus no new vertex is a stable ancestor of all species. The old root remains
the lowest stable ancestor. In the planar subclass, use parallel arms in the
old slot's local corridor; its outer-labelled embedding is preserved. No
embedding is required for the RAW NONPLANAR class.

The construction is a finite real-parameter witness recipe. It does not claim
an executable algebraic encoding of arbitrary input rates or decide an exact
real comparison. Rational-bank effectivity is owned by the Cloud task.

## 6. Why this exact graph implements the full decorated-forest interface

At age t_v, regard each incoming CURRENT root as a distinct token carrying its
entire previously formed rooted subtree, old merger ages/bin tags, descendant
copy labels, and any carried original outside register/history. There are at
most M tokens because routing never splits one genealogy root into two roots.
No population can enter the private run through another port.

Apply the actual local source dynamics to these tokens. COMMON uses one bit
for the whole token forest at each h_i; INDEPENDENT uses one parent choice per
token, not per old leaf. A coalescent merger joins the two current subtrees
under a new binary parent. Subtree payloads and old tags are untouched. Pair
rates depend on the current physical population, not on the internal shape of
the old payload. Thus substituting arbitrary valid old subtrees is a
deterministic graft map on the same token-level merger forest.

All new events occur strictly inside (t_v,t_u), hence have the same bin b.
Applying the graft map and tagging every NEW merger by b converts the local
ordinary full-forest kernel into the actual binned kernel of the constructed
graph. It retains repeated-bin topology and old subtree chronology. It does
not replace the full binary tree by a pair-age matrix and does not erase old
subtrees. Exact within-run merger times have been changed by retiming, so they
are deliberately not asserted equal in law.

Here the carried history is a GENUINE ENTERING PAST. It does not include an
arbitrarily conditioned downstream event or a revelation of this private run's
unused natural coins. In a once-drawn register representation, the private
hybrid coordinates used only inside this run may be deferred until entry:
distinct natural private hybrid coordinates are independent, and the acyclic
two-port geometry prevents an earlier visit revealing one of them. Retained
protected register coordinates remain retained. If an external recorded
variable reveals or correlates with the private bits in a way excluded by this
source independence, the run is not eligible for this theorem.

Consequently, for every physically admissible input forest x and every fixed
causally carried entering past/register z, the original and replacement binned
boundary kernels have TV distance at most eta. The local rates and p_i were
chosen once from the source run and cap, independently of x,z or experiment
row. This is the requisite source-derived conditional estimate. It is not a
desired joint-law equality supplied as an input field.

## 7. One source for every row; error without exterior independence

Perform the preceding surgery once on every guarded run, using disjoint fresh
internal IDs. Their finite union is a SINGLE graph S' with a SINGLE physical
rate, age and inheritance assignment. The new primitive variables are not
reselected when the experiment row, entering forest, or outside register is
chosen. The ancestral population, retained original registers, and all
retained source primitives retain their original joint interpretation.

Expose original source randomness in an ancestral order compatible with the
finite graph and interval decomposition, deferring unused private bits. Condition
on the causally revealed entering past, current outside state and old forest
when a private run is reached; do not condition on later observations of its
internal randomness. Independently pre-drawn retained outside coordinates may
be carried without revealing these private bits. Each run's
conditional kernel is precisely the §6 kernel; correlations created earlier
are carried in that state. A current root visits a run at most once by
acyclicity, and all its entering roots are present at the younger endpoint.

Couple the two source computations identically until the first differing run
output. Conditional on equality so far, couple that run's finite decorated
output with failure probability at most eta. Continue through all retained
kernels and the final original readout. If no local mismatch occurs, all
observed genealogy records of that locus agree jointly. The union bound gives
TV at most the number of replaced runs times eta, hence at most epsilon.

Equivalently, a telescoping kernel argument with full carried state gives the
same result. Neither proof asserts independence between simultaneous exterior
populations or between requested records of the same locus. Unrelated
within-bin event ordering is not part of the observation; changing an internal
age relative to an unrelated demographic vertex creates no extra port or
observable rank. The actual calendar/history adapters remain a separate formal
implementation obligation, and this paragraph does not supply their Lean
acceptance.

The same graph and estimate work for every row/allocation with at most M copies.
Taking maximum row TV introduces no factor equal to the number of rows. If a
later protocol samples H fresh loci, the usual transcript comparison can cost
H epsilon; it is not a claim that an H-locus product law has error epsilon.

## 8. Switching target and the finite marked-control extension

In any switching of an old or new bigon, exactly one arm is retained. Suppressing
the resulting unary private vertices yields the same endpoint connection.
Contract every modified run. Both the original and replacement switching sets
then have exactly the switchings of the SAME retained core; every core
switching extends through every nonempty choice of local arms. Hence their
displayed trees, quartet support Q, and split union agree. Switching
multiplicities and genealogy laws are not conflated with this target equality.

For the marked-control extension, retain every primitive modified by any row
with its original ID and physical meaning. Require the original unchanged-run
condition: no row changes a replaced run's law or the endpoint-age/physical-rate
interface needed by the surgery. If a proposed control moves those endpoints
or acts on new private IDs, ID preservation alone is insufficient; that
experiment needs its own covariance/admission proof and is outside this adapter.
An effective algebraic control formula alone is not such a proof. This is an
explicit reading of the inherited unchanged-private-run restriction, not an
assertion covering arbitrary finite interventions.

With at most K_h marked chain hybrids and K_e marked population primitives,
retain at most K=K_h+2K_e additional bigons: one for a marked hybrid or arm,
and both neighbours of a marked connector when present. Marked core/ancestral
primitives are already retained. Count the UNION of marks across rows, not a
different marked core for each row. Protect the same union of J time cuts.

There are at most T=E0(2J+1)+K unmarked runs and at most 2J E0+K retained
chain bigons. With per-run tolerance epsilon/T, the identical construction has

    R_control = r0 + 2J E0 + K + T B_mode(M,epsilon/T).

All row transformations on retained primitives still use the SAME original
shared parameter assignment. Because each private run is genuinely unchanged
across rows, §6–7 applies uniformly. Neither the natural bound without K nor
an unspecified unbounded registry justifies this control claim.

## 9. Precisely what this adapter discharges and what remains

The finite witness has an admitted graph, positive constant physical rates,
strict inheritance, retained source IDs/ages, the SAME switching target, and
one bank-wide joint-law approximation. The approximation is source-derived
in both mechanisms. Its hybrid count gives the inherited finite candidate
graph envelope: for each representative count r, the binary identities give
V=2n+2r−1 and E=2n+3r−2. This is the input to a finite source census, not an
arbitrary matrix catalogue.

Still separate: formalizing the actual cut/history composition, implementing
the graph constructor/census, rational source density and coupled feasibility,
auditing complete compiler output, and assembling the connected G6 endpoint.
No exact finite-source extraction for an arbitrary closure point, no G3
terminating recognition, no full-calendar TV normalization, no same-locus
counterfactual control coupling, and no uniform bound independent of M,J,epsilon
are proved. All inherited acceptance belongs to its cited exact source;
this adapter itself awaits independent review.
