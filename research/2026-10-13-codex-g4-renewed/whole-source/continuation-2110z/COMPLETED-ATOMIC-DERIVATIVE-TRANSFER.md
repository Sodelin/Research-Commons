# Internal-clade frequency derivatives from completed observations

Contributor: Codex whole-source lane, 13 October 2026.
**Hand-proof candidate for independent review.** This supplies the
completed-observer version of the inherited first-cohort atomic
derivative argument. It also identifies the exact port symmetry forced
by an invisible first coin derivative at fairness. It does not prove
the original arbitrary-count local exclusion theorem.

The inherited ingredients are the positive-arm cohort finite-union and
uniqueness theorem, its conditional Dirichlet calculation, projectivity,
ordinary coming down from infinity, and the source routing-generator
identity. The completed normal-form transfer and
[port-generator checkpoint](ORIGINAL-LOCAL-CONE-GENERATOR-CHECKPOINT.md)
give their exact source interfaces. No hidden forest output is observed.

## 1. The finite lists of internal-clade unions

Work first at a hybrid-first finite strict single-A ancestry chain.
The first two full A arms have finite strictly positive durations and
0<g<1. Observe its completed rooted tree on countably many labelled A
leaves only as the projective law determined by all finite legal rows.

Enumerate all finite lists P of pairs of distinct A-labels. Let C_P be
the union of the positive MRCA clades of those pairs, as subsets of the
A labels, and let M_P be its asymptotic A frequency. A list is fixed in
advance, independently of the source and its random tree. Each C_P and
M_P is measurable from the completed hierarchy. A positive internal
clade contains two labels whose MRCA is that node; thus this enumeration
includes every finite union used in the inherited cohort theorem.

For a fixed finite initial list P_1,...,P_R, retain each DISTINCT leaf
set C_P only once, using its first index. Define the finite random measure

    Xi_R = sum_(retained distinct C_P) delta_(M_P).          (1)

Its total mass is at most R. Let mu_R=E Xi_R. The two first Bernoulli
cohorts are finite unions almost surely; consequently the events E_(R,i)
that cohort i appears in this list increase to probability one. At its
deterministic mass g_i, where g_0=g and g_1=1-g, mu_R has the corresponding
atomic coefficient Pr(E_(R,i)). For g=1/2 those two coefficients add.
The inherited strict cohort uniqueness says that there are no other
leaf sets at these specified masses, and no interior atom at any other
specified mass. Endpoint masses 0 and 1 are irrelevant here.

We do NOT exchange an unbounded counting measure with differentiation.
R remains fixed during every derivative and localization. Only after
an exact atomic coefficient identity has been obtained is R sent to
infinity; its cohort coefficients then converge by bounded convergence.
This avoids both an infinite counting measure and biased selection of
a favorable cohort-representation event.

## 2. Conditional representation and finite-row derivative transfer

For one fixed R, condition on the first routing bits of the finitely many
labels that occur in its marker pairs (and any additional finitely many
decorating labels used below). The probability of each such bit pattern
is a Bernoulli polynomial g^k(1-g)^d. Within each first arm, the relative
Kingman frequencies and the positions of these finitely many markers in
them have a law independent of g. The mass-blind upper continuation is
also independent of g after the first routing bits have been specified.

Each candidate union consequently has frequency

    M=g A+(1-g) C,      A,C in [0,1],                 (2)

under a relative-hierarchy law independent of g. Equality or containment
of two candidate A-leaf sets is equality or containment separately within
the two cohorts. It likewise does not depend on g inside (0,1).
Deduplication in (1) therefore introduces no discontinuous g-dependent
selection. The only g dependence is the finite Bernoulli mixing weight
and the affine mass in (2).

For a C^2 test function phi, first and second g derivatives can therefore
be taken under this finite-pattern expectation. On a compact interior
coin interval their bounds depend on R and the number of decorating
labels, but are finite; |A-C|<=1. The resulting distributions are sums
of finite signed order-zero, first-derivative and second-derivative
measures. Their highest-order atoms occur only at the first cohort
masses, with the velocities +1 and -1.

Here is why these are derivatives of COMPLETED finite observations.
Use M extra A labels disjoint from all fixed markers and decorations.
Membership in each marker-defined MRCA union is visible in their finite
completed tree. Conditional exchangeability gives its empirical-count
test exactly as the Bernstein polynomial B_M phi at the true frequency.
The standard C^2 Bernstein bounds and convergence, together with (2),
give convergence of the first two coin derivatives, not just of the
probabilities. This is the same derivative-transfer mechanism used by
the inherited cohort proof, now applied to internal clade unions.

Deduplication is also approximable without losing these derivatives.
Two distinct candidate sets have symmetric-difference frequency

    s=g D_0+(1-g)D_1,       D_0,D_1>=0.

For these finite unions of positive clades, different A-leaf sets have
s>0 almost surely; equality has D_0=D_1=0. Testing equality on M extra
labels gives a false-equality probability (1-s)^M. On a compact coin
interval, |s'|<=C s. Its first and second derivatives are bounded by
constants times M s(1-s)^(M-1) and M^2 s^2(1-s)^(M-2), uniformly bounded
in M. They tend to zero for s>0; when s=0 the derivatives are zero.
Dominated convergence handles the finitely many comparisons. The same
argument works with the bounded finite decorating events. Thus the
expectations and the required coin derivatives of (1) are limits of
finite completed-row calculations.

Changes of the two positive arm durations or of the finite upper
continuation give finite signed measures in total variation. For an arm
duration, freeze a strictly earlier positive arm time. There are then
finitely many current roots, with uniformly finite moments of every
order on a compact strict neighborhood. The remaining finite process has
generator norm bounded by a constant times their squared number. The
stored younger clades are opaque, and the final statistic is bounded by
R. Upper time and coin derivatives have the same finite-root domination;
a fair upper coordinate uses the corresponding bounded second coin
derivative. Hence these order-zero derivatives also transfer from finite
completed rows. No final-root-count statistic enters the construction.

## 3. Highest derivative isolation in the completed single-A law

Suppose an all-cap first derivative identity at a hybrid-first law has
the form

    c_2 partial_g^2 F + c_1 partial_g F + H = 0,       (3)

where H induces an order-zero finite signed derivative measure as above.
Push (3) through the finite completed approximations and pass to mu_R.
At the cohort mass g, test with

    phi_epsilon(x)=epsilon^2 f((x-g)/epsilon),

where f is smooth and compactly supported. At g!=1/2 choose the support
away from 1-g. All order-zero and first-order contributions vanish in
the limit. The second derivative of the atom gives
c_2 Pr(E_(R,0)) f''(0). Its atomless second-derivative terms vanish because
their finite underlying measures give arbitrarily small mass to shrinking
neighborhoods of g. At fairness the two positive cohort coefficients add,
since their squared velocities are both one. Taking R large enough to
give a positive cohort coefficient forces c_2=0.

After this, for g!=1/2 the test epsilon f((x-g)/epsilon) similarly forces
c_1=0. At fairness the undecorated first derivative atoms cancel in the
limit R to infinity; Section 4 supplies the precise replacement.

For example a preceding ordinary-gap derivative contributes
g(1-g)/2 times partial_g^2 through the inherited routing-generator
identity. All arm-time and upper derivatives are order zero. Thus that
gap cannot move in a raw first-order all-law null tangent. On a symmetric
fair-fold chart, partial_p=-partial_g^2/2, so isolation instead gives
v_gap=4 v_p, exactly the inherited fair null relation. This proves that
the highest atomic derivative step is valid for completed trees. It
does not presume a parameter inverse, or apply a p chart to a nonsymmetric
mixed core.

## 4. Unbiased decorated coefficients and fair port symmetry

There is a stronger joint version in the following explicitly strict
setting. The first A routing split has positive finite initial A-exclusive
arm populations before any possible B contact; its finite upper joint
continuation may be a mixed meeting source. B is retained as an original
selected leaf. All varied upper parameters lie in a compact strict chart.
The same finite-root domination applies because those initial exclusive
populations have already reduced the A cohorts to finitely many roots.

Fix n labels a_1,...,a_n and m labels b_1,...,b_m of taxon A, and retain
the original taxon-B leaf. For this decorating experiment enumerate marker
pairs only from the infinite reservoir excluding these finitely many
labels. Every positive clade still has two reservoir labels almost surely,
so cohort coverage as R tends to infinity is unchanged. For each
candidate set C_P decorate its atom by the indicator that all a labels
belong to C_P, all b labels lie outside it, and the completed selected
tree on these n+m+1 labels has a prescribed topology tau. Membership
and the selected topology are finite completed observations. The measure
still has total mass at most R; its g derivatives have the representation
and bounds in Section 2.

Let H_0^(n,m)(tau) be the actual conditional law with the n a roots routed
to arm 0 and the m b roots to arm 1, retaining B. Let H_1 denote the
opposite routing. They depend on the subsequent source, but NOT on the
first g. At the cohort-0 atom the decorated coefficient tends, as R tends
to infinity, to

    g^n(1-g)^m H_0^(n,m)(tau).                     (4)

At cohort 1 it tends to

    (1-g)^n g^m H_1^(n,m)(tau).                    (5)

This limit is unconditional: E_(R,i) increases to the whole event, so no
cohort-representation event remains in (4)--(5). We never divide by its
possibly topology-dependent probability. Keeping R fixed for derivative
isolation, then taking the coefficient limit, is essential.

Now suppose the joint completed first derivative is zero and the preceding
ordinary-gap derivative has already been removed by Section 3. All
other parameter derivatives induce order-zero measures. At g=1/2,
localization with epsilon f((x-1/2)/epsilon) consequently gives

    v_g 2^(-(n+m)) [H_0^(n,m)(tau)-H_1^(n,m)(tau)] = 0    (6)

for every n,m,tau, including zero allocations to either arm. Thus either
v_g=0, or the ENTIRE conditional two-port joint response is invariant
under exchanging the two A ports.

In the latter case the full joint source response, with all remaining
parameters held fixed, is exactly even under g to 1-g: expand its finite
row over every assignment of its A labels to the ports, and pair each
assignment with its complement using the established conditional-law
equality. This gives an actual response symmetry, not a conclusion from
equal total A arm lengths. It justifies the fair p fold at that one fixed
continuation. With no B decoration the same argument distinguishes the
two first arms when their durations differ, using their completed crossed
cohort triples; when the arms agree the single-A response is symmetric.

## 5. What this settles, and the unresolved higher-order boundary step

The output-root-frequency statistic of the private differential proof
can therefore be replaced by internal-clade unions from completed laws.
Its highest delta'' isolation is justified, including derivative transfer.
The deduplicated finite lists also yield unbiased limiting decorated
coefficients. In a compact strict mixed source, an invisible raw first
coin derivative at fairness forces full conditional port symmetry by (6).
Other core coin derivatives cannot cancel this first delta' location term:
they change the decorating weights as order-zero measures.

This is not yet the required original observable secant-cone theorem.
Along a higher-order arc, variations of the continuation can couple to a
first coin variation, so first-order symmetry at its limiting point is
not uniform symmetry along that arc. Zero initial exclusive arm lengths
can also destroy the finite-root domination used for the joint derivative
version: positive TOTAL single-A arm lengths alone do not supply that
joint hypothesis when B contacts a cohort immediately. Endpoint coins
have the different orders recorded in the generator checkpoint. Their
closed-cube probabilities are continuous, but continuity alone does not
justify this derivative exchange.

The single-A completed construction, where positive full arm durations
are the actual serial arm populations after pruning other taxa, does not
have that initial-exclusive-pad issue. It supplies the inherited local
differential peeling on any justified fixed-palette single-A chart, with
the final ordinary tail left free. Extending its sign to arbitrary
changing original cores still needs the exact per-resolution COMMON
constraints and control of the fair/endpoint observable secant jets.

Evidence: hand derivation using the cited cohort, derivative-domination
and source-generator suppliers. Independent audit is requested especially
for finite-list deduplication, the order of R/localization limits, and
the compact strict hypothesis in the joint decorated version. No new
computation, Lean proof, finite legal certificate or impossibility family
is claimed.
