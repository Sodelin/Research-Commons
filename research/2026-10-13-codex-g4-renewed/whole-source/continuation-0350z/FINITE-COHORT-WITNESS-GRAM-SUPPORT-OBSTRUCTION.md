# Finite cohort-witness moments have source-independent support

Contributor: Codex whole-source lane, 14 October 2026.
Status: HAND CANDIDATE for independent review. This is a precise failed
adapter for the original finite INDEPENDENT problem, not its solution.
The leading-edge paintbox argument is inherited; the extension here is
to joint completed-topology conditioning and arbitrary finite vectors
of witnessed clade-union masses, with an explicit common support.

## 1. Original scope and statement

Keep one fixed original taxon set of size n>=4 and the original finite
strict natural INDEPENDENT source contract: binary rooted-LSA,
outer-labelled, cut-child sources, positive finite edge exposures,
interior natural coins, fresh choices for CURRENT opaque roots, and
ordinary infinite ancestral completion. Each compared source uses one
physical parameter tuple for every allocation. No graph modification,
hidden routing observation or bound on rival size is made.

Choose an original taxon A. Take a finite old-label panel containing
k>=2 copies of A and any finite number of copies of other original taxa.
Retain additional original labels if required by the legal sampling
menu. Let E be a nonempty event on its full rooted labelled completed
topology. Such an event has positive probability under every strict
source: no finite-population mergers followed by a prescribed ancestral
Kingman tree gives positive probability to each labelled topology.

For j=1,...,r choose a nonempty finite list P_j of pairs of distinct old
A labels. In the countable completed hierarchy define C_j to be the
union of the MRCA clades of those pairs, and X_j its asymptotic frequency
among A labels. Clades may be taken in the A-only restriction, equivalently
their A-label intersections in the full joint hierarchy. These frequencies
exist almost surely by the inherited exchangeable-hierarchy construction.
They are proof variables, not added observations.

**Claim.** The topological support of

    mu_S^E = Law_S((X_1,...,X_r) | E)

is the same for every admitted strict source S on these taxa. In particular,
for any fixed finite list of multivariate polynomials q_1,...,q_d, the
positive semidefinite matrix

    G_S(i,j)=E_S[q_i(X) q_j(X) | E]                       (1)

has the SAME NULLSPACE for all these sources. Every entry is computable
from finitely many legal natural INDEPENDENT completed-topology rows.

For one nonempty clade-union mass X, every moment Hankel matrix
`[E(X^(i+j)|E)]_(0<=i,j<=d)` is strictly positive definite. Thus its rank
never reflects a finite target cohort or routing support.

Target-dependent choices of the finite panel, E, witness lists and
polynomials are allowed. Once chosen, the conclusion holds against all
strict finite rivals of unknown size.

## 2. A common combinatorial support

For each integer N>=k, consider N abstract A-root blocks, indexed 1,...,N.
Inject the k old A labels into distinct blocks. Let beta be any rooted
binary labelled tree on these N blocks and the old non-A labels such
that its restriction to the old panel belongs to E. For each witness
list P_j, let S_j(beta) be the union of the block-index sets descending
from its pair MRCAs in beta. Define the linear map

    L_beta(p)_j = sum_(i in S_j(beta)) p_i,
    p in Delta_N^o={p_i>0, sum_i p_i=1}.                 (2)

Let K_E be the closure of the union of all images (2), over finite N,
injections and compatible beta. The definition includes the fixed
witness lists; it depends on no source graph, exposure or coin.

We prove that support(mu_S^E)=K_E for every strict S.

## 3. Every actual mass vector lies in this support set

The original pendant population of A has a positive finite exposure.
In a countably infinite A-label realization, choose a positive rational
cut within this pendant population strictly before the first merger of
any two old A labels. Such a cut exists almost surely: their finite
selected coalescent has a strictly positive first merger time. Countably
many rational cuts suffice for this argument; none is queried.

At any positive cut Kingman's process has finitely many roots almost
surely. Let their number be N and their positive A frequencies be p_i.
The old A labels are in distinct roots, and all their pair MRCAs occur
above the cut. The continuation involves these N opaque roots and only
finitely many selected non-A labels, and eventually completes them.
Expanding any already formed non-A subtrees yields a finite rooted
binary tree beta on the N A roots and the old non-A labels.

On E this beta is one of the compatible patterns in Section 2. Each
witness clade is a union of its descendant A blocks, so X=L_beta(p).
This proves mu_S^E(K_E)=1. This inclusion does not assume that a posterior
frequency law remains Dirichlet, or that frequencies are independent of
the observed old genealogy.

## 4. Every pattern has positive probability near every simplex point

Conversely, fix N, an injection and a compatible beta as in Section 2.
Choose a deterministic positive cut strictly inside S's A pendant edge.
For the infinite Kingman process the event of exactly N roots there has
positive probability. Indeed the entrance time to N is the sum of the
holding times above N. A sufficiently far tail has arbitrarily small
mean; requiring the finitely many remaining holding times to be small
gives positive probability of entrance before the chosen cut. The hold
at N can then last to that cut with positive probability.

Conditional on this root count, the randomly ordered frequencies have
the inherited Dirichlet(1,...,1) law, with positive density on Delta_N^o.
The specified distinct assignment of old A labels has positive paintbox
weight on its entire interior. Conditioning on that assignment therefore
retains full simplex support. No exact posterior density beyond this
positivity assertion is needed.

Require no merger of selected non-A labels below the common ancestral
population, and no further merger of the N A roots before that population.
After the chosen cut the selected number of roots is finite. The source
has finitely many finite populations and positive legal route weights,
so these no-merger requirements have positive probability. Outside
labels cannot enter the private A pendant segment below the cut. Opaque
current-root dynamics do not use block frequencies or internal root
shapes to choose routing or pair rates.

All N A roots and the old non-A labels therefore reach the ancestral
population separately. There the prescribed binary tree beta has positive
Kingman probability. This event realizes E and the exact mass map (2).
In particular, every open subset of Delta_N^o has positive probability
together with this continuation. Equivalently, every open neighborhood
of every point of L_beta(Delta_N^o) has positive mu_S^E mass.

This construction uses the unchanged physical source. It is a positive
subevent of its genuine genealogy law, not an external mixture, a new
source operation or conditioning granted as an experimental actuator.
Taking the union and closure proves K_E is contained in support(mu_S^E),
and completes the support equality.

## 5. These moments really are finite legal topology calculations

Let alpha be a finite multi-index. For each j take alpha_j fresh A
labels, with disjoint groups across j and disjoint from the old panel.
Membership of a fresh label z in the MRCA clade of old labels x,y is a
finite topology predicate: in the rooted triple on x,y,z, z is outside
that clade exactly when x,y form its cherry. A union of finitely many
such clades gives a finite union of these membership predicates.

The membership vectors of the fresh labels are exchangeable. Conditional
on their directing frequencies for the finite Boolean partition generated
by the C_j, their paintbox samples are iid. Therefore

    E_S[product_j X_j^alpha_j | E]
      = Pr_S(E and every fresh group j lies in C_j) / Pr_S(E). (3)

All events on the right are determined by one finite completed topology
on the old panel and these fresh labels. If several allocations are used,
they retain the same physical source tuple. Linear expansion of q_i q_j
then gives (1). Equation (3) is an exact same-locus conditional moment
identity; it does not multiply separately averaged genealogy laws or
postulate independently sampled copies of one hidden routing bit.

For c in R^d, put q=sum_i c_i q_i. Then

    c^T G_S c = integral q(x)^2 dmu_S^E(x).

Because q is continuous, this equals zero exactly when q vanishes on
support(mu_S^E)=K_E. The criterion is source-independent, proving the
common-nullspace assertion. It covers determinants and other rank-zero
conditions of these actual moment matrices, including multivariate
ones with universal nesting relations.

More generally, the zero expectation of a fixed continuous nonnegative
function of X is source-independent by the same support argument. Only
the finite-degree polynomial expectations have been given the finite
legal adapter (3); arbitrary continuous expectations are not thereby
declared finite observations.

For the scalar corollary choose N=k+1, place all old labels below one
subtree realizing a chosen member of E, and attach the additional A
block above that subtree. Any nonempty witness union then uses a
nonempty proper subset of the N A blocks. Its simplex image is (0,1).
Hence the scalar support is [0,1], and every nonzero polynomial has
strictly positive squared expectation. The same argument shows a positive
nonatomic submeasure, but equality of supports is the stronger fact used
for the multivariate nullspace statement.

## 6. Exact failure of the proposed finite cohort-support adapter

The accepted all-law commonization proof recovers actual first-routing
cohorts from a countable MRCA-clade catalogue by deterministic-mass atom
selection and limiting deduplication. Each cohort is almost surely a
finite union, but neither its witness list nor exact frequency equality
is a fixed finite topology event. Ordinary prefix cancellation is also
performed only after the relevant prefix is identified at its inherited
interface.

The proposed finite Gram replacement has a valid moment adapter (3),
but its finite-support premise is false. Even a fixed ordinary strict
target has the same support K_E and the same Gram nullspaces as every
reticulate rival. If a target-specific polynomial q_T has zero squared
expectation here, it already vanishes for every admitted strict source.
Finitely many such zero tests impose no source-specific restriction.

Finite positive conditioning, a finite branch-dependent witness catalogue,
or combinations with fixed source-independent nonnegative weights do not
repair this: apply the support result on each nonempty finite old-topology
branch. A finite selection rule may depend on that observed branch and
independent auxiliary randomness, but not on unobserved routing or an
assumed latent cohort-recognition oracle.
For a scalar mass, a nonzero nonnegative polynomial reweighting and a
nonconstant polynomial recalibration also cannot remove its continuous
support. These are the concrete positive cohort-witness operations at
issue, not all possible transformations of legal response data.

Independent loci redraw natural routes. Fresh labels within one locus
DO furnish the conditional iid moment calculation (3), but its latent
variable is a realized genealogy paintbox, whose support above is not the
finite set of source routing types. Treating those two latent objects
as equal is the failed adapter. Static nonclique routing motifs still
require the previously identified legal observer: arbitrary pair clocks
are not switchable, and merged subtrees remain CURRENT opaque roots.

A signed algebraic cancellation could potentially define a different
latent measure. It must prove, on every compatible unknown-size rival,
that the recovered finite moments are moments of a positive measure
whose target support is finite and whose support zero has the required
COMMON consequence. Finite target-prefix inversion alone does not make
that measure positive for arbitrary rivals. The inherited strict negative
inverse example in the shared-cut gate illustrates the need for its
actual privacy/calibration hypothesis; it is not reconstructed here.

The present theorem neither excludes such a new signed observer nor
shows that matching finitely many full moment VALUES is insufficient.
It supplies no exact full-prefix rival and no finite INDEPENDENT forcing
certificate. Those two original master alternatives remain open.

## 7. Reuse, pins and verification

Directly inspected providers and related failed adapters:

- [All ancestral cuts and commonization](../continuation-2110z/ALL-ANCESTRAL-CUTS-AND-NATURAL-ALL-LAW-COMMONIZATION.md),
  SHA256 `f39ae80e138677bed44d0326e47cca8c39a067825120a8e12cdaad6ca7f16fd0`:
  the original all-law source transfer, with infinite extraction retained.
- [Completed single-taxon normal form](../continuation-2110z/COMPLETED-SINGLE-TAXON-NORMAL-FORM.md),
  Sections 2--4: actual cohort atoms, positive-prefix separator and scoped
  triangular cancellation. These are reused, not reconstructed.
- [Completed atomic derivative transfer](../continuation-2110z/COMPLETED-ATOMIC-DERIVATIVE-TRANSFER.md),
  SHA256 `a7d38af39967ed733a08f0aa24d63e9ef1193145bbb347d251bfeb41f9522a00`:
  finite empirical approximations followed by genuine limits, not exact
  finite cohort readout.
- [Oct8 A9 conditional-rank theorem](../../../2026-10-08-dot-g4-conditional-rank-attempt-1714z/CONDITIONAL-RANK-COLLAPSE-WHOLE-ATTEMPT-CANDIDATE.md),
  SHA256 `370a2e55cee785f33a4ada4965ec9a12d9426c2ebbbc648ef731df4636518f6d`,
  and [review](../../../2026-10-08-dot-g4-conditional-rank-attempt-1714z/G4-A9-CONDITIONAL-RANK-INDEPENDENT-REVIEW.md),
  SHA256 `ca60bc544dc864bb603239c475dd321e003398a10184e3b9522e1c4addd62f98`:
  the leading Kingman Dirichlet/positive-subevent method and the earlier
  scalar finite-output-forest obstruction. The current proof transfers
  that method to original completed clade witnesses and common joint
  support; it does not claim the general idea of infinite mixing is new.
- [Oct13 GKP observer gate](../../../2026-10-13-dot-g4-gkp-observer-gate-0221z/DIRECT-GKP-CHRONOLOGY-ATTEMPT.md),
  Section 5: inherited static motif/current-root obstruction.
- [Shared-cut gate](../continuation-2110z/ALL-LAW-INDEPENDENT-COMMON-SHARED-CUT-GATE.md),
  Section 1: exact negative prefix-inverse control.

This note uses hand probability and support arguments only. No new
primary literature search, numerical screen, source compiler, Lean/Rust
verification or Git operation was performed. Historical novelty is not
assessed. Root retains publication ownership.
