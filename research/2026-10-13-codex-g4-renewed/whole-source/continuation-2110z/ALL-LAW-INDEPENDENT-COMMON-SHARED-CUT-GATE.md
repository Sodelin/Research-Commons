# Entire INDEPENDENT to entire COMMON: first-cut recovery and the fair-port gate

Contributor: Codex whole-source lane, 14 October 2026.
**Hand-derived source lemmas and a precise unresolved all-law handoff;
independent review requested.** No full general INDEPENDENT-to-COMMON
theorem or finite INDEPENDENT certificate is claimed. The completed
single-taxon normal form, projectivity, ordinary-tree reconstruction and
source compiler are inherited. This note concerns exact ENTIRE laws,
not approximate prefixes or a bounded numerical screen.

## 1. What the existing commonization theorem does not say

The accepted anchor commonizer assumes no hybrid ancestral to both chosen
taxa A,B. It determines the COMMON n-A/one-B law from its entire INDEPENDENT
counterpart. It does not reconstruct the entire COMMON law on arbitrary
allocations of all original taxa across changing original cores.

There is a concrete strict-source reason not to drop its premise. Take
four taxa, with an outside ordinary cherry {C,D}, and a parallel-arm bigon
h above the ordinary cherry {A,B}. Its child bridge has exposure z=log 2;
the A pendant has exposure a=log 2. Give every other edge and both h arms
strictly positive finite exposures, and choose any interior h coin. This
is a binary rooted-LSA outer-labelled cut-child source; h's proper child
cut has descendant set {A,B}.

The single-A normal form recovers the initial ordinary gap a+z=log 4.
But the actual INDEPENDENT AA-cherry probability on two A copies and one
B copy is

    F(AA|B)=1-(2/3)exp(-a)=2/3.                      (1.1)

Once the three unmerged roots meet below h, their subsequent completed
rooted triple is exchangeable, even though it passes through h. The
initial A pendant gives (1.1). If one wrongly treats a+z as an A-private
joint prefix, its completed triangular inverse would require

    U(AA|B)=exp(a+z) F(AA|B)-[exp(a+z)-1]=-1/3.      (1.2)

This is a negative completed probability, not an admitted continuation.
The shared population below h acts on A AND B roots. The A-only normal
form does not authorize moving that joint ordinary interval into an
A-exclusive factor. Equation (1.2) is a counterexample to that proposed
proof step, not a pair of full-INDEPENDENT-equivalent sources with
different COMMON laws.

## 2. A full-INDEPENDENT observer for the first hybrid's descendant cut

Fix a finite strict original source and a taxon A with at least one
ancestral hybrid. Let h be its first hybrid in the backward direction.
The completed single-A normal form determines the preceding ordinary
exposure a_A>0. There is no A-ancestral hybrid on this ordinary path.
Let D_h be the proper taxon descendant set of h's child bridge.

For B different from A, let p_n(A;B) be the probability of the prescribed
labelled B-spine caterpillar on n A copies and one B copy: merge B with
a_1, then attach a_2, then a_3, and so on. This is a legal completed
topology marginal after padding and pruning. It has no nontrivial
A-only clade. Put lambda_n=binom(n,2).

**First-cut lemma.** The entire INDEPENDENT law determines D_h by

 D_h={A} union {B: for SOME finite n,
                  p_n(A;B)>exp(-lambda_n a_A)}.       (2.1)

Proof when B is outside D_h. The child bridge separates B from the entire
ordinary A path of exposure a_A. A merger among the n A roots there
creates an irreversible forbidden A-only clade. Therefore all n roots
must survive this private interval, and

    p_n(A;B)<=exp(-lambda_n a_A) for every n.         (2.2)

Proof when B belongs to D_h. Choose one positive-probability B routing
path reaching the A path below h. There are no A hybrids before h, so
every B routing site before contact is B-only and carries one root. Its
fixed routing weight w>0 is independent of n. Let b be the A-exclusive
exposure to their first meeting on this route. The subsequent common
ordinary interval before h has exposure z=a_A-b>0: it contains the
strictly positive h child edge. No hybrid can lie on this shared interval,
since it would be an A hybrid before h.

Require no A merger on b, then the prescribed B-spine sequence to finish
completely within z. The probability of the prescribed n pair choices
among n+1 roots is

    kappa_(n+1)=product_(k=2)^(n+1) 1/binom(k,2)
                =2^n/[(n+1)! n!].

Pair choices and Kingman holding times are independent. If S_(n+1) is
the total Kingman time from n+1 roots to one, then

 p_n(A;B)>=w exp(-lambda_n b) kappa_(n+1)
                                      Pr(S_(n+1)<=z).             (2.3)

Couple S_(n+1) increasingly to S_infinity=sum_(k>=2) Exp(lambda_k).
Its expectation is finite. Moreover Pr(S_infinity<=z)>0 for every z>0:
choose a tail with expectation less than z/4 and use Markov's inequality
to give it probability at least 1/2 of being at most z/2; independently,
the finitely many remaining positive exponential variables have positive
probability of total at most z/2. Hence (2.3) is bounded below by the same
positive constant times exp(-lambda_n b) kappa_(n+1), uniformly in n.

After multiplication by exp(lambda_n a_A), the logarithm of this lower
bound is lambda_n z-O(n log n), which tends to positive infinity. Thus
(2.2) fails for some finite n, proving (2.1). Once the whole selected
genealogy has formed below h, no older source operation can change its
internal topology. No unknown upper-law assumption enters (2.3). QED.

This is an all-law determination with a finite positive witness for
membership. No uniform witness arity or finite certificate of NONmembership
is asserted. The length a_A itself is supplied by the entire single-A law;
it is not assumed to be a separately observed coalescence time.

## 3. Identify a youngest hybrid and its entire lower ordinary tree

Apply (2.1) to every taxon with a nonempty hybrid ancestry, obtaining its
first-hybrid cut D_A. Their inclusion-minimal distinct sets correspond
to youngest original hybrids. In fact if any hybrid lay below such h,
choose a taxon below it. Its first-hybrid cut would be a proper subset
of D_h, contrary to minimality; if its descendant set were the same D_h,
then h would not be first for ANY taxon in D_h. The child-cut hierarchy
also prevents two incomparable hybrids from having the same descendant
set. Thus one minimal set D identifies one youngest hybrid h, and there
is no hybrid in the entire ordinary subtree below it.

For A,B in D, the legal specified INDEPENDENT crossed-cherry probability
u_(A|B) satisfies

    l_AB=-log(3u_(A|B)),                              (3.1)

where l_AB is the ordinary exposure from A to its first meeting with B
in that lower tree. Above their meeting, the three selected roots have
an exchangeable completed continuation, so the usual 1/3 formula holds
without a COMMON observation or knowledge of the upper reticulate source.

These pair depths and the ordinary rooted triples determine the ordinary
rooted tree on D and its edge exposures below its least common ancestor.
This is the inherited strict ordinary-tree identification: positive
internal edges identify rooted triple relationships; directed path sums
then recover the edge lengths. For two taxa, (3.1) directly gives both
pendant lengths; for one taxon there is no branching to recover.
For any A in D, subtract its recovered path to that least common ancestor
from a_A to obtain the common positive stem ending at h. The value is the
same for all A because this is the actual youngest-hybrid subtree.

Consequently the complete ordinary lower forest operator K_D is determined
from the entire INDEPENDENT law, along with h's coin orbit and its two full
arm exposures from any single-A normal form. These are proof functionals,
not hidden forest observations or hypothetical independent fitted sources.

## 4. What a youngest biased hybrid permits

Let E be the original taxa outside D. Retain arbitrary finite copies of
them, and use only one representative A in D as the inside taxon, with
arbitrarily many copies. The known path a_A is private relative to ALL
outside-D taxa. Its completed joint triangular inverse is therefore valid,
unlike (1.2). It recovers the actual h-first joint INDEPENDENT law.

Use the inherited first-cohort extractor on the A-only restriction while
retaining those finitely many outside copies. Each recovered cohort equals
the original first Bernoulli routing cohort almost surely. Selecting finitely
many labels in it depends only on that routing partition, not on later
genealogy or outside histories. Strict original incoming edges provide
positive initial exclusive arms; in fact selected-label projectivity is
the operative unbiasedness statement. This is the same finite-decoration
argument as the anchor commonizer, now with an arbitrary fixed finite
outside panel.

If g is not 1/2, cohort masses orient the two groups. Thus the entire joint
laws H_0(k,E) and H_1(k,E), with all k inside roots routed to the respective
parent, are separately determined, up to simultaneous passive arm swap.
They retain every early outside interaction and all later natural sites;
no inversion of the possibly mixed arms is used.

Now restore an arbitrary allocation to all original taxa in D. Sum over
the known lower ordinary forest f with probability K_D(f), let k be its
number of current roots, and graft its opaque component trees into the k
inside tokens of H_i(k,E). This gives the FULL original completed law with
h deterministically resolved to parent i and every other hybrid still
INDEPENDENT. The same construction works in two full-INDEPENDENT-equivalent
sources: their cut D, lower tree and coin orbit agree, and so do these
resolved laws after the corresponding passive swap.

Resolving one hybrid in the proof preserves every unmarked hybrid and
the original admission after pruning/suppression, by the inherited
controlled-resolution source lemma. This does not add a physical actuator
to the menu. All surviving edge lengths are positive sums; any newly
redundant stem above the LSA is ordinary and harmless under completion.

It follows by induction that full INDEPENDENT equality implies full COMMON
equality when all hybrids have biased coins. A full-INDEPENDENT-equivalent
rival also has only biased coins, because every one is visible on some
single-taxon ancestry and those coin orbits agree. Resolve a shared
youngest cut in both sources; apply induction to the two separately
recovered conditional laws; finally mix their COMMON resolutions with
the original g and 1-g. The fixed taxon set remains intact. This is an
unbounded-size all-law consequence, not finite-prefix forcing.

At a fair hybrid that is genuinely private relative to all outside taxa
until its arm join, the same resolution step is also available. The
extracted fair average is [(E_x+E_y)/2]U for one joint upper continuation
U. The positive-diagonal ordinary mixture is invertible capwise; after
recovering U, both E_x U and E_y U are separately known. This reuses the
inherited private fair-cell inverse. The unresolved case below concerns
mixed parent arms, not fair private bigons.

## 5. The precise unresolved fair mixed-port implication

At a fair youngest hybrid with outside interactions on its parent arms,
the measurable cohort extractor has an independent fair orientation.
It supplies, for every allocation to both extracted cohorts and the
outside panel, the PORT-SYMMETRIZED joint law

    (1/2)[H_(k,l,E)+SwapPorts(H)_(k,l,E)].            (5.1)

In particular it supplies (H_0(k,E)+H_1(k,E))/2. It does not orient the
two actual conditional parent laws separately. Choosing an orientation
from a realized outside genealogy would generally condition on later
events and bias the recovered conditional law. The private formula
[(E_x+E_y)/2]U is unavailable when outside lineages meet one arm early.

For the immediate site h, the fair COMMON mixture is exactly the available
average; there is no ambiguity in commonizing h ALONE while leaving all
older sites INDEPENDENT. But the recursive operation needed above changes
the older sites too. It has not been proved to be a linear operation on
arbitrary mixtures of conditional resolved-source laws. Therefore one
cannot apply it to (5.1) componentwise without proving the required
decomposition or an equivariant quotient theorem.

One sufficient missing theorem is:

  For every finite strict source-derived two-port continuation obtained
  by opening a youngest fair hybrid, its entire port-symmetrized
  INDEPENDENT completed response determines the port-symmetrized COMMON
  completed response of that SAME continuation, with all remaining
  original sites and outside panels retained.

This must include arbitrary changing original upper cores and repeated
equal parameters. A generic identifiability theorem, a single-A orbit,
a known exterior inverse or a latent independently queried parent law
does not supply it. An alternative is an all-strict ordinary/multiport
source reconstruction from (5.1) sufficient for the desired commonization;
none of the inspected providers establishes that conclusion.

The fair symmetry loss has NOT been shown to cause actual nonidentifiability.
No two strict finite sources with equal entire INDEPENDENT laws and
different COMMON laws are supplied here. It is the exact gap in the
bottom-up all-law argument. The full-INDEPENDENT fibre count bound alone
does not fill it.

## 6. A separate finite algebraic formulation of the all-law question

For a fixed strict target T, the
[all-law fibre count bound](INDEPENDENT-ALL-LAW-FIBRE-BOUND.md) already places
every finite strict source with its entire INDEPENDENT law in the finite
shape class h<=sum_A L_A(T). On each of these finitely many shapes the
source compiler and Hilbert finite generation give finitely many original
INDEPENDENT equalities whose zero set is exactly the full target
INDEPENDENT fibre within that shape.

The general all-law I-to-C question is whether every COMMON response
difference vanishes on each such STRICT physical fibre. This is a real
zero-set implication, not an automatic ideal inclusion. Bounded-shape
COMMON finite determination also reduces the desired differences to a
finite original list. For an untied coalescent-survival/coin chart with
specified exact constants, this gives a finite real-algebraic feasibility
formulation of a possible counterexample. Additional original parameter
ties must be retained; arbitrary ties are not declared semialgebraic.

This formulation neither proves the implication uniformly for all targets
nor permits its bound to be imposed on finite-prefix rivals. Even a
complete all-law I-to-C theorem would still leave the finite missing-mode
bridge open, because of the reviewed
[COMMON-transfer discontinuity](INDEPENDENT-COMMON-TRANSFER-DISCONTINUITY.md).

## Evidence and next action

New hand steps: the comb first-cut test (2.1), its youngest-cut consequence,
and the stated bottom-up resolved-source reduction. Inherited inputs are
the completed single-taxon normal form, cohort/projectivity interface,
ordinary rooted-tree recovery, actual finite source compiler and
[resolution source lemma](../FULLY-ACTUATED-TARGET-TRANSFER.md). The
[anchor commonizer](ANCHOR-COMMONIZATION-AND-TWO-CLOCK-RIGIDITY.md) retains
its narrower accepted scope.

Independent review should first challenge (2.3), minimal-cut ordinary
recovery and the biased resolved-source recursion. The next general
mathematical duty is the fair mixed-port implication in Section 5, or a
strict exact counterexample to full I-to-C determination. No finite
screen, approximation, boundary source, formal verification or historical
novelty claim is substituted for that obligation.
