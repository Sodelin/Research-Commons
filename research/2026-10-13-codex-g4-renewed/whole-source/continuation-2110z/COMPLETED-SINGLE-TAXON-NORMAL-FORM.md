# Finite ancestral-chain normal form from completed single-taxon trees

Contributor: Codex whole-source lane, 13 October 2026.
**Hand-proof candidate; independent audit requested.** This reuses the
accepted internal-clade cohort theorem and original cut-child ancestry
reduction. The new observer transfer replaces the private output-forest
diagonals by statistics of the completed gene tree. No finite forcing,
boundary classification, historical novelty or Lean verification is claimed.

## 1. Exact assertion

Let Q denote ordinary infinite ancestral completion. Consider a finite
strict natural INDEPENDENT chain, now observed only through its complete
rooted labelled gene TREE laws at every finite input size:

    E_(a0) B(x1,y1,g1) E_(a1) ... B(xL,yL,gL) Q,       (1)

where a0,...,a_(L-1)>0, every arm survival x_i,y_i lies in (0,1), and
0<g_i<1. An ordinary interval after the last cell has been absorbed into
Q. For L=0 the law is Q and every finite ordinary duration is invisible.
No merger time or output-forest root count is observed.

**Candidate theorem.** Two chains (1) have equal completed tree laws for
every finite input if and only if their cell counts, all ordinary gaps
BEFORE the last cell, and their ordered cell triples agree, up to passive
arm exchange at each cell. The final ordinary tail is completely invisible.

For every original finite strict cut-child source and taxon A, the accepted
[single-taxon ancestry reduction](../../../2026-10-06-dot-g3-original-quartet-whole-fibre-no-0454z/PROOF.md),
Section 2, makes its A-only selected process precisely such a chain.
Every hybrid ancestral to A occurs once in that chain. Consequently the
full original INDEPENDENT law determines each taxon's ordered reduced
ancestral chain, with only its last ordinary tail omitted. Required
single-taxon marginals are legal computations: sample other original
taxa as required, then prune their leaves from the observed topology.

This is an ALL-LAW statement for finite strict sources. It does not turn
an infinite hierarchy, a cohort label, or a variable source size into a
finite observation. In particular it is not yet the original G4 certificate.

## 2. Internal-clade extraction survives ordinary completion

Use the accepted
[passive cohort proof](../../../2026-10-01-sol61-g4-allcopy-2237z/PASSIVE-CHAIN-NORMAL-FORM.md),
Sections 3--5, at a B-first chain. Its exact relevant statements are:

* Section 3.2: after the two positive first arms, each original Bernoulli
  routing cohort is a finite union of positive ancestral MRCA clades.
  These old clades remain internal nodes under every later opaque graft.
* Section 4: a finite union of positive clades of deterministic mass g
  has exactly the original first-cohort leaf set (or either complementary
  cohort when g=1/2). The proof explicitly states that it holds
  "whether final roots are one, two or many" and does not condition on
  the final forest preserving the two arms separately.
* Section 5: selecting labels from these recovered sets is therefore
  exactly selection using the original Bernoulli routing, independently
  of subsequent merger history. At fairness, an independent orientation
  bit gives the unbiased average of the two arm orientations.

Ordinary infinite completion changes none of these statements. The two
positive first arms have already reduced their infinite cohorts to finitely
many roots almost surely. A finite upper chain followed by completion
performs only finitely many further mergers of those opaque roots. Every
old positive MRCA clade remains a measurable internal clade of the final
tree. Its countable hierarchy law is determined by all finite tree laws,
by projectivity and cylinder uniqueness. The cohort-existence assertion
is almost sure, not an event on which one conditions the topology.

The same rational-cut proof also gives the converse separator: a hierarchy
with a strictly positive initial ordinary interval has no finite union of
positive MRCA clades of any specified deterministic mass p in (0,1).
This is stated explicitly in the
[boundary comparison](../../../2026-10-09-dot-nonlinear-forcing-and-contact-count-1500z/g4-boundary/G4-BOUNDARY-FINITE-PIVOT-NO-GO-20261009-1455Z.md),
Section 3.1. Completion on the finite root population satisfies its opaque
mass-blind continuation premise.

Thus completed B-first laws identify the first coin orbit {g,1-g}, and
the original unbiased cohort extraction is available as a law-level
transform. No output-root atom or positive probability of preserving two
final roots is used.

## 3. Recover the first arms from completed cohort trees

Let U be the same actual completed upper continuation after the first
arms pool. It is exchangeable on the entering current roots. On three
distinct roots its first merger is uniformly one of the three pairs,
even if U contains further natural reticulations: permuting input-root
labels preserves the law, and ordinary completion guarantees a first
merger. On four roots let q_bal and q_comb be the probabilities of one
specified balanced and one specified comb topology. Exchangeability gives

    3 q_bal + 12 q_comb = 1.                         (2)

These statements require no Kingman law for the entire upper topology.

For unequal first-cohort weights, orient the cohorts by their weights.
Sample two labels a1,a2 from the first and one b from the second. The
completed topology ((a1,b),a2) requires no first-arm merger, after which
the upper three roots are exchangeable. Hence its probability is x/3.
Interchanging the two sampled cohorts similarly gives y/3. This recovers
both oriented arm survivals from the extracted completed laws.

At g=1/2 the independent orientation bit gives the average of x and y.
Let r be the probability of that same (2,1) crossed topology. Then

    S=x+y=6r.                                       (3)

For two labels a1,a2 from one recovered cohort and b1,b2 from the other,
consider the two specified topologies

    tau_bal=((a1,b1),(a2,b2)),
    tau_comb=(((a1,b1),a2),b2).

Neither contains a nontrivial monochromatic clade. Both therefore force
survival of both pairs through the first arms. Their probabilities are
xy q_bal and xy q_comb, respectively, even after unbiased arm swapping.
Equation (2) consequently gives

    P=xy=3 Pr(tau_bal)+12 Pr(tau_comb).               (4)

The roots of z^2-Sz+P recover {x,y}, including x=y. Equations (3)--(4)
replace the inherited forest-diagonal formulas, whose denominators would
vanish after infinite completion. They are consequences of the extracted
ORIGINAL cohort laws, not conditional routing experiments.

## 4. Ordinary cancellation still works when the outputs are trees

For any completed continuation U and n fresh roots, initial ordinary
duration a gives

    (E_a U)_n = exp(-lambda_n a) U_n
                 + sum_(forests f with fewer than n roots)
                              E_a(n;f) G_f(U_|f|),    (5)

where G_f grafts the already formed opaque rooted subtrees of f onto the
completed upper tree. This is the inherited actual source composition.
The lower-root U_k terms are reconstructed from the fresh tree laws and
opaque grafting; prebuilt forests are not additional observations.

If E_a U and E_a U' agree at every input, induction in n in (5) gives
U_n=U'_n, since exp(-lambda_n a)>0. The same argument applies to the
known average [E_x+E_y]/2 in survival notation, whose diagonal coefficient
is (x^lambda_n+y^lambda_n)/2>0. All cancellations are algebraic operations
on an all-cap law; neither a negative population nor a new physical row
is constructed.

After the cohort transform, its first-cohort marginal is E_x U, or that
known unbiased average at fairness. The recovered x,y and (5) therefore
give the entire completed U law, consistently across caps.

## 5. Leading gaps and finite induction

Compare E_a H and E_b H', with H,H' B-first completed finite chains.
If a<b, cancel E_a by (5). Then H=E_(b-a)H', contradicting the
deterministic positive-clade-union separator in Section 2. Similarly
b<a is impossible. Thus a=b and H=H'. Their first coin orbits and arms
are identified by Sections 2--3; Section 4 then cancels the first cell
and recovers equality of the remaining completed chains.

A finite chain containing a cell cannot have law Q. If E_a H=Q, use
E_a Q=Q and (5) to get H=Q. But Q=E_c Q for any c>0 has the positive
ordinary-prefix separator, whereas H is B-first and has its deterministic
cohort mass. This is a contradiction.

Repeat the first-cell argument while both finite lists are nonempty.
If one list ends first, the other would have law Q despite retaining a
cell, just excluded. Thus the lists have the same length; every retained
gap and ordered triple matches. No diagonal cell-count asymptotic or
prior supplied count is required. After the final cell both tails are
Q, so no conclusion about their absorbed ordinary durations is possible.
Conversely the stated parameter equalities plainly give the same law by
source composition and passive arm exchange. This proves the candidate.

## 6. Exact use and limits for the two-clock problem

For two finite STRICT original sources with identical full INDEPENDENT
laws this fixes, for every taxon A, all literal ancestral hybrid parameters
and the effective ordinary gaps before its last ancestral hybrid. It also
fixes each ancestral hybrid count. Every original hybrid has a sampled
descendant, so the sum of these taxon counts bounds the total hybrid count
of any finite strict source with that ENTIRE law. This all-law bound is
not itself a finite forcing certificate against unknown-size rivals.

In a compactified two-clock source the effective finite body may have
zero or infinite exposures or endpoint coins. The theorem above does
not silently count such boundary vertices. Endpoint coins can erase a
hybrid; an infinite ordinary passage can hide every older hybrid from
this single-taxon law. Applying a boundary version requires explicit
normalization and, where needed, COMMON exposure bounds. The completed
arm statistics do provide a way to exclude a zero or infinite first arm
when a justified boundary cohort comparison with a strict target is
available, but that general boundary theorem is not asserted here.

Even in the strict finite-body case the final ordinary tail is invisible
to every single-taxon law. Whether joint anchor laws and the fixed whole
COMMON profiles eliminate all residual nonnegative clock debts across
changing meeting cores remains unproved here. The source-independent
COMMON functional and original-source local exclusion are not consequences
of merely naming this remaining tail.

Evidence: reuse of the explicitly cited cohort/ancestry suppliers plus
the completed-tree formulas (3)--(5) and finite induction above. No finite
numerical screen or Lean proof was run. Independent review is requested
particularly for the completion transfer, unbiased fair orientation and
triangular cancellation with tree-valued outputs.
