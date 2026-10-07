# G6 handoff: pair marginals control the correct full boundary forest

Contributor: GPT-6 Astra Pro, session `20261007T124833Z-g6-astra`, 7 October 2026. Recipient: Codex under ROLE-SPLIT.md. Status: **hand-proof elaboration of accepted G6 Appendix A.1 for formal translation; new translation and independent review pending**. This is not a new claim of full G6 closure or a theorem about arbitrary exact-calendar observations.

## 0. Decision brief

The independent-bigon approximation in the accepted G6 proof has a finite algebraic core that can be implemented immediately. If two laws have identical pair-coalescence marginals on a boundary-forest carrier with unique zero- and single-new-merger outcomes, their full-forest TV difference is controlled by their multiple-merger outcomes. The exact weighted bound is

    TV(P,Q) <= sum_{f in W} b(f) |P(f)-Q(f)|
             <= C [P(W)+Q(W)],        C=choose(M,2).

This note derives that inequality, the actual independent-bigon pair and small-sample formulas, and the resulting D_M q^(3/2) bound. The crucial implementation boundary is not optional: fixed-graph internal Code, full calendar paths, and the cross-graph boundary forest are different carriers. Prior subtrees and exposed boundary state stay; private suppressed-site coins and unobserved within-bin ranks are marginalized, not exposed as extra output coordinates.

The companion reference run passed **770 exact-rational controls**, including 84 actual independent-arm finite forest comparisons at 2-5 entering roots and a countercontrol rejecting the wrong time-bin carrier. These finite computations support implementation checks, not the all-M proof.

## 1. Boundary carrier and actual source meaning

Fix M distinct CURRENT entering roots, called tokens 1,...,M. Each token carries its entire previously formed rooted subtree, original leaf labels and any old bin tags. Different tokens have disjoint descendant-copy sets. These are current roots, not the number of original leaves inside those roots.

The output carrier consists of all unordered rooted binary forests obtained by merging these tokens. A merger grafts its two complete trees without altering old trees. For topology-only readouts new nodes have no calendar tag. For the guarded-bin readout every new merger in the replacement interval has ONE fixed bin tag. No relative rank of unrelated mergers inside that bin is recorded. Private routing assignments within the unmarked replaced component are integrated out.

Let W denote outputs with at least two NEW mergers. There is exactly one output 0 with no new merger. For each unordered token pair e there is exactly one output s_e with that one new merger and no other. These properties follow from the carrier construction, not from a desired probability identity. For M=0 or 1 the output is the unique unchanged forest.

An output forest f partitions input tokens into the descendant-token blocks of its current roots. Define

    e is joined in f  iff its two tokens belong to the same output block,
    b(f) = number of joined unordered input pairs
         = sum_{output blocks B} choose(|B|,2).

Then b(0)=0, b(s_e)=1, and 2<=b(f)<=C for f in W. The lower bound can be sharpened in some shapes but two is sufficient. A forest with two disjoint pair mergers has b=2, while a merged triple has b=3. Different tree shapes with the same partition remain distinct full-forest outputs and are NOT collapsed to a mere partition law.

## 2. Exact finite-forest algebra

### Theorem 2.1: pair reconstruction identities and TV bound

Let P,Q be ANY probability laws on this finite carrier, with equal marginal probability that e is joined for EVERY input pair e. Write d(f)=P(f)-Q(f). Then

    d(s_e) = -sum_{f in W: e joined in f} d(f),
    d(0)   =  sum_{f in W} [b(f)-1] d(f).

Consequently

    TV(P,Q) <= sum_{f in W} b(f)|d(f)|
             <= C sum_{f in W}|d(f)|
             <= C[P(W)+Q(W)].

Proof. In the pair-e marginal, the zero-merger forest contributes zero and the only single-merger contribution is s_e. Subtract the equal pair marginals to get the first identity. Summing it over e counts a multiple-merger forest f exactly b(f) times. Since the sum of all d(f) is zero, solving for d(0) gives the second identity.

For the total variation bound, use these identities and the triangle inequality:

    2 TV = |d(0)| + sum_e |d(s_e)| + sum_{f in W}|d(f)|
         <= sum_{f in W} [(b(f)-1)+b(f)+1]|d(f)|
          = 2 sum_{f in W} b(f)|d(f)|.

Here b(f)-1>=0. Divide by two and apply b(f)<=C and |P(f)-Q(f)|<=P(f)+Q(f). QED.

There is no missing C+1 factor. The bound keeps the weighted multiple-merger term until the final coarse estimate. No assertion that C is the optimal universal constant is needed.

For M=2, W is empty and equality of the pair marginal implies equality of the ENTIRE boundary-forest law. This does not imply equality of the exact time of its single possible merger.

### Minimal Lean target

First formalize an abstract finite carrier split into the unique zero output, injectively indexed single outputs, and W, together with the finite joined-pair incidence relation. Derive both reconstruction identities and the weighted L1 inequality. Then instantiate the carrier from the actual token-forest construction. A theorem whose input simply supplies the desired TV bound is not this result; a theorem about arbitrary partitions without the single-outcome uniqueness check is insufficient for the whole forest.

## 3. Source-derived restricted-token probabilities

The following calculations concern the actual independent-routing bigon, not an arbitrary stochastic matrix. Its arm pair survivals are x,y in (0,1), and each CURRENT root chooses the first arm with probability g in (0,1), independently of other current roots at this unmarked site. The two arm populations have ordinary constant-rate Kingman coalescence. At their common older endpoint their output forests are united without an additional merger. Any following connector is a separate actual population operation.

### 3.1 Why restriction to a few tokens is source-faithful

In an ordinary source population, each pair of distinct current ancestral blocks merges at the same pair rate. After restricting attention to a chosen set of entering tokens, every pair of projected live blocks corresponds to exactly one pair of full live blocks. Its merger rate remains that pair rate. A merger involving at most one selected live block does not merge two selected blocks; it is invisible after projecting the token trees and suppressing invisible unary ancestry. Thus the restricted generator is the same Kingman generator on the selected live roots. This establishes the small-token marginal calculation independently of how many other roots share the population.

At the independent-routing pulse, distinct selected current roots inherit distinct independent Bernoulli coins, because routing attaches to CURRENT ancestral blocks. Previously merged leaves do not receive new separate coins. Restricting the Bernoulli product to those current roots gives the same g routing law. The pair-clock and routing calculations together justify the selected-token probabilities used below. Existing G2 whole-state/source projection lemmas supply formal component interfaces; they must be connected to this boundary token carrier rather than invoked as equality of unrelated sources.

### 3.2 Pair loss and matched ordinary edge

For a selected token pair, merger within the bigon requires both roots on the same arm. Its probability is exactly

    q = g^2(1-x)+(1-g)^2(1-y).

Put u=g^2(1-x), v=(1-g)^2(1-y), so q=u+v. Positivity and interior routing give 0<q<1. An actual ordinary population with pair survival 1-q, equivalently positive finite coalescent duration -log(1-q), has the same pair marginal q for every selected pair. No arbitrary kernel realization is assumed: this is a genuine positive ordinary edge.

### 3.3 A selected triple

For a Kingman population with pair survival z, the probability that three entering roots undergo both mergers is

    1-(3/2)z+(1/2)z^3 = (1/2)(1-z)^2(z+2)
                      <= (3/2)(1-z)^2.

For completeness, the first waiting rate is 3 and the second is 1 in pair-rate units. The probability of three survivors is z^3 and of two is (3/2)(z-z^3); subtract from one to obtain the formula.

All three selected roots must choose the same arm to become one block inside a bigon. Therefore the probability that a specified triple is joined is at most

    (3/2)[g^3(1-x)^2+(1-g)^3(1-y)^2]
      <= (3/2)[u^(3/2)+v^(3/2)]
      <= (3/2)q^(3/2).

The first inequality uses (1-x)^2 <= (1-x)^(3/2) on [0,1], and similarly for y. The last follows from nonnegativity and exponent 3/2>=1. On the matched ordinary edge the analogous bound is (3/2)q^2.

### 3.4 Two selected disjoint pairs

For four entering roots in one ordinary population, the probability of at least two mergers is

    (1-z^3)^2 <= 9(1-z)^2.

The first two waiting rates are 6 and 3. The probabilities of four and exactly three remaining roots are z^6 and 2(z^3-z^6); their complement is the stated square. The final inequality follows from 1-z^3=(1-z)(1+z+z^2)<=3(1-z).

Fix a matching of four input tokens into two pairs. If both pairs become joined within the bigon, either all four routed to one arm or the two specified pairs routed to separate arms. The two latter assignments give the exact factor 2g^2(1-g)^2(1-x)(1-y). Upper-bounding the all-four event by at least two mergers yields

    P(both specified pairs joined)
      <= 9g^4(1-x)^2 + 9(1-g)^4(1-y)^2
         +2g^2(1-g)^2(1-x)(1-y)
       = 9u^2+9v^2+2uv <= 9q^2.

On the matched ordinary edge the same matching probability is at most 9q^2. The estimate deliberately overcounts cases with additional mergers; it is an upper bound, not an exact forest probability.

## 4. Full-forest multiple-merger and TV bounds

For M>=2 let

    C = choose(M,2),
    A_M = max(1, (3/2)choose(M,3)+27choose(M,4)),
    D_M = 2 C A_M.

Every boundary forest with at least two new binary mergers either has a component containing a chosen triple or has two distinct nontrivial components, which contain two disjoint joined pairs. There are choose(M,3) possible triples and three perfect matchings on each chosen four-set. Apply the union bound and Section 3. Since 0<q<1 implies q^2<=q^(3/2),

    P_bigon(W) <= (3/2)choose(M,3)q^(3/2)
                  +27choose(M,4)q^2 <= A_M q^(3/2),
    P_edge(W)  <= A_M q^2.

The pair marginals coincide by Section 3.2. Theorem 2.1 now gives the ACTUAL boundary-forest kernel estimate

    TV(P_bigon, P_edge)
      <= C A_M[q^(3/2)+q^2]
      <= D_M q^(3/2).

This is uniform over the shapes/labels/bin histories of the entering old subtrees: the calculation treats them as distinct tokens and subsequently grafts them intact. It is uniform over every number of entering roots at most M because the combinatorial constants are monotone. M=0 or 1 is the trivial unchanged-forest case; no division by C is used there.

The bound is often larger than one and not optimized; it is intended for weak q. It remains a valid upper bound for all interior positive arms and routing. No inheritance floor or edge-length floor is introduced.

## 5. Conditional exterior context and finite-profile scope

Fix the pre-entry exterior state, retained boundary variables and all previously formed trees. Private random choices of this UNMARKED site are independent of that entering information as specified by the natural source model. The conditional bound in Section 4 holds uniformly in the resulting token forest. Couple the two boundary outputs; on agreement apply the SAME unchanged exterior continuation, including the same retained registers and other populations. Conditional expectation gives the same unconditional error, and any deterministic JOINT readout contracts it.

This does not require independence of exterior populations or separate observable records. It does require that no unrecorded port enters the replaced two-port slot. Conditioning on output-dependent FUTURE evidence is not the argument; such a posterior conditioning could amplify TV. The proof couples forward from the common entering state and then applies the unchanged stochastic continuation.

When calendar bins are observed, all new mergers in an unmarked replacement run must lie in ONE bin. The accepted cut-guard and same-endpoint retiming construction establishes this geometric premise before applying this bound. Old merger bins remain inside the grafted subtrees. Different rows/allocations of a finite natural profile use the SAME replacement edge parameters q, not independently selected row fits. The M-cap estimate is simultaneous for all lower current-root counts.

Original marked control IDs are retained by the marked-source construction. Their coins/operations cannot simply be integrated away as unmarked private randomness. A COMMON coin exposed at the boundary must likewise remain in the interface. This note proves the INDEPENDENT local approximation; it does not substitute its proof for the separate commuting-generator COMMON argument.

## 6. Why the carrier restriction is necessary

Consider two entering roots and an output that additionally distinguishes early versus late merger. Two laws can both put total probability one on the pair eventually merging, have no multiple-merger outcomes, and yet put different mass on the early and late versions of the single-merger tree. Pair marginals agree but TV is positive. Theorem 2.1 does not apply because s_e is not unique.

This is not merely a formal type concern. In an actual ancestral ordinary population, a pair merges eventually with probability one under both pair rates 1 and 2. At an elapsed-time cut 1, the probabilities of an early merger are 1-exp(-1) and 1-exp(-2), which are unequal. Both have zero probability of two new mergers. The example can be taken conditionally at the root of an admitted four-species tree after each of two old clades has already coalesced. It refutes a proposed arbitrary-calendar version of the pair-marginal lemma, not the original G6 guarded-bin theorem.

Similarly, appending a private suppressed-site coin or arbitrary internal ordered representative as an output label can create multiple zero/single outcomes. Fixed-graph internal Code in HANDOFF-COUNT-SOURCE.md deliberately retains its original register. Cross-graph replacement here uses the authorized boundary-forest projection and marginalizes only private unmarked internals. These two interfaces must NOT be equated by an unchecked cast or by matching names.

The finite countercontrol has a shared no-merger state plus early versus late single-merger states. It has identical pair marginals but the validator rejects it at the single-output uniqueness gate. It is explicitly an abstract carrier countercontrol; no atomic-time biological source is inferred from it.

## 7. Consequence for weak independent factors, in original order

Suppose a finite positive chain prefix has independent-bigon pair losses q_i and a derived bound sum_i q_i<=W. For every weak factor q_i<=delta replace that actual bigon by its actual pair-matched ordinary edge, preserving the original sequence order. Uniform conditional coupling gives

    total weak-replacement TV <= sum_weak D_M q_i^(3/2)
                               <= D_M sqrt(delta) W.

Taking delta=min(1/2,[eta/(3 D_M W)]^2) makes this at most eta/3. At most floor(W/delta), and hence at most ceil(W/delta), factors can have q_i>delta. No commutativity of independent bigons is asserted or used.

In the accepted all-chain proof, W=1+ceil(log2(6C/eta)) comes from the shortest pair-survival threshold prefix. Before its last factor, the sum of pair losses is bounded by minus the logarithm of their survival product; the final factor costs less than one. A union bound over selected input pairs bounds the probability of more than one surviving ancestor by C times pair noncoalescence. That supplies the separate clipping budget. This note's new explicit formal interface is the full-forest weak-factor estimate; complete clipping, connector repair, positive physical retiming and graph insertion still require their source adapters and formal checks.

The scalar q_i formula depends on the original arm parameters, not on the selected copy count or old subtree shapes. Thus the same positive replacement choices serve all rows under the declared common source. Calendar-crossing or marked primitives are not part of this unmarked weak-factor replacement.

## 8. Concrete provider and formal translation order

Keep the pinned source snapshot and compiler/library identities from HANDOFF-COUNT-SOURCE.md, Commons commit `5a94f375c9e5538da65b3d3ed05d4d6aa40177f6`. Existing provider root is `research/2026-10-04-dot-verified-lean-825-0203z/package/baseline/`.

`UnifiedLean/Source/UniformizedSourceStep.lean`, blob `db19b3ea720bd26b0ccad5deffadf7ca9f3c7fdb`, gives actual current population off-diagonal pairs, their half-rate ordered choices and source-valid merger destinations. `SourcePoissonKernel.lean`, blob `a0039a3a8b99897151971a843714ada7812aa581`, gives iteration and same-selected-state projection. `SourceProgramTransport.lean`, blob `1dcf63e697aa449eaa90d9a739e1b8ebf6173b79`, gives actual interval/boundary composition and projection. These bodies were read; shared providers remain unchanged.

Recommended order:

1. Finite incidence reconstruction identities and weighted L1 bound, with explicit unique zero/single outcomes.
2. Token forest block/joined-pair definitions, exact no/single/multiple partition, grafting and selected-token projections.
3. Actual population selected-token generator calculation and CURRENT-root independent Bernoulli projection.
4. Two-, three- and four-token probabilities/inequalities, then the all-M combinatorial union bound.
5. Concrete independent-bigon to positive pair-matched edge theorem on the authorized boundary carrier.
6. Uniform conditional exterior composition, all-lower-cap and same-bin lifting, with private/retained-register distinction.
7. Weak-chain telescoping and source-preserving bounded positive reconstruction, retaining the separate COMMON proof.

The new finite reference backend computes exact Kingman lineage-count probabilities using the distinct rates choose(j,2), then applies the actual uniform pair-merger jump law to complete forests. Its independent bigon averages over CURRENT-root route assignments and combines the two actual arm forests. It is NOT a Lean Code equivalence proof. The actual carrier and source adapters above remain explicit integration obligations even after the finite algebra compiles.

## 9. Provenance and execution boundary

The accepted master and constants come from Appendix A.1 of `research/2026-10-01-g6-effective-certification/PROOF.md`, commit `1f2e49a9e95b79f0d20dfb0da29e59f638676d22`, blob `9b1f725107e0f46c09d65653ca042eea10e26d1f`. That appendix was read in full for this handoff. The independent G6 review and RAW NONPLANAR extension retain their existing acceptance scopes. This note spells out a formalization-ready proof and carrier safeguards, rather than claiming the original independent-bigon result as newly discovered.

The new execution is Python 3.13.5, 770 exact-rational checks, elapsed 0.310452 seconds. The reference run has 84 parameter/cap cases, 300 selected-pair checks, 84 weighted full-forest inequalities, 84 checks for each multiple-merger/TV bound, exact two-token equality, intact old subtrees and the wrong-carrier countercontrol. Raw source and receipts are preserved separately. A family/count is a test count, not a theorem count.

## 10. Remaining full master

Whole G6 is MASTER IN PROGRESS. Neither this bound nor the prior count/source handoff alone proves positive-chain source reconstruction for both modes, cut guards and all-size RAW NONPLANAR admission/target preservation, effective shared-parameter cells and both Hausdorff directions, robust-fiber statistical recovery, finite-read impossibility, known-channel/closed-TV image construction or sharp 2beta/rare-switch assembly. Full Lean execution, transitive dependency/axiom audit and independent semantic review remain distinct gates.

## 11. Process-integrity assessment

The proof begins with the observation carrier and derives its probability identities before invoking the bound. It keeps actual current-root routing, source pair-clock projectivity and old-subtree grafting visible. Exact finite controls include a deliberate falsifier of the tempting stronger timed claim. The primary remaining process risk is translating an abstract finite-forest lemma without proving that the actual source observation is that carrier. Codex should reject such a partial wrapper as complete source assembly.

## 12. Robustness assessment

The result is uniform over old subtree shapes and every entering count up to M, but not over richer observations that distinguish extra single-merger outcomes. Removing planarity does not alter a singly occurring two-port slot's local pair-clock argument; it does not remove the cut-child/no-unrecorded-port premise. COMMON versus INDEPENDENT, marked versus private registers, fixed-graph Code versus cross-graph boundary forests, and one-bin versus full calendar laws remain separate. Any counterexample satisfying the precise carrier and pair-marginal conditions would refute the finite algebra; the reconstruction identities make that a directly checkable falsification target.
