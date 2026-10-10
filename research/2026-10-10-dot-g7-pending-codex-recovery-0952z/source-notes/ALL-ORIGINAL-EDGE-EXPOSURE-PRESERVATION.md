# All-original-edge exposure preservation: actual-source proof and Lean binding audit

Contributor: dot, 2026-10-10 01:29 UTC. This is a complete hand/source argument for the named integration obligation, not a new polynomiality claim and not a Lean certificate. The original mathematical argument and frontier compiler are attributed to the 2026-10-01 continuous-design packet; its independent master review accepted this contract. The audit below identifies precisely which steps are already declarations and which source-specific composition remains to be elaborated.

## 1. Frozen original contract and exact target

Immutable prior commit: `904721f6c06c4d244685d05159d1c09bc84f99ab`.

- `research/2026-10-01-g7-continuous-design/PROOFS.md`
- `research/2026-10-01-g7-continuous-design/law_compiler.py`
- `research/2026-10-01-sol61-head-audit-1956z/G7-EXACT-MASTER-REVIEW.md`

Their byte pins are in the adjacent manifest and local `prior/` directory. The reviewed master takes finite n >= 2 and exactly r supplied original binary hybrid IDs, parent bits, finite contemporaneous sample menus and finite unranked topology readouts. Sources are original rooted binary LSA, taxon-cofacial planar cut-child DAGs, with parallel edge occurrences allowed. All original edge coalescent lengths are positive and finite; natural inheritance is interior. COMMON or INDEPENDENT is fixed globally, or forms a declared finite tagged union. Controls act on the original IDs. These hypotheses are not replaced by a bounded compressed core or by an unknown-hybrid cutoff.

Fix one such original graph N, its parent registry H, sample map, natural inheritance p, mechanism and control row m. For a strict calendar C and positive rate bank r put

    exposure(C,r,e) = r.edge(e) * (C.age(source(e)) - C.age(target(e))).

The target identity is: if all these exposures agree for (C,r) and (D,s), the completed actual source laws have the same final full forest/register marginal, hence the same declared finite unranked readout law. The ancestral rates may differ positively. The same equality holds for every original-ID control row using the SAME natural p and once-drawn register distribution.

No equality of timed bins, event ages, checkpoint histories, raw representative identities or calendar words is asserted. There is no assumption that chronological interval survival coordinates are independent. The root-population rate disappears only through the already justified infinite ancestral completion.

## 2. Actual single-population kernel and its exact clock

Condition on the current source state and its original register. For an original edge e, let C_e be all original copies whose current ancestor occupies e. C_e is a union of complete ancestral blocks, rather than a collection of independently retained descendants. The actual restricted state on C_e is `panelCode`; it is colocated in e.

`G7SinglePopulationPolynomialKernel.actual_population_polynomial` gives every actual restricted transition mass as a rational polynomial evaluated at exp(-r.edge(e)*t). Its polynomial depends on the original source state, destination and labelled genealogies, not on r or t. Consequently, equality of r.edge(e)*t is sufficient for equality of the entire restricted PMF, even when every other rate in the two banks differs. This is a direct comparison of each finite destination mass, not a fitted table.

Define K_e(a) on a colocated forest by taking the actual restricted source kernel with every rate equal to one and duration a >= 0. The preceding identity identifies a chronological fragment of duration t exactly with K_e(r.edge(e)*t). No zero-rate bank is needed. `SourceEpochSemigroup.actual_source_time_add`, together with preservation of the copies' population through an epoch, gives

    K_e(a) ; K_e(b) = K_e(a+b),   K_e(0) = identity.

It holds on the entire finite carried genealogy state. The ordered-pair convention is preserved: each ordered pair has rate 1/2 and total rate is choose(k,2). There is no unproved switch between ordered source grafts and unordered tree probabilities; child-order forgetting is a final readout.

## 3. Exact full-source epoch factorization, including nonbridge edges

For a fixed actual entering state, all C_e are disjoint and each is ancestor-closed. The ancestral population is another disjoint coordinate. Copies currently waiting at original nodes cannot coalesce and contribute an identity coordinate.

`G7PopulationForestReassembly.actual_smaller_source_reassembly` splits the full retained forest law into the actual restricted law on a chosen population panel and its actual complement, then deterministically rejoins their whole genealogies, population coordinates and unchanged register. `G7FiniteForestReassembly.actual_finite_forest_reassembly` gives the corresponding finite-index identity. Iterating this split over the finite ORIGINAL edge type and root population gives the product of the actual population-coordinate kernels, conditional on the full entering state. This is exactly the active-population induction already used by `G7FullEpochPolynomial.polynomial_by_active_set`.

No bridge predicate occurs in this factorization. A nonbridge edge inside a reticulation cycle, either incoming parallel occurrence, an empty population and the ancestral population all have their own original location. Parallel edges remain distinct because `originalPlace` is injective in Option E. The descendant panels may be random and correlated before conditioning; this statement does not make their unconditional laws independent.

This is the all-edge replacement for the narrower G1 BridgeActor construction. G1's private-actor algebra remains reusable as finite PMF algebra, but its existing bridge ownership theorem is not asserted for nonbridge edges.

## 4. Source-derived lifetime and local boundary action

For e=(u -> v) in the forward graph, backward-time entry to e can occur only when the one original node v is processed. Indeed an ordinary entry targets its own incoming edge; a hybrid pulse targets one of its two actual incoming occurrences; both have target v. No other original node can introduce an ancestor into e. The one exit operation for e removes every current ancestor on e to node u. No exit creates an edge occupant. Epoch mergers preserve each original copy's population.

These statements follow literally from `ordinaryLocation`, `exitLocation`, `rootLocation` and the actual hybrid parent records, with encode/decode transport supplied by `SourceBoundaryLocations`. Calendar scheduling visits each original node once and each original edge exit once. Strictness puts the entry at age(v), the exit at age(u), and age(v)<age(u). The existing physical-support induction (`SourceCalendarPhysicalSupport`, `SourceInitializedCalendar`) shows that these are the actual supported states, not additional admissibility premises.

It follows that after v's routing and before e's exit the set C_e is fixed. Mergers may change its partition into live genealogies but cannot add or remove any original copy from C_e. No unfinished below-edge event can later contribute a lineage: all vertices reachable strictly below v have earlier age and have already been processed. This uses acyclicity/strict calendar support, not a bridge or level-1 restriction.

Consider a boundary strictly inside this lifetime. An exit f distinct from e acts only on location f. A node w distinct from v acts only on location node(w) and routes only into edges whose target is w. Thus neither can read or modify e's current genealogies, nor add a new copy to C_e. They act on the complementary coordinate. At e's own closing date its kernel is gathered immediately before its own exit, never across that exit. At its opening date it remains after v's node action. Other equal-date operations can be kept in their original exit-before-node phases; the argument does not swap entry and exit at a common endpoint.

For an INDEPENDENT pulse on the complementary coordinate, the set of current AtNode owners is unchanged by an e-local merger, and its product Bernoulli distribution is unchanged. For a COMMON pulse, the original register is fixed under conditioning. Under forcing, the corresponding actual deterministic routing is also unchanged. Therefore all three cases genuinely act on the complementary coordinate, not merely on a disjoint set of names.

## 5. Derivation of the required local commutation

Fix a supported state in e's open lifetime. Write its full retained state as (a,b,R), where a is the entire e-panel, b is the complement and R is the fixed original register. Section 3 derives the local epoch factor in the form

    L_e(a,b,R) = K_e(a)(da') * delta_(b,R).

Section 4 derives every safe complementary boundary or complementary population factor as

    B(a,b,R) = delta_a * B_R(b)(db').

These are identities obtained from the literal source operations. For any final event A, the two compositions have the same finite sum

    sum_(a',b') K_e(a,a') * B_R(b,b') * 1_A(a',b',R).

Commutativity of multiplication and finite sum exchange prove L_e;B = B;L_e. Equivalently this is `PMF.bind_comm` followed by the deterministic full-forest reassembler. No assumed source-kernel commutation field is introduced. Random panels cause no difficulty: prove this for each supported entering state and then bind the equality against its actual distribution.

This proof does NOT commute an entire global epoch through a boundary. Such a statement is false: two lineages on the boundary's exiting edge have merger probability 1-exp(-rho*t) before the exit and zero merger probability at their common node immediately after it. Even if that exit is unrelated to some other edge e, the global epoch still contains the exiting population. Only the separated e-local factor commutes.

## 6. Complete gathering, not a single-swap endpoint

Expand every chronological interval into its finite conditional population product from section 3. Each e-local factor occurs after e's single opening and before its single closing. There are finitely many factors and boundaries.

Starting with the last e-local factor, move each earlier factor rightwards past intervening complementary population factors and safe boundaries until it is adjacent to the accumulated e-factor immediately before e's exit. Every move is licensed by sections 4-5. It never crosses the opening or closing. Compose adjacent factors by section 2. This removes all internal chronological fragments of e and replaces them by one factor

    K_e(sum_j r.edge(e) * delta_j).

The original sorted dates partition the complete interval [age(v),age(u)], so the sum telescopes exactly to exposure(C,r,e). Empty populations have the identity kernel and require no exception. Do this for every original edge occurrence. The argument is finite, and each move preserves the full joint final retained state after any remaining continuation. It does not rely on independent marginal sampling.

After all edges are gathered, each original node receives the completed output forests of all its forward child edges, performs its actual original routing once, and creates the input forests of its incoming edges. This is the old whole-edge frontier compiler, now related to the literal chronological source kernels. At the original root the collected forest enters the ancestral population. The reviewed G7 selected-completion adapter and G2 actual limit give its rational completion law, independently of the positive ancestral rate.

## 7. Calendar-order independence and the full frontier formula

Gathering first gives the frontier interpreter in the reverse-topological order induced by C. This does not yet compare arbitrary calendars, because incomparable original vertices can change order. The following finite sum removes that remaining issue.

A complete frontier assignment records an input and output labelled forest for every original edge and the original routing choice at every hybrid. Use a fixed canonical encoding of live forest blocks, or use the full selected forest index; do not sum duplicate raw representatives as distinct forests. An inconsistent assignment has weight zero. Its weight is

    initial singleton indicator
    * product_e K_e(exposure_e)(input_e, output_e)
    * product_v B_(v,R,gamma,m)(child outputs, parent inputs)
    * ancestral rational completion factor.

The desired terminal probability is the finite sum of these weights over assignments with that terminal readout. B is the actual node routing mass: deterministic at an ordinary vertex; the current-lineage Bernoulli product at an INDEPENDENT hybrid; the fixed stored bit at a COMMON hybrid; and the actual forced original-ID route when controlled.

Induction along any reverse topological order expands its frontier binds to exactly this product/sum. Each edge factor and node factor appears once, every local interface is matched, and finite distributivity sums exactly the internal assignments. All topological orders therefore give the same value: they are just different orders of summing the same finite assignment table. Equivalently, adjacent incomparable vertices touch disjoint edge occurrences and their conditional kernels commute; no ordering of comparable vertices is exchanged.

This proves the target whole-edge exposure identity for arbitrary strict calendars, including calendar order changes and ties among incomparable nodes. The argument covers all original edges, with no assumption of disjoint reticulation cycles or bridge ownership.

## 8. Natural initialization, controls, readout and polynomial consequence

Integrate the conditional-register identity exactly once against `originalRegisterPMF N p`. Keep this natural initialization unchanged for every control row. Only node transitions are changed by the original mask, using the inherited controlledMode semantics. In particular a forced common hybrid does not force the initial natural p or resample another source bank.

Each K_e is the already proved rational polynomial in x_e=exp(-exposure_e). Every node mass is polynomial in the same original natural gamma variables (or an actual forced endpoint); the initial register mass is also polynomial in those same natural variables. Completion is rational. The finite frontier sum is therefore one rational polynomial table for the actual completed law, sharing exactly one graph/edge/gamma bank across every row and response. A finite declared rooted/unrooted unranked readout is its linear pushforward. Ordered internal child encoding is forgotten only by that declared projection.

This does not identify the newly derived whole-edge table with the currently accepted interval-symbol table by syntactic substitution. Equality is through their common actual source law. It does not replace multiple interval variables by independent edge variables without the gathering proof.

For zero copies use the empty forest's deterministic law; for one copy use the deterministic singleton genealogy. The existing Nonempty Copy completion consumer handles the latter, while the accepted G2 all-panel results include the empty panel. No artificial nonempty assumption is added to the original finite sample menu.

## 9. Exact full parameter coverage in the original contract

Choose any one strict calendar C0 for the fixed finite acyclic graph. For each desired positive finite exposure ell_e set

    r0.edge(e) = ell_e / (C0.age(source(e)) - C0.age(target(e))).

The denominator is positive, so r0 is a positive rate bank; choose any positive ancestral rate. Its whole-edge exposures are exactly ell. Conversely every physical C,r produces such positive exposures. Thus every physical source law is represented on the fixed calendar and every positive whole-edge exposure vector is physically realized.

Equivalently, the survival image is exactly the open cube 0<x_e<1: exp(-ell) is in that cube, and for any x in it take ell=-log(x)>0. The realization map need not be algebraic; the source family allows positive real lengths/rates. The coefficient table and the represented image used by real-algebraic policy synthesis are algebraic in x and gamma. This distinction matters: no QE claim about exponential constraints or a tied-rate model is required.

Fixed rate equalities, metric bins and arbitrary timing constraints are outside this original master contract. They cannot be inferred from this coverage proof.

## 10. Formal disposition and remaining master boundary

Already accepted, byte-pinned source providers supply: literal source operations and current-owner pulses; full source physical support; single-population actual polynomial and rate-only dependence; actual semigroup; ancestor-closed panel restriction and full forest product/reassembly; actual completion and natural/control initialization.

The complete sections 4-7 all-edge lifetime/reassembly and finite frontier gathering argument is hand/source-level here. No Lean declaration currently asserts that whole gathering identity, nor does this document claim one compiled. The hard new elaboration is an all-original-edge finite frontier carrier with its source projection, safe local update binding, and the complete expansion/gathering induction. The G1 actor generic algebra can shorten its finite probability manipulations, but its bridge instance does not discharge these source bindings.

If elaborated and audited, this result discharges the original whole-edge exposure/independent-cube source-parameter coverage obligation. It does not by itself discharge exact finite cofacial admission/enumeration, executable whole-table extraction, verified first-order real QE, algebraic winning-fiber selection, executable policy synthesis or full Pareto certificates. Existing rank/resource semantic drafts remain separately frozen and uncompiled pending their queue. These are formal/implementation obligations toward an already accepted hand theorem, not newly alleged mathematical gaps.
