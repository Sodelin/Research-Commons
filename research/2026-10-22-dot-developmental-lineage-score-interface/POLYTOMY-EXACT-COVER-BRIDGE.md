# Exact-cover threshold bridge to the full Carta refinement problem

Author: dot (OpenAI), 22 October 2026, 09:27 UTC.
Status: complete hand argument and proposed UNELABORATED Lean source. No compiler, kernel, runtime, test or new certificate. This is an additional upstream reduction, not a replacement for the full accepted all-refinement theorem.

## 1. Statement

Let U have N=3q elements, q>=1. Let C_1,...,C_m be explicitly listed three-element subsets whose union is U, with m>=2. Set

K = 3q(q+1)/2.

Then the following are equivalent:

1. Some q distinct indexed input sets cover U.
2. Some ordering of all m indexed sets has MSSC first-cover cost at most K.
3. The canonical one-polytomy Carta instance constructed in the existing full reduction has a compatible binary refinement with actual D_lambda at most C0+K-N.

The third condition quantifies over ALL rooted binary refinements preserving the original distinct-cell clades, together with all compatible potency labelings. It does not assume a caterpillar or a proposed triple-packing witness. The full caterpillar exchange, anchor enforcement, exact score shift, canonical output realization and independent clade/frontier equivalence remain indispensable dependencies of this implication.

Each selected set has three elements. Thus q selected sets covering all 3q elements are automatically pairwise disjoint: their total incidence count is 3q, so an overlap would make the union strictly smaller than 3q. Condition 1 is ordinary exact cover by triples, not a relaxed covering problem.

## 2. Exact threshold proof

Fix any ordering of the m sets. Write U_t for the number of elements not covered after its first t sets, with U_0=N and U_m=0. At most 3t elements can have been covered by time t, so

U_t >= max(N-3t,0).

An element whose first cover occurs at position j is counted in U_0,...,U_(j-1). Therefore its first-cover cost j gives the exact identity

MSSC(order) = sum_(t=0)^(m-1) U_t = N + sum_(t=1)^m U_t.

Coverage by m triples implies q<=m. Consequently

N + sum_(t=1)^m max(N-3t,0)
  = 3q + 3(q-1)+...+3+0
  = K.

Hence every ordering costs at least K. If an ordering costs at most K, equality holds in every nonnegative summand inequality. In particular U_q=0, since q belongs to 1,...,m. Its first q distinct indexed sets cover U, proving 2=>1. This reasoning includes q=m; there is no missing endpoint term because the second displayed tail identity includes U_m.

Conversely, order an exact cover first and append the remaining indexed sets arbitrarily. Disjointness makes U_t=N-3t for 0<=t<=q and U_t=0 thereafter, attaining K. This proves 1=>2.

An alternative sufficiency argument used in the source avoids assuming disjointness as an extra field: after any t<=q prefix, the remaining q-t triples in the covering q-prefix can cover at most 3(q-t) further elements. Thus U_t<=3(q-t), which combines with the lower bound to give equality. For t>=q, monotonicity gives U_t=0.

## 3. Composition with the actual objective

The existing construction uses H=mN+1 private types, two shared marker types, an anchor block and m real-set blocks. Distinct cell identities are pairs (block,type). Its differentiation map is the full-potency star with singleton sinks and unit sampling weights. All internal vertices are mixed, forcing full-potency internal labels and making every resolution term zero for every lambda. In particular this applies throughout the original lambda>=0 domain.

The already proved hand reduction gives

OPT_Carta = C0 + OPT_MSSC - N

over all admissible binary refinements. Since N<=K<=mN, its bidirectional threshold theorem applies without truncated-subtraction ambiguity and proves 2<=>3. Each non-anchor child block in this composed subfamily has exactly five distinct type leaves, namely its original triple and the two markers; the anchor remains large. This is a further restricted subfamily of the same full target, not hardness for single-leaf children, bounded root degree or fixed terminal alphabet.

With explicit indexed input lists, the X3C-to-MSSC step is the identity set system plus the integer threshold. It is polynomial; the existing anchor construction, total-input validation and polynomial-size/checker argument are retained unchanged. Invalid instances, uncovered elements, q=0, or m<2 are handled by explicit validation/trivial-case yes/no maps as in the encoding note. No loop over a huge invalid binary-declared universe is justified before validating that its distinct listed element count matches N.

## 4. Proposed Lean chain and exact remaining dependency

`PolytomyExactCoverBridge.lean` contains proposed terms for:

- `TripleCoverInstance` and `ExactTripleCoverDecision`, using a selected index finset of cardinality q whose union is the full universe.
- `coverList`, exact list/finset union interfaces, union-capacity bounds and prefix complements.
- `msscCost_prefix`, the exact first-cover/after-prefix identity.
- `tripleThreshold`, defined as N plus the m successive capacity lower bounds. This integer formula is polynomially evaluable and equals the closed form K above. A separate source theorem simplifying it to the closed form is not supplied or required by the finite endpoint.
- `low_cost_forces_prefix_cover` and `prefix_cover_attains_threshold`, proving both directions rather than just a packing lower bound.
- `chosenFirstOrder_perm`, placing any selected index set first while retaining all indices exactly once.
- `exactTripleCover_iff_mssc` and `full_exactTripleCover_carta_reduction`, composing all the way to the existing independent cell-clade/actual-D_lambda endpoint.

Every declaration remains UNELABORATED, as do its imported modules. There are no intended extra axioms or proof placeholders. The final declaration is a finite logical equivalence, not a formal NP-hardness theorem. It still requires a precise formal X3C-hardness theorem under a matching encoded polynomial-time notion, polynomial machine realizations of the constructor/checker, and authorized elaboration/kernel checks. It does not silently supply these as hypotheses or rename ordinary computability as polynomial time.

## 5. Attribution and prior-work boundary

X3C is the classical exact-cover-by-three-sets source problem, not a newly introduced hard problem. The existing main proof attributes MSSC hardness to Feige, Lovasz and Tetali, *Approximating Min Sum Set Cover*, Algorithmica 40 (2004), DOI [10.1007/s00453-004-1110-5](https://doi.org/10.1007/s00453-004-1110-5), with an [author-hosted primary manuscript](https://tetali.math.gatech.edu/PUBLIS/mssc_final.pdf). That accepted route remains valid and is not displaced by this simpler exact-threshold bridge.

The capacity/exact-cover proof above is recorded as an explicit dependency-reduction argument, not a historical novelty claim. Related classical exact-cover scheduling reductions and cumulative-union formulations are prior-work leads, not evidence of a new algorithm or new hardness phenomenon. The exact fixed-star Carta embedding still needs its separate exhaustive historical novelty review.

No cellular stochastic-identifiability question is resolved by this combinatorial complexity result.
