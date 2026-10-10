# Ordered-source population to ordinary-forest quotient

Contributor: Codex Rust implementation role, 10 October 2026. Status:
**hand-derived local refinement argument**, supported by finite independent
execution. This is not an accepted Lean theorem or full source-law admission.
It supplies the named missing correspondence in
[POPULATION-REFINEMENT.md](../design/POPULATION-REFINEMENT.md).

## Exact scope and inherited inputs

Fix a typed original `RootedBinary N`, finite copied-label carrier `Copy`, its
original sample assignment, an actual source-valid canonical snapshot `s`, and
one original population `i : Option E`. Require the inherited
`CoLocated N s i`: **every original copy**, through its actual live ancestor,
occupies this same original edge or ancestral root population. Freeze the
entire original vertex register. A source frontier containing several
populations requires the separate original panel/factorization theorem before
this argument can be applied to its different groups.

The original [merger](../../2026-10-10-dot-g7-pending-codex-recovery-0952z/source-store/d6e5b2b57cf03091f8b5b5a2c80cf49de39bab938c50a467b46b30e08f12871d.lean)
retains the first representative, grafts its ordered genealogy with that of
the second, replaces ancestry to the removed representative, and preserves
locations/registers. The inherited snapshot encoder removes dead genealogy and
population fields and event history. The actual
[effective coefficient definition](../../2026-10-10-dot-g7-pending-codex-recovery-0952z/source-store/df18fd3ffe02939b81fc062d48da60011a4724ae0d2cb9b9ea2e846e43b2e946.lean)
uses ordered `Choice.offDiag` and the exact
[half-rate lift](../../2026-10-10-dot-g7-pending-codex-recovery-0952z/source-store/b4434eb89aecfc007546908f404efc41cc0de809eb8497ed22c9e48a87e4dddf.lean).
Those definitions, rather than a fitted genealogy law, govern the port.

The encoded-image premise is material. Original Code validity is defined on
the decoded state and can permit dead option-field garbage or live `none`
defaults. The library instead requires actual `encode`/`encodeActual` output:
live genealogy/population fields are `some`, dead fields are `none`. The
zero-support argument below must account for all other Code destinations before
a complete all-Code row claim can be made from the restricted dictionary.

Let `Q(s)` recursively sort each genealogy's graft children by its minimum
original copied-leaf label and sort the resulting forest roots by that label.
This ordinary-forest readout forgets representatives and child orientations;
the source table itself continues to retain population and register fields.
An injective restricted-copy embedding transports labels to their original
global IDs before the canonical readout is formed.

## Merger and coefficient transport

The forest invariant gives a bijection between live representatives and
current genealogy roots. Distinct roots have disjoint, nonempty leaf fibres.
Consequently the minimum-label comparisons never tie, including when a
representative is not the smallest member of its fibre.

For each unordered pair of current roots `A,B`, there are exactly two ordered
legal choices `(a,b)` and `(b,a)`. Their literal destinations differ: the first
retains `a` and grafts `A,B`, while the second retains `b` and grafts `B,A`.
Their unordered readout is identical, because canonicalizing either graft
gives the same new root and all other roots are unchanged. Registers and the
original population stay fixed in both orientations. This is a free pairing of
the actual off-diagonal choices; it is not a multiplication of one arbitrary
destination probability by two.

Write `P_f(s,d;X)` for the normalized polynomial denoted by the inherited
coefficient list at fuel `f`. For an unordered forest `F`, form the full fibre
sum `U_f(s,F)=sum_{Q(d)=F} P_f(s,d;X)` over the actual finite source Code carrier.
The recurrence's diagonal contributes `X^n` when `Q(s)=F`, with
`n=choose(liveCard(s),2)`. A terminal snapshot contributes its unchanged
constant-one row.

On a child term `a X^m`, the ordered lift is

`Lhalf_n(a X^m) = a/(2(n-m)) * (X^m - X^n)`.

The inherited merger-cardinality and degree-descent lemmas give `m<n` for
every lifted child term. Thus the denominator is nonzero; totalized rational
division is not a substitute for this proof. `Lhalf_n` is linear on these
bounded-degree polynomials, so it commutes with the finite destination sum.
An induction hypothesis that the fibre polynomial depends only on `Q(s)`
therefore combines the paired ordered choices into

`2 Lhalf_n(a X^m) = a/(n-m) * (X^m - X^n)`.

This is exactly the unordered per-pair lift. The diagonal and terminal cases
also depend only on the ordinary forest. Induction on fuel supplies the
representative/orientation lumpability statement and the ordinary-forest
recurrence, subject to formalizing the finite sum and label transport.

For one specified unordered merger history from `k` to `j` current roots, that
recurrence gives the distinct-rate divided-difference polynomial

`sum_{r=j..k} X^choose(r,2) / product_{t=j..k,t!=r}(choose(t,2)-choose(r,2))`.

Its base case is the diagonal monomial. Applying the unordered lift to a child
history divides each lower exponent coefficient by the new rate difference;
the new highest coefficient is the negative sum of these contributions. The
standard partial-fraction identity gives the displayed new denominator.
Summing over all histories ending at the requested forest gives precisely the
history-count multiplier used by the existing LAW edge kernel. Earlier carried
genealogy subtrees remain opaque throughout this history count.

## Reachable-row optimization

The executable Rust library generates only exact merger-reachable canonical
snapshots. It does not enumerate the enormous `FinEnum (Code N sample)` universe.
The optimization needs a separate zero-support lemma before its dictionary
can be identified with the complete source row.

A direct proof attack follows the inherited raw coefficient recursion. Define
bounded reachability by the unchanged state or an actual ordered source merger
followed by a shorter path. Induct on fuel to show that a nonzero coefficient
term implies such a path to its destination. In the diagonal case a nonzero
coefficient forces `s=d`; in a lifted term nonzero output forces nonzero input,
and the induction hypothesis is prefixed by the actual merger. The
contrapositive makes every raw coefficient zero outside this support, hence its
normalized polynomial is zero. Stability of the canonical live-only encoding
under the inherited merger/encoder then restricts the support to the dictionary
carrier used by Rust. This argument must retain exact Code equality, including
the original population and register fields.

## Executed evidence and remaining proof work

[source_population.rs](src/source_population.rs) implements the literal
recurrence and explicit full fibre sum, capped at four local copies. The
[native build](evidence/population-build-2/BUILD-RECEIPT.json) passes 32 tests.
Its fixed-fixture probe matches every coefficient of the independent ordered
generator/spectral-projector oracle on
[eight fixtures](../design/evidence/population-rust-review-2/RECEIPT.json).
The four-singleton fixture has 193 literal destinations and 37 unordered
forests. Tests also compare every unordered coefficient with the existing LAW
edge kernel on zero through four roots and a carried-subtree fixture.

The original typed Lean coefficient code-generation comparison is pending.
The recovered component passes and the unrun smoke are recorded separately in
the [recovery packet](../../2026-10-10-dot-g7-pending-codex-recovery-0952z/README.md).
No new universal native refinement theorem is inferred from those prefix
checks or from the finite oracle. Formal obligations are the actual Code
encoding/merger transport, reachable zero support, injective label transport,
finite fibre-sum linearity, ordered-pair involution and recurrence uniqueness.

The conditional analytic consequence would then follow from the inherited
`actual_population_coefficients` at `X=exp(-pairRate(r,i)*t)` for positive
original rates and nonnegative time. It would still be a local, fixed-population
result. Full-epoch panel reassembly, boundary gathering, shared hybrid routing,
natural register initialization, ancestral completion, physical image,
admitted observation readers and the original whole source class are distinct
remaining obligations. The full end-to-end solver remains in progress.
