# Canonical native population and epoch correspondence

Contributor: dot, 2026-10-22. Independent complementary source review for PR2;
the provider/capture/exporter remains owned by its existing author. This is a
mathematical hand derivation about the pinned source algorithms, plus an
unelaborated Lean proposal. It is **not** a Rust semantics verification, compiled
certificate, executed test, or admission of an original source family.

## Exact source basis

The complete relevant bodies were read, not executed:

- [Native population recurrence](https://github.com/Sodelin/Research-Commons/blob/0874c13e2b71a88154ac2bc8a7cb033965213fc0/research/2026-10-21-lean-rust-solver-builder/native/source-inputs/research/2026-10-10-codex-lean-rust-parity/rust/src/source_population.rs), restored from 4e556c4a, SHA256 6afebffe8bb727a1c92bd113d479f01f0b2877bbf527c79866247805bc21da7c.
- [Native epoch](https://github.com/Sodelin/Research-Commons/blob/0874c13e2b71a88154ac2bc8a7cb033965213fc0/research/2026-10-21-lean-rust-solver-builder/native/source-inputs/research/2026-10-10-codex-lean-rust-parity/rust/src/source_epoch.rs), SHA256 c46a498ac2b5a0f3bc3ea246cc4f6d012ff58871292b8af84cfebe3d45b40354.
- The accompanying complete `polynomial.rs` and `forest.rs`: exact rational sparse arithmetic and the ordered `Tree` constructors, respectively.
- [Original snapshot](https://github.com/Sodelin/Research-Commons/blob/1138a5b1a281caa00b38e0976db95b586938754b/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/4628112bbbc69528748bbc93f8a3f8200bc802a6e72417fb90c39e7acd49f744.lean), [executable enumeration](https://github.com/Sodelin/Research-Commons/blob/1138a5b1a281caa00b38e0976db95b586938754b/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/6dabfdee6e47169a0135bc26523230213785338538c8179fc67d3cbc64cc3138.lean), and [original forest operations](https://github.com/Sodelin/Research-Commons/blob/1138a5b1a281caa00b38e0976db95b586938754b/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/d6e5b2b57cf03091f8b5b5a2c80cf49de39bab938c50a467b46b30e08f12871d.lean).
- [Original effective coefficients](https://github.com/Sodelin/Research-Commons/blob/1138a5b1a281caa00b38e0976db95b586938754b/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/df18fd3ffe02939b81fc062d48da60011a4724ae0d2cb9b9ea2e846e43b2e946.lean) and [single-population kernel](https://github.com/Sodelin/Research-Commons/blob/1138a5b1a281caa00b38e0976db95b586938754b/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/b4434eb89aecfc007546908f404efc41cc0de809eb8497ed22c9e48a87e4dddf.lean).
- [Existing full-epoch support theorem](https://github.com/Sodelin/Research-Commons/blob/1138a5b1a281caa00b38e0976db95b586938754b/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/188177cf95a52762d2f37148c7db2c1d9120d16d5764eabe1927854d7c766d0a.lean) and [effective full coefficients](https://github.com/Sodelin/Research-Commons/blob/1138a5b1a281caa00b38e0976db95b586938754b/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/85bed5b975ebb09a4042952aa486459d5cf422903d4356ac049d6d681b891994.lean).

The original theorems and their existing review qualifications are reused, not
claimed as newly checked. PR2's particular-table certificate exporter at
0874c13e remains a separate, uncompiled candidate. No exporter is replaced here.

## 1. Relation and quantifiers

Fix one original typed graph `N` whose vertex, edge-occurrence and taxon carriers,
root, source/target arrays and leaf array equal the native Context literally.
Fix the local Copy carrier `Fin context.sample.len()` and the literal sample
map. This is an explicit premise, **not** a consequence here of
`Source::validate`, a digest, or a named import.

Interpret native `Leaf(i)` as original `.leaf i` and `Node(a,b)` as ordered
`.graft a b`. Interpret all three Location tags without quotienting edge IDs or
root IDs. Interpret every register position, including nonhybrid vertices.
The native global-label injection is not used for this internal relation.

A canonical snapshot has genealogy and population present at every live index,
and both absent at every dead index. The native validator explicitly enforces
this, sorted distinct live indices, finite bounds, representative/ancestor
fibres, disjoint well-labelled trees, and original descendant checks. Where
the actual typed `SourceValid` witness is supplied, the literal snapshot
therefore determines a Code, denoted `J(s)`. This review does not formally
verify the DFS or parser that supplies such a witness.

The original Code subtype is larger: SourceValid of its decoded state does
not force canonical option fields. No bijection onto all Code is assumed.

## 2. Canonical round trip, merger and keys

For canonical `s`, encoding its decoded state returns exactly `s`. Live,
ancestor and register are unchanged by definitions. At a live index the
present genealogy and location are decoded and re-encoded unchanged; at a dead
index the encoder writes none, already equal to the canonical fields.
Subtype proof fields are irrelevant by proof irrelevance.

For a legal ordered pair `(a,b)`, the original merge followed by encoding has:

1. live set `live \ {b}`;
2. ancestor `x ↦ if ancestor[x]=b then a else ancestor[x]`;
3. graft `(genealogy[a],genealogy[b])` at `a`, none at `b`, and unchanged
   genealogy at every other index;
4. none population at `b`, unchanged population elsewhere;
5. the complete unchanged register.

These are exactly the assignments in `merge_unchecked`. The original history
append and dead-field garbage are discarded by encoding, not compared to the
native history-free structure. No child swap or minimum-survivor normalization
is permitted. `a≠b` is essential to this calculation.

The native key is injective on canonical valid snapshots of the fixed Context.
Decimal nonnegative integers have a unique representation. Tree strings obey
the unambiguous grammar `digits | (tree,tree)`; matching parentheses identify
the unique root comma. Semicolons delimit option entries and cannot occur in
trees or tagged locations; `-` differs from every present value. Distinct
V/E/A tags distinguish locations. Fixed field markers delimit the live and
ancestor lists, option arrays and fixed-length Boolean register. Equality of
keys therefore gives equality of all literal fields. Sorted live order makes
vector equality agree with finite-set equality. Lexicographic key order need
not agree with any formal FinEnum order.

Consequently replacing an existing map value with another destination having
the same key does not discard a different Code. This is a source-level grammar
argument, not a verified Rust String/BTreeMap theorem.

## 3. All extra formal destinations have zero coefficient

For canonical `s`, any fuel `f`, and any noncanonical admitted Code `d`, every
term of `coefficients N f (J s) d` has rational coefficient zero.

Proof by fuel induction. At fuel zero or terminal live count, `J(s)≠d`, so the
sole indicator coefficient is zero. Otherwise the holding indicator is zero.
Every merger is canonical by encoding. The induction hypothesis makes each
recursive term's coefficient zero; the existing `liftTerm` maps it to two zero
coefficients. This includes rational division's zero-denominator convention,
although the genuine nonzero support also satisfies strict exponent descent.
Thus the resulting polynomial is zero.

`NativeCanonicalPopulationBridge.lean` states this stronger termwise result,
its polynomial consequence, and the round-trip/merger canonical lemmas. The
source has not been elaborated. This eliminates a real coverage ambiguity:
the native carrier need not enumerate irrelevant noncanonical Codes, while
the conclusion must still quantify over every original Code.

## 4. Universal successful-return coefficient induction

Let `R_f(s,d)` be the rational polynomial at destination `d` in a normal return
of the native private `coefficients(f,s,limits,work)`, interpreted as zero
when absent. Work/caps may refuse a return; they never license a partial row.
Assume exact native rational/map operations have their documented ordinary
semantics, and the literal typed graph/state relation above. This is the
source-algorithm model being audited, not an imported Rust semantics theorem.

For every original Code `d`, the induction yields

`R_f(s,d) = exprPolynomial (coefficients N f (J(s)) d)`.

Here the native side sums all literal entries mapped to `d`; key injectivity
makes the stored canonical table a special case of that total fibre sum.

Base: fuel zero or at most one live lineage returns the identity row, exactly
the formal indicator polynomial. All other destinations, including absent and
noncanonical destinations, have coefficient zero.

Step: let `k=|live(s)|≥2` and `h=k(k−1)/2 = choose(k,2)`. Native loops visit each
ordered distinct live pair exactly once. Under co-location, the existing
`populationChoices` equivalence identifies these pairs with **all** formal
Choice values, with the unique original population. This is not true for a
mixed-population entering state; the public population entry point checks
co-location and recursive mergers preserve it.

For every destination the native row is therefore

`1[d=J(s)] X^h + Σ_(a,b) L_h(R_(f−1)(merge(s,a,b),d))`,

where the rational linear operator is

`L_h(Σ_m c_m X^m) = Σ_m c_m/(2(h−m)) (X^m−X^h)`.

The merger relation identifies recursive starting Codes. The induction
hypothesis identifies each polynomial. The formal list recurrence has the
same expression, possibly in a different enumeration order and with repeated
or zero monomials. Linearity of `L_h`, distributivity, and commutativity of
finite rational sums justify combining equal exponents **before** applying
the lift. This is the exact reason canonical sparse normalization is sound;
matching normalization/mass alone would not prove it.

Every nonzero recursive exponent is at most `choose(k−1,2) < h`, by induction
or the original `kernelExpr_bound` and `merger_exponent_lt`. Thus the native
`SOURCE_DEGREE_DESCENT` branch does not remove a genuine supported term.
With the inherited maximum four local copies, `h≤6`; the denominator's
machine-integer conversion is exact. Zero polynomials omitted before or after
addition contribute zero under the linear lift. A previously canceled key
may be reinserted later without changing the accumulated polynomial.

`population_row` uses `f=card Copy`. Composing this mathematical recurrence
identity with original `actual_population_coefficients` gives the entire
population law at each positive original bank and nonnegative duration.
Its additional mass/register validations are consistency checks, not the
proof of the identity. No extension beyond the native four-copy profile is
claimed. No executable, parser, object or invocation is certified here.

## 5. Epoch representative selection and the actual remaining join

The native epoch additionally quotients by the **full selected view**, retaining
one lexicographically chosen snapshot witness. That witness need not equal the
formal `findRepresentative`. Requiring literal witness equality is unnecessary
and generally wrong. What is needed is congruence of subsequent reassembly.

For original population `i`, define the whole-copy panel
`K_i={x : population[ancestor[x]]=i}`. Validity implies ancestor closure, not
merely a set of current roots. The native ascending `copies` array is a
bijection `Fin |K_i| → K_i`; `outer_to_local` is its inverse. Restriction maps
every tree leaf, ancestor and sample through that same bijection. Global
observer labels do not replace this map.

Panels for distinct population tags are disjoint. A merger within one panel
preserves every copy's population, so no later panel changes membership.
This justifies computing each panel from the *entering* snapshot even while
joining it into progressively modified witnesses.

For fixed `K_i`, the full view after joining a supported local destination is
the local destination view relabelled back on `K_i`, and the previous outer
view on its complement; its register is the unchanged entering register.
This follows coordinate by coordinate from `join_panel`, and is also explicitly
checked there. Thus equal outer views and equal local views imply equal joined
views regardless of chosen representative IDs. Zero-deletion and merging equal
selected keys are sound under subsequent joins by bilinearity of polynomial
multiplication and this congruence. This is the essential quotient argument,
not a claim that selected-view equality implies literal Code equality.

An induction over the native edge-occurrence list followed by ancestral root
therefore describes its final selected coefficient as the finite sum, over
all tuples of supported local destinations, of the product of their embedded
population polynomials, grouped by the glued full view. Copies at node
boundaries remain in the untouched complement. Empty panels contribute the
identity factor. Variables are the explicit original edge indices followed
by `none`, not the order of `FinEnum.toList (Option E)`.

This matches the product-and-reassembly structure of existing `fullRows`,
but **a formal carrier-transport and loop-refinement proof remains**: connect
each native ascending local Fin bijection to `SelectedCopy K_i`, connect the
iterative product to the existing recursive complement decomposition, and
instantiate its exact joined selected-view equation. The hand argument
identifies all maps and the representative congruence needed, but does not
claim that these Lean obligations are supplied by the canonical proposal.
After that join, reuse `fullRows_actual` with its exact population list and
ActiveIn premise; do not create a second biological epoch theorem.

## 6. Full-outcome obligations and evidence boundary

This packet provides a hand recurrence derivation and an unelaborated
canonical/zero-support proof proposal, not a finished solver. The next
source-level obligation is the explicit panel-carrier transport/iterative
reassembly refinement just stated, followed by actual whole-word transitions,
raw calendar/completion and authorized readout. Input graph/sample/registry
admission, shared physical bank, original target and both directions of
source/action coverage, AST/game correspondence, QE/history-relative selection,
and authenticated request/result still remain.

New native/Cargo/Lean/Lake/CI/QE and control execution remains held until the
original encrypted first-writer/controller binding is admitted. No such run,
new worker, installation, relay, credential action or canonical-profile change
occurred. The hand derivation must not be promoted to an end-to-end execution
certificate, and its proposed Lean source must not be described as checked.
