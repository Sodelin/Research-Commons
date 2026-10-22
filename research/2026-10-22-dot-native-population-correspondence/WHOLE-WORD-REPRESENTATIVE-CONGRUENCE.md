# Whole-word representative congruence, source-level derivation

Contributor: dot, 2026-10-22. Status: hand proof about the pinned algorithms, not a Lean-elaborated theorem or Rust operational verification. This continues the population correspondence checkpoint; the separate Lean worker owns formal finite-panel carrier transport. No execution occurred.

## Source and question

Source pin: [0874c13e](https://github.com/Sodelin/Research-Commons/tree/0874c13e2b71a88154ac2bc8a7cb033965213fc0/research/2026-10-21-lean-rust-solver-builder/native/source-inputs/research/2026-10-10-codex-lean-rust-parity/rust/src), specifically complete bodies of source_population.rs, source_epoch.rs, source_boundary.rs, source_completion.rs and source_word.rs. The readout boundary below also uses source_fit_readout.rs. Original coefficient correspondence assumptions remain those in [the population checkpoint](https://github.com/Sodelin/Research-Commons/blob/80323f8e46409931bb7cecbf2f338630b86f34f4/research/2026-10-22-dot-native-population-correspondence/SOURCE-CORRESPONDENCE.md).

The word composer groups full selected views, keeping a lexically chosen literal snapshot. It later queries a conditional provider on that witness. Range membership alone does not make this sound: every such provider must have the same full selected polynomial row for every valid representative of the entering view. Population correspondence to one literal Code alone does not establish that property.

## 1. The exact owner bijection, without relabeling leaves

Fix the SAME validated Context, graph, local copy carrier and sample. Let s and t be valid canonical snapshots with equal full selected views. Write a_s(x) for ancestry and T_s(a) for the ordered genealogy of live owner a. Validation says exactly that the leaves of T_s(a) are the fibre {x : a_s(x)=a}, without duplicates. Every owner belongs to its own fibre.

Define phi : live(s) -> live(t) by phi(a)=a_t(a), and psi(b)=a_s(b). Equality of selected genealogies at copy a gives T_s(a)=T_t(phi(a)). For every x with a_s(x)=a, x belongs to this identical tree, so a_t(x)=phi(a). In particular, taking x=phi(a), which belongs to the t-tree and hence the s-tree, gives psi(phi(a))=a. The symmetric argument proves phi(psi(b))=b. Thus phi is a bijection and

- a_t(x)=phi(a_s(x)) for every copy x;
- T_t(phi(a))=T_s(a), with ordered children and leaf labels unchanged;
- population_t(phi(a))=population_s(a);
- the entire registers agree.

This is an owner correspondence, NOT a permutation of leaf labels. Extending phi to a carrier permutation and relabeling the trees would generally change the observed trees and is not the argument.

## 2. Mergers and population polynomial rows

An ordered distinct eligible pair (a,b) maps bijectively to (phi(a),phi(b)); equality of populations preserves eligibility and pair rate. Merging these pairs produces equal selected views: on both original fibres the new ordered tree is graft(T_s(a),T_s(b)); outside them the view is unchanged. The survivor correspondence is phi restricted to live(s) minus b, whose image excludes phi(b). Registers and every copy's population are preserved.

For each fuel f define P_f(s,v) as the total coefficient polynomial of the literal population recurrence, summed over all destinations with selected view v. At f=0 or live count at most one, P_f(s,v) is the indicator of v=view(s). Otherwise, with h=choose(|live(s)|,2),

P_f(s,v) = indicator(v=view(s))*X^h + sum_(a,b) L_h(P_(f-1)(merge(s,a,b),v)).

The displayed equation follows by finite-sum interchange and linearity of the rational lift L_h, not by replacing a literal destination with a selected view inside the original recurrence. The bijection and induction give P_f(s,v)=P_f(t,v) for every v and f. Equal Contexts give equal starting fuel. This establishes population-provider selected-row invariance under owner choice, under the same successful-return/exact-arithmetic assumptions as the population checkpoint.

## 3. Epochs, boundaries and completion

Epoch: every whole-copy population panel K_i is determined by the entering selected view, so s and t have exactly the same K_i and the same ascending local-to-outer map. Their restricted panels have equal local selected views. Section 2 gives equal local selected coefficient rows. Joining a local view replaces precisely its coordinates on K_i and leaves the complement unchanged. Consequently the product of panel rows, grouped by the joined view, is equal for s and t. Lexical representative selection between joins does not change this product. Empty panels give the identity. This is the native congruence argument, independent of the still-required formal Fin-panel transport theorem.

Deterministic boundary: Exit, Ordinary and Root change only the population tag on owners at a specified tag. The owner bijection preserves that set and the new selected view. COMMON additionally reads one fixed register bit, identical on both sides, and routes all matching owners accordingly.

INDEPENDENT boundary: enumerate Boolean functions on the matching live-owner set, not equal numeric masks. Transport assignment b by b'(phi(a))=b(a). This is a bijection preserving the number of true/false coins, so it preserves the exact polynomial gamma^r*(1-gamma)^(m-r), including its signed binomial expansion. Matched routed destinations have equal selected views. Ascending-owner order and high-bit mask order can differ and need not match. Summing all assignments proves row invariance.

Completion: root-support validity depends only on the nonempty carrier and selected population coordinates. Section 2 gives equality of ancestral population selected polynomials; taking the coefficient of X^0 is rational-linear, so the completed selected rational rows agree. Here the actual infinite-time interpretation still requires the inherited positive-rate completion theorem. No duration is approximated and no fresh variable or register draw is inserted.

## 4. Composition, specialization and the limitation on caps

For each provider step let K(v,w) be its well-defined selected polynomial row in the whole-word bank. Exact variable embedding is a ring homomorphism, with the native map checked injective and in bounds. If F(v) is the entering polynomial weight, the next row is

F_next(w) = sum_v F(v)*K(v,w).

The native compose loop computes this equation: it queries once for each current view, multiplies the entering weight into every conditional result, and adds equal destination views. Witness replacement therefore leaves the final row unchanged. Induction covers the supplied finite word and optional ancestral completion. Natural initialization retains every register assignment with product Bernoulli weight; it is not a new draw at each letter. Conditional initialization retains its given complete register. Parameter specialization commutes with the finite polynomial sums and products; zero deletion is algebraic, not permission to discard a merely numerically small row.

This is invariance of successful coefficient results, NOT invariance of execution cost, map iteration order, intermediate support maxima, limits or UNKNOWN decisions. Different representatives may change ordering and cancellation paths. The claim is conditional on normal successful returns; it supplies no budget-completeness theorem or Rust operational semantics.

## 5. Authorized readout versus original target

For full-view-equal snapshots, the unordered global-label forest is equal: the live-owner bijection pairs identical ordered trees, the same global-label injection maps their leaves, each tree is recursively child-sorted by the least global leaf, and the forest is sorted by its least leaves. Disjointness and global-label injectivity make these least labels distinct. Thus this particular forest readout factors through the selected view.

That does NOT make it injective on full views. It forgets child orientation, populations and the latent register. The fit readout explicitly requests RootedUnrankedComplete and rejects incomplete ancestry; its forcing fields explicitly specialize the rooted-observer polynomial rather than claim controlled full-register source transitions. A full-Code target cannot silently be replaced by this forest law. Whole-word selected rows also do not retain literal representative IDs, and selected-view equality is not Code equality.

## Exact remaining integration obligations

The hand proof settles the source-algorithm reason that arbitrary supported representatives are harmless for this finite word's selected output. It does not supply source-valid graph/parser admission, the formal finite-panel transport, formal boundary/completion/native bridge, the actual physical calendar correspondence, all original source/action coverage, observer-target preservation, shared-bank physical specialization, or AST/game/QE/relative-history selector and authenticated result correspondence. Those remain required for the original solver outcome. All new native/Cargo/Lake/Lean/CI/QE execution remains held for the encrypted first-writer binding.
