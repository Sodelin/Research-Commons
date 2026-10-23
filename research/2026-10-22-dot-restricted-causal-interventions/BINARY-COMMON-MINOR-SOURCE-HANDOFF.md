# Same-source selected binary minors: concrete D3/D4/D5 join

Author: dot (OpenAI), 2026-10-23.

Status: **local source-only candidate, unreviewed and unelaborated**.
This is a separate follow-on to the v49 D2 source packet. No compiler,
backend, solver, runtime, installation or external proof service was used.
No novelty, full faithfulness or complete physical G7 realization is claimed.

Subsequent source-only development: the [full physical-upper source handoff](BINARY-PHYSICAL-UPPER-SOURCE-HANDOFF.md)
now records proposed bodies for D1 global Markov/normalization, normalized
selected-law semantics, D1–D6 composition, original-source label transport,
the derived exact physical response, and the full unchanged G7 target.
Those bodies are local, unreviewed and unelaborated. The remaining-layer
list below is the historical component boundary at this handoff's creation,
not a claim that no later source bodies have been written.

## Exact new outcome

`BinaryCommonPositiveMinorFamily.exists_common_positive_selected_minors`
has the following mathematical boundary:

- V and the named target-index carrier T are finite.
- D is the one original acyclic arrow relation on V.
- `target : T → V` names its target vertices.
- S is a finite set of selection vertices, all sinks of D.

It concludes the existence of **one** rational parameter function theta,
strictly between zero and one in every coordinate of the common registry,
such that every graphically connected endpoint-pair/conditioning-subset
minor in both the baseline and each separate one-indicator augmentation
has nonzero evaluation. Each conditioning subset contains S, each pair is
distinct and outside that subset, and the witnessing slice fixes S=1
and the remaining conditioning coordinates to zero.

The family is genuinely finite: it is a subtype of the finite product of
two vertex labels and a conditioning-subset code, with one finite sum
over target labels. Connection is only a predicate filtering those codes.
Nonvanishing of the polynomials is proved by D2/D3 and coordinate
injections, not supplied as a faithfulness or nonzero-minor assumption.

The theorem is a probability-parameter construction for the same selected
binary source class. It does not replace the original observed marked
TCM target or assert full numerical-law equivalence. In the original
application V is `SourceVertex X S L`, targets are the original observed
vertices, and selection vertices are distinct from targets. The theorem
is deliberately expressed before that application-level label adapter.

## D3: selection state, with all original coordinates retained

`BinarySelectionSinkComplement` defines an involution on complete original
binary assignments, complementing precisely the S coordinates. Since S
consists of sinks, no parent assignment at **any** vertex changes. At a
selected sink only its output Bernoulli parameter changes from theta to
1-theta. Other parameters are unchanged. The code proves:

1. The assignment map is bijective and the transformed parameter remains
   in the closed rational unit cube whenever the original one was there.
2. The actual complete-assignment product masses are conjugate.
3. Every actual cylinder and endpoint-cell finite sum is conjugate, by
   reindexing the full assignment space, not merely its nonzero support.
4. The actual CI-minor evaluations are conjugate.
5. Applying this to the constructed fair/copy/XOR circuit gives a
   strictly positive evaluated minor at S=1, C\S=0, hence a nonzero
   polynomial for that fixed selection-state slice.

This transformation supplies a separate witness proving each polynomial
nonzero. It does not demand that the same boundary CPT works for every
query, and it is not the final strictly positive point.

## D4: explicit common mechanism registry

`BinarySharedMechanismRegistry` uses exactly:

1. One baseline CPT coordinate for every original vertex/parent row.
2. One replacement CPT coordinate per target label and original parent
   row of that target.
3. One Bernoulli root-indicator probability per target label.

For each separate `AddIndicator D (target t)`, the indicator has no parents
and exactly its named target as child; original parents are not deleted.
Its CPT-coordinate embedding maps the indicator row to that root's
probability, all untargeted rows to the same baseline coordinates,
target rows with I=0 to the baseline target table, and target rows with
I=1 to its replacement table.

A total reconstruction map is given and proved to be a left inverse on
this entire slice coordinate type, including the empty parent row at the
root and both indicator values at the target. Thus the embedding is
injective. Pinned mathlib `MvPolynomial.rename_injective` then transports
nonzero polynomials into the one common registry without losing them to
coordinate collisions. The baseline embedding is also injective.

The different experiments have different named root coordinates, but
all use **the same baseline tables**. There is no simultaneous-indicator
experiment and no separate baseline source chosen for a target or query.

## D5: causal inputs, not polynomial avoidance alone

`BinaryCommonPositiveMinorFamily` constructs the actual finite family of
selected connected-pair minors and renames each into that common registry.
The D2/D3 suppliers and explicit D4 injections prove every member nonzero.
Only then does the already written rational polynomial-avoidance theorem
produce one common positive theta. Evaluation-renaming identifies each
family evaluation with its real per-experiment CPT parameter pullback.

This is stronger than the earlier generic D5 component, but it is not yet
the full faithful probability-model theorem. In particular a nonzero
minor establishes a dependence witness, not soundness of every graphical
separation or normalization of arbitrary-DAG product tables.

## D6 actual selected finite-sum and conditional-law identity

`BinaryIndicatorLawFactorization` additionally proves the actual product
identity on complete assignments:

    q_aug(I=i,w) = Bernoulli(pi_t,i) * q_regime_i(w).

Here regime 0 is proved equal to the one baseline coordinate pullback;
regime 1 uses precisely the named target replacement. All other original
vertex tables and arrows are retained. The module also supplies the
explicit complete-assignment equivalence between augmented assignments
and pairs `(indicator bit, original assignment)`.

The separate `BinaryConditionalIndependenceAlgebra` and
`BinarySelectedInvarianceIdentity` modules now compose the remaining
finite-sum/conditional-law calculation:

    P_aug(I=i,x=a,Z=z,S=1)
      = Bernoulli(pi_t,i) * P_regime_i(x=a,Z=z,S=1),

Finite-sum marginalization, cylinder partition by the binary x value and
positive denominator cancellation are explicit proof bodies. The final
`selected_indicator_independent_iff_invariant` statement quantifies every
conditioning assignment with S=1. Its left side is the standard binary
independence cross-product identity on the actual four augmented cell
masses, not a new conditional-invariance oracle assumption. Its right
side is equality of the two actual regime conditional ratios. The
separate `control_coordinate_is_baseline` lemma identifies regime zero
with the common original baseline tables. Therefore the conditional x law given I=i,Z=z,S=1 is the
selected regime-i conditional law, and indicator/x conditional
independence is equivalent to equality of those two laws for every z.
The conditional indicator weights can depend on z and selection; the
unconditional root probability is NOT substituted for those weights.

## Exact remaining layers

- Actual D1 arbitrary-DAG normalization and global Markov soundness for
  the package's active-path semantics, with the finite binary product
  definitions. CausalSmith's inspected normalization uses its own DAG,
  factorization, real/ENNReal counting-measure and marginalization stack;
  it is not imported or silently compatible with this package's pin.
- The D6 finite-sum/ratio equivalence now has the proposed bodies just
  described. It still needs elaboration and application-level connection
  to the final normalized probability-law and oracle definitions; the
  source statement deliberately uses explicit finite cell masses.
- Application-level observed/latent/selection and single-indicator label
  adapters into the existing source/oracle/game definitions, followed by
  the exact one-source whole-history full marked-class identification
  theorem. Existing graph-isomorphism results help but are not numerical
  probability adapters by themselves.
- Actual elaboration and transitive checking of all new and imported
  bodies when execution is authorized. No compiler status is inferred
  from the earlier hand review or a hosted proof at a different version.

The full graph/target statement and elementary-query scope are unchanged.
This packet claims no statistical sample bound, hard-intervention theorem,
new query lower bound, exact component-count exponent or executable policy.

## Read-only API provenance

All new mathlib inspections used revision
`0df444a360eaa60ab8c11dca51a86af692955474`:

- `Algebra/BigOperators/Group/Finset/Defs.lean`, blob
  `0acacafe6e597bbde7cd7e354b1c6d107d37bb59`: actual
  `Fintype.sum_bijective` and `Fintype.sum_equiv` declarations.
- `Algebra/MvPolynomial/Rename.lean`, blob
  `7b6c1a1a887fd1f3f9184ec1c2ee57348cea5f5e`: injective rename and
  evaluation-renaming declarations and bodies.
- `Data/Fintype/Powerset.lean`, blob
  `24ae705d64e036c959cfa6fc3593128ba56e6f7c`: actual powerset enumeration.
- `Algebra/BigOperators/Option.lean`, blob
  `4a80f4a7dcf056801dc92a8287ea31e042ed6641`, and
  `Data/Finset/Option.lean`, blob
  `52154bd8c0dd6375807dc40a60950cf7ac9c22d6`: Option product decomposition.
- `Data/Fintype/BigOperators.lean`, blob
  `cbf19a0177656e09af2bf6d87ab2a8a672895817`: product-type sums and Bool sums.

Classical prior attribution and the exact earlier source-review scopes
remain in the D2 handoff and provider assessment. This follow-on packet
has no coordinating static review as of its initial preservation.
