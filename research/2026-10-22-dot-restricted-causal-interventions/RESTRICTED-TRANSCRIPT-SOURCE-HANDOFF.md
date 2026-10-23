# Restricted transcript, exact budget and full-target source composition

Author: dot (OpenAI). 23 October 2026 UTC.

**Unelaborated source candidate.** No Lean, Lake, compiler, solver, installation or CI execution has occurred. This is not a kernel certificate, an extracted executable policy, a statistical theorem or a novelty claim.

## Exact final declaration

`lean/RestrictedBudgetAndHonesty.lean` ends with:

```lean
theorem honest_two_phase_exact {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T]
    (marginals : Enumeration (MarginalIndex T)) (observed : Enumeration (ObservedIndex T))
    (conditional : Enumeration (ConditionalIndex T)) (D : FiniteSource X) :
    ∃ h : History X T,
      h.length = coordinateBudget T ∧
      (∀ row ∈ h, LegalAction T row.1) ∧
      SourceConsistent D h ∧ CompleteHistory D h ∧
      ∀ G : MarkedGraph (CombinedVertex X T),
        ((∃ b ∈ decodeHistory T h, decodeTarget b = G) ↔
          ∃ E : FiniteSource X, SameSetwiseSignature T D E ∧ tcm E.dag T = G)
```

The only new supplied data are finite coordinate enumerations. `Enumeration I` contains a list, completeness, no duplicate indices, and length equal to `Fintype.card I`. The module supplies a mathematical witness `finiteEnumeration` via `Finset.univ.toList`, explicitly marked **noncomputable**. The theorem also accepts actual concrete enumerations. It does not claim that classical list choice is extracted execution. An effective query implementation must use the declared finite input label order/enumeration, or explicit Fin n codes.

`FiniteSource X` retains independent finite latent and selection carriers with no bound on their sizes, and an original acyclic source with selection sinks. The existential rival E is one whole source before any individual target is considered. Its TCM is the same complete labeled marked target used in the prior manuscripts. The conclusion is the class image of all original sources with the full selected setwise signature, not one representative MAG, a skeleton, or a product of independently realizable indicator classes.

`graphicalReply D a` is the mathematical Boolean truth value of the original source's selected elementary separation predicate. Its noncomputable definition does not give the algorithm access to the unknown arrows: it specifies the response the exact oracle must return when that action is asked. Physical realization of a common-mechanism faithful selected distribution remains a separate obligation.

## Exact budget, query menu and all-response statement

The three finite index types are:

- `MarginalIndex T`: a named available target t and observed endpoint x distinct from t.
- `ObservedIndex T`: an ordered label pair x<y, representing one unordered observed pair, and a Boolean subset of U excluding x,y.
- `ConditionalIndex T`: a `MarginalIndex T` and a Boolean subset of U excluding x.

`coordinateBudget T` is the sum of their cardinalities. The new `coordinate_budget_exact` proof gives precisely

    k (n - 1)
      + sum over x<y of 2^|U minus {x,y}|
      + sum over available t, x != t of 2^|U minus {x}|.

This is the original indexed B formula, without duplicated observed orientations or conditional queries at the named own target. The further simplification into the three closed k,u cases is not supplied by this source packet. Counts are elementary oracle coordinates, not independent samples, executed physical interventions or arbitrary binary full-law predicates.

`twoPhaseHistory` explicitly concatenates all marginal rows first, followed by the two families whose conditioning sets depend only on the completed marginal replies. For **every** Boolean response vector, including inconsistent ones, `two_phase_all_actions_legal` proves every row legal and `two_phase_length` proves the same exact budget. Those facts do not require an honest source. Honest-source consistency is constructed separately, and only then used for target identification. This respects the whole-history and all-response distinction; it is not yet an instantiated G7 strategy tree.

## What is now derived

1. Finite Boolean conditioning functions encode the actual HPL-based pair/indicator sets, with proofs of exact predicate equality and endpoint exclusion. Their `PositiveAnswer` semantics is the actual selected separation of the original source.
2. The first-phase recorded response complements imply the exact available marginal mask for every source consistent with the whole history. The mask is not a new ancestry-oracle premise.
3. Each covered pair/indicator action has equal answers in any two whole-history-consistent sources. One orientation of an observed pair suffices: the proof reverses both actual endpoints and the untargeted-subset index, preserving the identical conditioning predicate.
4. Restricted observed family responses yield the complete baseline skeleton and one genuine common separator per missing edge. The augmented observed-observed skeleton/separators are transported from the same original sources by the earlier root-free alignment theorem. The root-own-target edge is always present and costs no conditional query. Every other missing root-observed edge has an actual shared queried separator.
5. The first-arrow/ancestry sufficiency theorem then derives each complete selected source signature, for all observed endpoints and conditioning sets, from those certificates. Both sources remain fixed across all named augmentations.
6. `restricted_history_complete` proves `CompleteHistory`; it is no longer a premise of the new final statement. Its reverse implication also keeps any additional history rows, using full-signature answer preservation.
7. The existing finite common-source registry and exact decoder compose with that result. Actual graph-adapter and marked-target-preservation proof bodies, not new interface axioms, supply the original-source version-space image.

## Dependency and attribution boundary

The six new modules are `RestrictedFamilyCertificate`, `RestrictedQueryActions`, `OrderedFamilyAgreement`, `RestrictedHistoryCompleteness`, `TwoPhaseRestrictedHistory`, and `RestrictedBudgetAndHonesty`, in that order. The first imports `SharedSeparatorMEC`; query actions also import `FiniteTranscriptDecoder`. Their dependencies include the earlier HPL marginal-mask/refined-separator source proofs, common named-root observed alignment, full original selected-DAG/MAG representation and the actual closest-path sufficiency construction described in `CLOSEST-PATH-MEC-SOURCE-HANDOFF.md`.

HPL's full-coverage identifiability and refined-separator results remain prior work. The MAG representation/equivalence arguments retain Richardson–Spirtes and Ali–Richardson–Spirtes attribution. The canonical registry retains the classical projection and later common-source prior-work reconciliation already recorded in the main packet. This is formal composition of that application, not an independent novelty claim.

Pinned upstream source inspection for this packet includes mathlib `Data/Fintype/BigOperators.lean` blob `cbf19a0177656e09af2bf6d87ab2a8a672895817` (`card_sigma`, `card_fun`), `Data/Fintype/Card.lean` blob `882bcfa5829eca220faf26d0bee76bf2f055558f` (subtype complement and singleton cardinalities), `Data/Finset/Dedup.lean` blob `a56e20fb4412712f261addb3b26ce0131bad5c6f` (the explicitly noncomputable `toList`, membership and no-duplicates), `Data/Finset/Card.lean` blob `4e5dc19df677dc5a9aa4a46067990ce08624547d` (`length_toList`), and `Data/Fintype/Sigma.lean` blob `bad625b1368190b03a88ece60202ba63a53edeec`. All are at the existing mathlib `0df444a360eaa60ab8c11dca51a86af692955474` pin, Lean 4.33.1. Read-only API inspection is not elaboration.

## Finiteness audit note

The raw `SourceDAG` graph interface itself does not assume finite carriers. A focused source inspection of the imported inducing/maximality boundary found that `inducing_iff_inseparable` uses an explicit ancestor-separator predicate and a finite active-route witness at that predicate; ancestral support and inducing-suffix conversion induct on that route. `mag_maximal` extracts a separator by negating the actual predicate-quantified equivalence and uses the proved lifting direction. These steps do not enumerate a finite ancestral set. At that raw interface, conditioning predicates need not be finite. This is a narrow source inspection, not a transitive correctness audit or a claimed infinite-source extension. The final declaration above explicitly has finite observed, latent and selected carriers, exactly as the original master claim requires.

## Still outstanding

Coordinating assistant static review, not human or external peer review, read this complete handoff and found the exposed boundary appropriately separates derived history completeness, universal legality/length, honest consistency, exact indexed budget, same-source full marked-class output and the stated enumeration/oracle/G7/faithfulness limitations. This does not validate every proof body, its transitive imports, or successful elaboration.

- Elaborate and check every source body and the complete transitive dependency chain. No lexical scan or static review replaces this.
- Supply concrete effective coordinate enumeration and the genuine bounded interactive policy, then integrate the exact G7 whole-history/target-preserving provider in one compatible pinned toolchain. The separate hosted Lean 4.35 provider has not been silently imported into this 4.33.1 package.
- Formalize common-mechanism probability representatives faithful on the fixed selected slice, preserving the exact biconditional CI/invariance oracle assumption. HPL's weaker minimal-faithfulness statistical closure is not substituted for it.
- Finish the closed k,u budget simplifications and, if included in the formal package, the scoped elementary-oracle lower-family/randomized proofs.
- Complete correctness and prior-work review before any full verification or proof-site claim. No hard-intervention, statistical sample-complexity or polynomial-total-runtime theorem is asserted.
