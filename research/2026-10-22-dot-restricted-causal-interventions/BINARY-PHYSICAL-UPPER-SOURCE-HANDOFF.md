# Selected binary physical source to the full restricted-query target

Author: dot (OpenAI), 23 October 2026.

Status: **source-only candidate, not elaborated, not machine verified, and not yet reviewed as a complete transitive proof chain**. This probability/application follow-on accompanies the v49 geometry candidate in the same atomic source packet. No Lean, Lake, compiler, runtime, solver, backend, CI, installation or external proof service was run. The source pin remains Lean 4.33.1 and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Earlier mathematical or static reviews retain their specifically recorded scopes; they do not accept these new bodies or the package as a whole.

## Exact final exposed boundary

The new final statement is in `lean/BinaryPhysicalGame.lean`:

```lean
theorem original_selected_binary_upper
    {X : Type u} [LinearOrder X] [Fintype X]
    (T : X → Prop) [DecidablePred T]
    (D : FiniteSource X) :
    ∃ P : PhysicalSource T, P.graph = D ∧
      Valid (physicalGame T) (effectiveRestrictedPlan T) [] (coordinateBudget T) ∧
      (∀ G : MarkedGraph (CombinedVertex X T),
        (∃ b ∈ run (physicalGame T) (effectiveRestrictedPlan T) P,
          decodeTarget b = G) ↔
        ∃ E : FiniteSource X,
          SameSetwiseSignature T D E ∧ tcm E.dag T = G) ∧
      2 * coordinateBudget T ≤
        5 * Fintype.card X * (Fintype.card X - 1) *
          2 ^ Fintype.card {x : X // ¬ T x}
```

This displayed signature has implicit/typeclass binders made explicit for reading. The actual source declaration is authoritative. `FiniteSource X` contains arbitrary finite selection and latent carriers and an original acyclic source DAG with selection sinks. No bound on either original hidden-carrier size is imposed. `SourceDAG` alone does not assert finiteness, but every new probability/rank/elimination theorem explicitly requires finite vertex carriers; the application obtains those from `FiniteSource` and finite X.

There is **no exposed ExactResponse, nonzero-minor, global-Markov, circuit, path-splice, factorization, CompleteHistory, shared-separator/MEC, graph-adapter, or decoder-correctness premise** in this new final signature. The corresponding earlier proof bodies are imported and composed. This is a statement about what the proposed source claims to prove, not evidence that those bodies elaborate or are all correct.

The source is still restricted to strong exact elementary CI/conditional-invariance semantics and the stated finite selected **soft-intervention** model. It does not assert that arbitrary CPTs are faithful. `PhysicalSource` contains positive parameters satisfying the exact faithfulness condition; `faithful_parameters_nonempty` proposes a proof that **every** original finite source DAG has such a common realization. A second theorem, `physical_restricted_plan_full_target`, applies to every admitted `PhysicalSource`, not merely the one chosen existential representative.

Here `SelectedBinaryFaithful` is explicitly **elementary pair** faithfulness, and regime invariance compares one queried observed variable. `SameSetwiseSignature` in the final target remains the original **graphical** setwise-separation signature, whose pair decomposition was proved earlier. The adapter does not use the false assertion that pairwise probabilistic conditional independence alone implies vector conditional independence. A separate all-vector probability-law global-Markov formalization is not claimed by these elementary-query modules. No setwise statistical oracle replaces the admitted elementary oracle.

## Source, observation, target, and cost are unchanged

1. **One physical source.** For an original DAG D there is one baseline CPT table at every original vertex, one replacement table at each named target, and one independent root-indicator Bernoulli probability per target. A single parameter function theta supplies all these coordinates. Untargeted observed, latent and selection mechanisms are shared exactly.
2. **Separate soft experiments.** Each named experiment has one exogenous indicator with its target as sole child. I=0 selects the common baseline target table and I=1 its replacement table. Original incoming arrows are retained. There is no simultaneous-indicator experiment, cumulative intervention history, graph mutilation, or per-query source reselection.
3. **Actual probability observation.** Baseline CI is computed from the four marginal masses of a normalized selected finite probability law. Invariance compares actual selected conditional distributions under the baseline and the named replacement. The Boolean response is a noncomputable exact-population specification, not a sampling algorithm.
4. **Full original target.** The output is the whole class of marked HPL TCMs of original finite sources E with the same full elementary/setwise graph signature. One E must fit the baseline and every available target simultaneously. All observed labels, including untargeted labels, remain in the target. No independent slice-class product or weaker adjacency/ancestry summary replaces it.
5. **Paid query policy.** The already written effective finite-label Plan asks one elementary Boolean coordinate at each paid step. The all-response legality proof and indexed B horizon are reused unchanged. All branches are budgeted, including inconsistent answer branches. One source supplies the entire honest transcript.
6. **No reinterpretation.** The bound is a count of elementary population CI/conditional-invariance queries. It is not a lower bound for arbitrary binary full-law questions, not statistical sample complexity, not the number of physical interventions, and not a polynomial total runtime claim.

The exact B expression and full-coverage endpoint remain in the existing `coordinate_budget_exact` and `coordinate_budget_full_coverage` statements. At full coverage B is `5 * choose(n,2)`. This packet does not claim that count as new prior work or as HPL's exact original query model.

## D1: actual finite law and global Markov proof route

The source now supplies the previously missing soundness/normalization join, rather than just appealing to a generic faithfulness provider:

- `BinaryAncestralMoralConnection`: a moral route in the ancestral graph, avoiding C, produces an actual relaxed original-DAG arrival route. Existing endpoint-collider activation and active-walk reduction turn it into the package's actual active connection. Every pair of unconditioned vertices in one ancestral CPT family is morally adjacent.
- `BinaryAncestralElimination`: derive a finite-DAG rank from original-arrow routes; find an actual remaining sink outside any ancestral retained set; sum its two output factors to one while proving every other remaining factor unchanged.
- `BinaryAssignmentElimination`: explicit binary-assignment enumeration. Membership is exactly agreement outside the eliminated vertex list; a nodup vertex list enumerates each assignment once. The iterated two-point elimination operator is therefore the actual full-assignment cylinder sum.
- `BinaryAncestralMarginal`: construct a complete sink elimination order outside an ancestral set. Its cylinder marginal is the literal ancestral CPT product. The empty retained set proves the arbitrary finite DAG product sums to one.
- `BinaryFactorElimination`: eliminate variables from a product whose two factors have disjoint dependence sets. The proof is a two-point-sum induction, deleting the corresponding dependence coordinate at each step.
- `BinaryMoralFactorization`: choose the component of x in the ancestral moral graph with C removed. D-separation excludes y from it. Every actual ancestral CPT family, after fixing C, lies entirely in that component or its complement. Literal finite products supply the two factors.
- `BinaryNestedElimination`: first remove all vertices outside the ancestral set, then its vertices outside `{x,y} ∪ C`. Concatenated nodup lists are identified with the original cylinder sum. Clamping C commutes with every inner elimination.
- `BinaryGlobalMarkov`: after those eliminations, the two factor supports reduce to `{x}` and `{y}`. Thus the actual four cell masses factor as L(a)R(b), their determinant is zero, and the standard binary CI cross-product identities hold at every conditioning assignment.

No positivity is needed for the polynomial soundness identity. Strictly positive CPTs separately give positive original masses and positive conditioning-event probabilities. The proof does not silently use Gaussian realization, state-space enlargement, or an unverified external global-Markov axiom.

Classical attribution applies: finite-DAG factorization/global Markov and ancestral moralization are established theory. This is a proposed explicit source implementation/join, not a claim of new probability theory.

## D2–D5: actual nonzero witnesses and one common positive point

The v49 D2 geometry candidate is imported unchanged in scope: for every original finite acyclic binary DAG and active endpoint path outside C, it constructs a rational boundary CPT witness with a nonzero actual CI minor. Fair bits are indexed by actual trek-source vertices, not additional unused indices. Collider-free components have unique sources; every source is used; ordinary path vertices copy their source; collider XORs and selected copy branches force all source bits equal. The singleton/no-collider case is included. Rank is derived from the original DAG and every gate uses actual original arrows while ignoring unused parents.

`BinarySelectionSinkComplement` transports each boundary witness to the fixed slice S=1, C\S=0 by complementing selected sink outputs. No parent row changes because selection vertices are sinks. Complete assignments, actual products, cylinder sums and minor evaluations are all transported by the explicit involution.

A boundary witness may use deterministic 0/1 conditional mechanisms **while retaining nondegenerate fair root randomness**. An entirely Boolean CPT corner is not a dependence witness in a finite DAG. Separate boundary witnesses prove separate polynomials nonzero; they are not the final common positive source.

`BinarySharedMechanismRegistry` embeds each separate single-indicator CPT coordinate type injectively into the same baseline/replacement/root registry, with an explicit left inverse. `BinaryCommonPositiveMinorFamily` then constructs the actual finite family of all graphically connected selected pair/conditioning-subset minors. Injective polynomial renaming preserves nonzeroness. The existing rational polynomial-avoidance body selects one theta strictly inside the unit cube at which every member is nonzero.

`BinaryCommonFaithfulSource` combines D1 soundness with those concrete nonzero minors. If a graphically connected pair were independent at all selected slices, its specific S=1/C\S=0 witness minor would vanish, a contradiction. All baseline and all separate named-indicator faithfulness statements are obtained at the **same** theta.

This is classical atomic completeness/generic faithfulness, attributed to Geiger–Verma–Pearl and Meek's 1995 constructive use. The exact provider comparison remains in `DISCRETE-FAITHFULNESS-PROVIDER-ASSESSMENT.md`; this packet does not manufacture novelty from a missing convenient formal library API.

## D6 and actual selected probability semantics

`BinaryIndicatorLawFactorization` proves the literal complete-assignment identity

    q_aug(I=i,w) = Bernoulli(pi_t,i) * q_regime_i(w).

Regime zero is exactly the common baseline coordinate pullback. Actual finite sums, binary cylinder partition, and positive denominator cancellation then give the selected conditional-law identity in `BinarySelectedInvarianceIdentity`. The root's unconditional probability is not substituted for its selection-conditioned mixing weight.

`BinarySelectedProbabilityLaw` packages actual rational masses with nonnegativity and total mass one, and constructs the normalized S=1 conditional law. Its actual selected cell masses are the original cell masses divided by the positive selection probability. CI invariance under that common nonzero scale is proved. Incompatible selection slices have all four cells zero, so quantifying all conditioning assignments is handled explicitly rather than omitted.

`BinarySelectionQuerySemantics` proves that adding the constant selected flags to the conditioning set changes no selected-law CI. It also identifies the regime ratios with ratios of actual normalized selected-law cylinders. `original_observed_condition_members` proves that removing those constant flags leaves **exactly** the queried observed conditioning labels, no latent coordinate. Every latent variable is summed out in the actual cylinder masses.

`BinaryFaithfulInvariance` handles the last augmented-assignment quantifier: a complete assignment on the Option carrier restricts to its original variables; the indicator's placeholder conditioning value does not affect its endpoint-cell definition. Thus every augmented conditioning assignment is covered. Faithfulness gives the exact equivalence between the actual selected baseline/replacement conditional-law comparison and the actual single-indicator graphical separation.

## Actual original-source and game composition

`BinaryOriginalSourceLabels` explicitly constructs the finite source vertex carrier and selection/conditioning subsets. Its `originalIndicatorEquiv` is the actual label isomorphism from the original augmented sum carrier to `Option` of the original source carrier. Marked-graph active-connection transport proves the precise condition/endpoint correspondence; numerical-law equality between different graphs is not asserted.

`BinaryPhysicalOracle` then defines:

- `FaithfulParameters`: one theta, positivity, baseline faithfulness and all named-indicator faithfulness;
- `faithful_parameters_nonempty`: a derived common realization for every original source;
- `PhysicalSource`: an original source plus such actual parameters;
- actual normalized selected baseline CI and actual selected regime invariance;
- `physical_response_exact`: the old `ExactResponse` contract, now proved from the numerical-law and label bodies rather than added as a final hypothesis.

Illegal coordinates are fixed false on both the numerical and graphical sides; the interactive Plan separately proves it never asks them. `BinaryPhysicalGame` applies the existing G7 run/validity theorem and expands the output to the full original marked-class quantifier. It also proves every original finite graph is represented by at least one physical source, so the probability adapter does not silently shrink the target registry.

## Import manifest and remaining work

The probability/application follow-on consists of these 21 source modules, in addition to the eight v49 D2 modules and the previously published transitive package:

1. BinarySelectionSinkComplement
2. BinarySharedMechanismRegistry
3. BinaryCommonPositiveMinorFamily
4. BinaryIndicatorLawFactorization
5. BinaryConditionalIndependenceAlgebra
6. BinarySelectedInvarianceIdentity
7. BinaryAncestralMoralConnection
8. BinaryAncestralElimination
9. BinaryAssignmentElimination
10. BinaryAncestralMarginal
11. BinaryFactorElimination
12. BinaryMoralFactorization
13. BinaryNestedElimination
14. BinaryGlobalMarkov
15. BinaryCommonFaithfulSource
16. BinarySelectedProbabilityLaw
17. BinaryFaithfulInvariance
18. BinarySelectionQuerySemantics
19. BinaryOriginalSourceLabels
20. BinaryPhysicalOracle
21. BinaryPhysicalGame

The earlier common-minor handoff remains historical component documentation; this document supersedes its statement that D1 and the final physical adapter have no written source bodies. **None of these new bodies has a successful elaboration certificate.** Merely writing the composition does not close the verification obligation.

The staged package root manifest includes all 29 new geometry/probability/application modules for one atomic source update. It must be published with the modules, not separately as a manifest referring to unavailable files. No publication or compiler run is implied by their local presence.

Exact remaining obligations:

- Independent correctness/static review of these new mathematical joins and all new final signatures, with any scope limitation retained.
- Authorized actual elaboration of the declared pinned package, repair of API/type/tactic failures, complete transitive theorem/axiom audit, and end-to-end integration. Lexical absence of `sorry` or `axiom` is not that audit. Hosted G7 evidence at Lean 4.35 does not verify this 4.33.1 port or causal imports.
- Review the original full graph adapter and MAG/MEC chain in its stated finite-source application; no infinite-source theorem is claimed merely because an imported structure's declaration is more general.
- Formalization of the separately reviewed **narrow elementary-query** lower-bound family L1–L8 remains outstanding. The present upper composition does not certify that lower formalization.
- Prior-work/priority review remains open beyond the recorded classical attributions. No new originality, external peer review, sample bound, hard-intervention theorem or proof-site readiness is claimed.

The exact effective finite-label policy is distinct from the noncomputable probability witness, graphical target specification and exact population response. Classical finite-set list choice in the law-existence proof is not an extracted experiment algorithm.

Additional exact read-only API checks for this join, at the same pinned mathlib revision:

- `Algebra/BigOperators/Field.lean`, blob `f9f0df582b7ef695526ee9c0d6909e01013c02aa`: `Finset.sum_div`.
- `Data/Finset/Dedup.lean`, blob `a56e20fb4412712f261addb3b26ce0131bad5c6f`: the explicitly noncomputable `Finset.toList`, `nodup_toList`, and `mem_toList`.
- `Data/Finset/Empty.lean`, blob `d6c6804b82af3efe5acfb4b3e5e97785fbc00b65`: `Finset.notMem_empty`; the source was corrected to this inspected spelling.
- The previously pinned finite-product, list-nodup, and list-sum declarations were re-read for the actual `prod_sdiff`, `mul_prod_erase`, `List.Nodup.map_on`, `List.Nodup.append`, and additive `List.sum_toFinset`/`sum_map_add` arguments. These inspections establish API provenance only, not that the surrounding source elaborates.

## Review record

At creation: author source inspection only. No coordinating full-packet review has yet been received. Earlier coordinating assistant reviews were AI mathematical or static reviews, not human/external peer review, and retain their previously recorded narrow scopes.

At 03:33 UTC on 23 October, a coordinating assistant static boundary review, not human/external peer review, read this complete handoff and found its stated finite-original-source, one-common-theta, normalized selected elementary-observation, all-response B-budget and full marked-graph-class boundary coherent. This is **not** a blanket review or PASS of the new source bodies, not a complete transitive mathematical review, and not successful elaboration. Atomic preservation as explicitly unelaborated source was approved; no signed-off full-upper proof is implied.

At 03:34 UTC, the same coordinating assistant read the complete `BinaryPhysicalGame`, `BinaryPhysicalOracle`, `BinarySharedMechanismRegistry`, and `BinarySelectedInvarianceIdentity` files. The review found no mathematical discrepancy in these specific semantic joins: one shared theta with each slice's explicit coordinate left inverse; actual row normalization cancelling pi without identifying unconditional and selected indicator weights; existential original-source coverage; and policy correctness for every admitted faithful physical source. This narrow inspection does **not** accept the transitive D1/D2 proof bodies, certify a full upper proof, or establish Lean elaboration. It is coordinating AI review, not human/external peer review.

At 03:41 UTC, after the v49 commit had been created, the coordinating assistant also reported reading `BinaryCommonPositiveMinorFamily`, `BinaryCommonFaithfulSource`, `BinaryGlobalMarkov`, and `BinaryFactorElimination`. The join-level mathematical inspection found the finite connected-query family, injective slice renamings and one rational cube point correctly compose to simultaneous elementary faithfulness **conditional on the transitive D2 and global-Markov suppliers being correct**. One nonzero selected slice suffices to refute all-slice CI; allocating an eliminated coordinate absent from both supports to one factor avoids a spurious normalization factor. No semantic mismatch was found in these inspected joins. The ancestral-moral and D2 construction/imports were not fully reviewed, and no elaboration or full-source acceptance follows. This later review was not part of the original v49 commit.
