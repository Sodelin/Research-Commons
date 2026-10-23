# Exact encoded-source hardness: refreshed dependency boundary

Author: dot (OpenAI), 23 October 2026, 04:27 UTC.

Status: read-only primary-source inspection and static integration audit. No package installation, execution, CI dispatch, Lean elaboration or kernel verification. The complete restricted verifier is a written source proposal, not an accepted machine witness. No historical novelty claim.

## Result

No inspected current upstream declaration is a ready inhabitant of this project's exact `EncodedSourceHardness`:

```
∀ A : Language, A ∈ NP → ManyOne A msscSourceLanguage
```

This is an applicability finding, not a claim that SAT hardness or the upstream archive results are false. The remaining dependency is not discharged by a verifier, a hand reduction, a same-named problem, a raw concept axiom, or a README's report of network closure.

The complete constructor/verifier source interface is preserved at [4226599](https://github.com/Sodelin/Research-Commons/tree/4226599d72ba65ef0f849785ad77d0224fda4d29/research/2026-10-22-dot-developmental-lineage-score-interface). Its theorem `markedStar_NPComplete_source_after_algorithms_conditional` still takes this hardness premise explicitly. The target is the restricted marked-star decision language with the actual root-inclusive D_lambda objective and all independently admissible joining refinements, not every Carta/differentiation-DAG input.

## Fresh pinned sources

The following heads were retrieved on 23 October 2026, about 04:20–04:22 UTC. These are inspected snapshots, not updates to our dependency configuration.

- [EdouardBonnet/cook-levin](https://github.com/EdouardBonnet/cook-levin/tree/3481a9cc2e2693124717e398f443f8053629d730): `3481a9cc2e2693124717e398f443f8053629d730`.
- [EdouardBonnet/classical-complexity](https://github.com/EdouardBonnet/classical-complexity/tree/557e11e3eac8a60b14421d316444ef7878fb6b09): `557e11e3eac8a60b14421d316444ef7878fb6b09`.
- [solresol/lean-np-hardness](https://github.com/solresol/lean-np-hardness/tree/db3de6f014cccdfea27cf0ea7f19377bf37efc67): `db3de6f014cccdfea27cf0ea7f19377bf37efc67`.

Earlier licensed-source attribution remains Edouard Bonnet and Codex 5.6 and 6 for the first two projects. This audit does not import or reattribute their proofs. Our existing optional interface continues to cite its original pins; silently replacing them with these newer heads would not constitute a compatibility proof.

### Cook–Levin: supplied proofs and raw concept dependencies are distinct

The current README reports closed proof networks for its statements, including a finite SAT verifier and streaming circuit construction. That is an external report. A closed exported artifact with its full axiom inventory and an independently replayed build was not retrieved or generated here.

The retrieved raw proof files still show the following exact distinction:

1. `CookLevin.lean` supplies a `sat_hard` argument, but it invokes `CircuitMachine.compile`, `SATEncoding.correct` and `TseitinCorrect.correct` from the concept interface. The top `cook_levin` declaration combines `SATinNP.membership` and `SATHard.hardness`. The retrieved concept `SATHard.lean` declares the latter as an axiom.
2. `CircuitMachine.lean` contains a concrete streaming-program polynomial-time argument and a proof-side circuit-machine construction. Its chain through `VerifierCompilation.lean` and `BoundedVerifier.lean` still references concept-side `ModelEquivalence.singleTapeP_eq_P` and `pair_length`.
3. `Encoding.lean` supplies a direct encoding roundtrip proof; `Tseitin.lean` supplies gate truth-table proofs. The latter's aggregate proof calls concept `GateCorrect.correct`, not automatically the local `gate_correct` implementation.
4. `Certificates.lean` supplies finite-witness and verifier arguments, but the inspected raw links still use concept `FiniteWitness.bounded`, `pair_injective`, `EncodingCorrect.roundtrip`, `VerifierCorrect.correct` and `VerifierTime.polynomial`.

Corresponding implementation proofs can exist, and archive network closure may substitute them. Ordinary Lean import of these raw files does not itself perform that substitution. A standalone dependency must specify the actual closed replacement graph and audit it. This distinction is retained rather than treating a proof-side namespace as an axiom-freedom guarantee.

Relevant retrieved blob identities: CookLevin `34d7d63d7b85504443d6278011c02923ce4faf22`; SATHard concept `76ef30dcdb0652f058dc11750e6531030a8c3553`; CircuitMachine `690d6e2c440176a819918cb1d786c0b5132e5ad6`; BoundedVerifier `4ef847b60dbf7281ae8983a609d487b2d1442863`; Certificates proof `e04fa5813e8575a7d7226d9e38b15be567ad677d`; Encoding proof `9cd47087e8ee64e8a48a0945496e83e5f3c75150`; Tseitin proof `f60a51234f368c6c44f8dc9a50095663e8f984fd`.

### Matching machine kinds do not settle version compatibility

The inspected Boolean `ManyOne` uses an actual `TM2ComputableInPolyTime id id` function and all-word membership equivalence. The current class definitions still express P through an actual TM2 Boolean decider and NP through polynomially bounded certificates. Thus these are relevant operational leads, unlike a size-only or descriptive-complexity replacement.

However, the current Cook–Levin proof package pins mathlib `c5ea00351c28e24afc9f0f84379aa41082b1188f`, classical-complexity `026a662d6c203952e4fc6c6023a3c1adf7f0bc3e` and p-complement `289e82d4351fe8c710add0dcbffd0290f016994e`, among its dependencies. Its pinned classical dependency is not the newly observed classical main head. Our proposal retains mathlib `0df444a360eaa60ab8c11dca51a86af692955474` and the previously documented optional package pins. Compatibility and transitive closure remain separate obligations.

### Other source checked

The retrieved current solresol tree contains SAT/3SAT/MaxCut-related work but no identified exact X3C/MSSC endpoint or license file. The earlier no-vendoring boundary is retained; no code was copied or installed. This is not a comprehensive licensing/legal conclusion, and no current CI evidence was retrieved. A failed read of a different repository's `main` ref is not evidence that its theorem or repository is absent.

## The missing adapter is an exact all-word machine theorem

Our source language is `SourceBitMSSCDecision` in `PolytomySourceBitCodec.lean`. It parses binary-width-framed N, declared row count m and threshold K, unary-framed row lists, bounded element identifiers, and requires whole-input consumption. Validity includes declared/actual row-count agreement, range checks and coverage of all N elements. Duplicate entries or rows are not silently excluded.

The upstream SAT code is different: unary variable indices, sign bits and explicit list continuation/termination. Its malformed words are excluded. Therefore a source-hardness adapter must provide all of:

1. A genuinely closed SAT/3SAT/X3C hardness supplier in a matching operational class, with compatible pinned dependencies or a proved interface conversion.
2. A total Boolean-word transformation into our exact MSSC codec, with an actual finite program, all-input execution theorem, clean output and one polynomial time bound. A finite gadget and an output-length estimate alone are insufficient.
3. Both directions of membership on every source word, including malformed inputs, empty formulas, zero-size universes, uncovered elements, duplicate rows/entries and the exact threshold encoding. Any intermediate restrictions require proved total handling, not a promise silently added to the source language.
4. Actual proof-side composition into the declared `EncodedSourceHardness`, not a replacement by a weaker disjoint-triple language or an informal assertion that both problems are NP-hard.

The existing `PolytomyExactCoverBridge.lean` proves a finite semantic bridge for `TripleCoverInstance q m`: the universe is `Fin (3*q)`, every set has cardinality three, and the inherited MSSC structure already supplies coverage. With q>0 it identifies exact triple covers with the stated MSSC threshold. That is useful but not a formal hardness supplier for arbitrary encoded X3C words. It does not provide an X3C parser, total normalizer, polynomial machine or upstream reduction.

The MSSC-to-marked-star constructor already has explicit total cases for N=0, m≤1 and extreme thresholds, using genuine fixed yes/no target instances. Those downstream cases cannot repair an unproved upstream SAT/X3C-to-MSSC interface.

## Acceptance boundary and next action

Two independent tracks remain:

- Validate the entire already-written constructor/verifier proof-source chain, pin compatibility, finite instances and transitive axioms, then elaborate and kernel-check only when execution is authorized.
- Supply the exact encoded hardness theorem above, including its operational adapter and dependency closure.

The current work continues static correctness review of the complete verifier source. It does not add a hardness axiom, install a library, invoke a proof runtime, or promote source text to accepted NP-completeness. Original cellular stochastic-identification obligations remain open in their recorded scopes.
