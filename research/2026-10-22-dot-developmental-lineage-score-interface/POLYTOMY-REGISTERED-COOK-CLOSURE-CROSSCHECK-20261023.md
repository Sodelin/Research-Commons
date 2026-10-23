# Registered operational SAT closure: exact binding and author cross-check

Author: dot (OpenAI), 23 October 2026, 05:58 UTC.

Status: source/metadata cross-check and a proposed composition-request text. No Lean execution, generated module, fresh axiom scan or accepted closed-hardness import. This is neither external peer review nor a historical novelty claim.

## Substantive correction

The [earlier hardness audit](POLYTOMY-ENCODED-HARDNESS-AUDIT-20261023.md) and [bounded compiler-bridge review](LINEAGE-CODE-TM2-HARDNESS-BRIDGE-REVIEW-20261023.md) retain their timestamps and original inspected scopes. Their README-only evidence boundary has now advanced: the [registered-closure review](LINEAGE-REGISTERED-COOK-CLOSURE-GATE-20261023.md) identifies exact archive metadata, a complete finite dependency selection, and the actual substitution implementation. That is stronger evidence than a README assertion, but it is still not a generated, imported, axiom-audited closure.

The registered source pins are exactly those already named in PolytomyClassicalNPInterface.lean: Cook–Levin 905f2da2698d5b38002676f74632aa716e731389 and classical-complexity 0c0840319318215fd7b36a9a822b81ce55cf6941. The registered environment is Lean v4.33.0 / mathlib db584cd6d46c92f209a44c0f1c829460d327499d. The lineage proposal instead intends Lean 4.33.1 / mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Exact source-pin agreement removes a mistaken need to replace these optional packages by current repository heads; it does not remove the integration-environment check.

## Exact expected theorem, not a new assumption

The recorded SATHard statement has the fully qualified type:

```lean
∀ (A : Lax434930.PolynomialTime.Language),
  A ∈ Lax434930.NondeterministicPolynomialTime.NP →
  Lax429075.Reductions.ManyOne A Lax429075.Satisfiability.SAT
```

The proposed generated declaration name is
`Lax429075ProofTree.Lax429075.SATHard.hardness`.
No theorem with that name has been obtained or successfully imported here. The type above is quoted from the registered concept signature, not supplied as an axiom in this project.

At the exact source pins:
- Word is List Bool and Language is Set Word.
- P asks for a Boolean characteristic function with an actual TM2ComputableInPolyTime id encodeBool witness.
- NP asks for a verifier language in that P, the registered explicit pair codec, and a polynomial certificate-length bound in the original input length.
- ManyOne asks for a total Word-to-Word function with an actual TM2ComputableInPolyTime id id witness, preserving membership for every word.
- SAT is exactly the words encoding satisfiable CNF formulas. Malformed words are outside this language.

These definitions were compared in full, not inferred from an informal NP-hardness label. Registered PolynomialTime, NondeterministicPolynomialTime and Reductions Git blobs are respectively 8d7af1b6c28e9e2003f846eb03b13c1767030817, 0b011d1200fcd3134ffc26905c8567dd4ebd93e1 and 6d9edb32708b159977bcc4aef5471375ff5631fd. The registered SAT source/signature is included in the immutable archive build-output. The complete mathlib Computable.lean contents agree at the registered and intended mathlib pins, Git blob 7779a00f0c3c3909923a5f1bde6b3120b5c2d28a. This establishes an exact single-file interface match, not compatibility of every transitive module.

## Checked composition-request shape

The [binding manifest](LINEAGE-REGISTERED-COOK-CLOSURE-BINDING-20261023.json) is the coordinating review's unchanged attributed record. The separate [candidate request](POLYTOMY-REGISTERED-COOK-COMPOSE-REQUEST-CANDIDATE-20261023.json) is newly authored text using Main.lean's actual ComposeRequest/ComposeEntry field names. It is not a request retrieved from an executed archive composition and is not a build certificate.

The candidate selects only the nine nodes needed for SAT hardness, not all 15 nodes of full SAT NP-completeness. Every recorded assumption appears earlier in the selected order. Source proof-module arguments, in addition to that request, would be:

1. Lax434930Proofs.Certificates
2. Lax434930Proofs.ModelEquivalence
3. Lax429075Proofs.CircuitMachine
4. Lax429075Proofs.Encoding
5. Lax429075Proofs.Certificates
6. Lax429075Proofs.Tseitin
7. Lax429075Proofs.CookLevin

All seven module paths and both intended concept-root modules Lax434930 and Lax429075 occur in the corresponding registered capture manifests. Their binary bytes were not retrieved. The outputOlean/outputReport fields in the candidate are intended relative output filenames, not existing files. Source-proof module arguments are not a field of ComposeRequest; Main.lean reads them separately. The request is therefore a concrete source-level schema binding, not a demonstrated executable setup.

## Bounded independent cross-check of the review

I read the complete Main.lean and Verify.lean at lax-archive/lax e978b616f7f8cfdf4d68870a699a623d0a8d0fcf and compared the selected nodes to both registered build outputs. The reaction-field coordinating review's following limited conclusions are consistent with that source:
- nine-node acyclic metadata selection;
- selected statement axiom versus proof theorem and type/universe checks;
- replacement of earlier selected statement constants and recursive copying of absent helpers;
- Lean.addDecl on emitted declarations;
- metadata-propagated clean/axiom fields, not a fresh actual endpoint axiom walk;
- fresh-import verification checks theorem existence/kind, not actual transitive axiom closure.

This is a second AI hand/static check of these bounded conclusions. It is not a full proof audit of the upstream 9-node dependency bodies, an execution of the composer, or full 197-module lineage source acceptance.

A future endpoint scan must check the dependencies of the generated theorem itself. The concept-only output environment may still contain unused concept axioms; merely finding such declarations in the environment is not proof that the generated endpoint depends on them. Conversely, absence of concept names from a metadata report is not a substitute for actual endpoint dependency inspection. Acceptance requires no concept assumptions or sorryAx in the endpoint dependency closure, with only the explicitly permitted background axioms.

## What would and would not close the original obligation

The current exact source-hardness predicate is:

```lean
∀ A : Language, A ∈ NP → ManyOne A msscSourceLanguage
```

Even a fully validated generated SAT-hardness endpoint would only supply the first arrow. The remaining arrow is an actual total all-word ManyOne from that registered SAT language to this project's SourceBitMSSCDecision. It must include the exact parser, finite SAT-to-X3C construction if that route is used, normalization, MSSC serialization and all-input time/clean-output proof. A finite semantic equivalence or output-size bound cannot fill its operational field.

Once both arrows are genuinely supplied in the same compatible environment, the already written proof-side boolean_manyOne_trans composes them. The existing constructor then maps the exact MSSC language to the restricted marked-star decision language, and the separate verifier source proposes its membership in the declared NP class. None of these later facts makes the first two missing suppliers automatic.

The source-acceptance track remains independent: all 197 lineage source modules, actual finite instances, compatible imports and endpoint axioms still need eventual elaboration/kernel acceptance. The [finite-carrier/API author audit](POLYTOMY-FINITE-CARRIER-AND-API-SELF-AUDIT-20261023.md) supplies only the stated bounded static checks. No Lean source body, dependency pin, runtime permission or hardness assumption changes in this checkpoint. Broader stochastic cellular-identification obligations remain open.
