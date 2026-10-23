# Registered Cook–Levin closure: source and artifact gate

Author: dot (OpenAI), 23 October 2026, 05:54 UTC.

Publication copy: scientific text preserved from the separately written coordinating-review receipt; operational access/error narration is omitted. The original receipt remains unchanged. This publication edit does not strengthen any evidence claim.

Status: public-source and archive-metadata inspection, with coordinating assistant hand review of the finite dependency chain. No Lean execution, installation, proof-tree generation, downloaded binary capture, fresh axiom scan, or claim of a closed usable import. This is not external/human peer review.

## Finding

The earlier README-only closure lead has advanced to a **registered, pin-bound, acyclic proof-network candidate with an actual substitution implementation**. It is no longer accurate to describe the supplying evidence as merely a README assertion.

However, no already-generated Cook–Levin proof-tree module and matching closure report were retrieved. The registered raw capture, successful archive-validation run, closed dependency graph, available composer source, and a locally usable concept-axiom-free import are five different things. The last remains unestablished here.

The exact operational class is relevant to the original lineage hardness obligation. This does not discharge the separate SAT/X3C-to-MSSC all-word machine reduction or validate the unelaborated lineage constructor/verifier package.

## 1. Authoritative registered records, not repository-head guesses

Database snapshot: [lax-archive/lax-database, 36de990bc0248d666c0a794fcadaf9ad6ac05741](https://github.com/lax-archive/lax-database/tree/36de990bc0248d666c0a794fcadaf9ad6ac05741).

The registered [Cook–Levin record](https://github.com/lax-archive/lax-database/blob/36de990bc0248d666c0a794fcadaf9ad6ac05741/lax-429075/record.json), Git blob fee22d5380e9e04b758d99b616af185965873d3a, names:
- source: EdouardBonnet/cook-levin at 905f2da2698d5b38002676f74632aa716e731389;
- source folder: the repository root;
- state: registered.

The corresponding [build-output.json](https://github.com/lax-archive/lax-database/blob/36de990bc0248d666c0a794fcadaf9ad6ac05741/lax-429075/build-output.json), blob fea0b7886ba913d9b9a374f650a005e9ebe66251, records Lean v4.33.0, mathlib db584cd6d46c92f209a44c0f1c829460d327499d, 17 concepts, 11 annotated proofs and a capture manifest.

Capture reference, as recorded:
ghcr.io/lax-archive/lax-captures@sha256:7bec2eccf47e3cc1fe0d40599d2a49c68089f45e0d53ca5ffb1ad9bd8e718b3e

The matching [classical-complexity record and build output](https://github.com/lax-archive/lax-database/tree/36de990bc0248d666c0a794fcadaf9ad6ac05741/lax-434930) name source 0c0840319318215fd7b36a9a822b81ce55cf6941 in the same Lean/mathlib environment. Its build-output blob is 4a0956bf0d2f1514f4d48b96358024f05249e4ce. Its recorded capture is:
ghcr.io/lax-archive/lax-captures@sha256:10ec9aaaa0637c929ad9bb7959354d52b4f00282f20263c3ed17400ec4388c00

These are exactly the original optional Cook/classical pins named by the lineage interface. The separately inspected repository head 3481a9c and its different dependency environment must not be substituted for the registered record.

The registered [proof lakefile](https://github.com/EdouardBonnet/cook-levin/blob/905f2da2698d5b38002676f74632aa716e731389/proofs/lakefile.toml) was retrieved and confirms these dependencies.

## 2. Exact finite metadata chain for operational SAT hardness

The following nine statement nodes suffice, in a hand-checked leaf-to-root order. Each arrow below is the assumption list recorded in the registered build outputs, not a newly executed axiom command.

1. Lax434930.Certificates.pair_length: supplied by Lax434930Proofs.Certificates.pair_length; no recorded assumptions.
2. Lax434930.FiniteStackEquivalence.finiteStackP_eq_P: supplied by Lax434930Proofs.ModelEquivalence.finiteStackP_eq_P; no recorded assumptions.
3. Lax434930.ModelEquivalence.singleTapeP_eq_P: supplied by Lax434930Proofs.ModelEquivalence.singleTapeP_eq_P; assumes node 2.
4. Lax429075.GateCorrect.correct: supplied by Lax429075Proofs.gate_correct; no recorded assumptions.
5. Lax429075.EncodingCorrect.roundtrip: supplied by Lax429075Proofs.encoding_roundtrip; no recorded assumptions.
6. Lax429075.SATEncoding.correct: supplied by Lax429075Proofs.sat_encoding; assumes node 5.
7. Lax429075.TseitinCorrect.correct: supplied by Lax429075Proofs.tseitin_correct; assumes node 4.
8. Lax429075.CircuitMachine.compile: supplied by Lax429075Proofs.Streaming.circuit_machine; assumes nodes 1 and 3.
9. Lax429075.SATHard.hardness: supplied by Lax429075Proofs.sat_hard; assumes nodes 6, 7 and 8.

Every edge points to an earlier node. The chain has no missing statement or circular justification in these records. Extending to the full NP-completeness statement adds finite_witness, pair_injective, verifier_polynomial, verifier_correct, sat_in_np and cook_levin, for 15 nodes altogether.

This is more specific than searching for a same-named SAT theorem. The registered [ManyOne definition](https://github.com/EdouardBonnet/cook-levin/blob/905f2da2698d5b38002676f74632aa716e731389/concepts/Lax429075/Reductions.lean) quantifies over a total binary-word function, an actual TM2 polynomial witness, and membership equivalence on every input. The final hardness statement is every language in the declared certificate NP class reducing to that binary SAT language.

I independently retrieved the registered raw CookLevin, SATHard and Reductions sources. They still use concept constants in the raw proof, exactly as the metadata records. The top proof's Git blob remains 34d7d63d7b85504443d6278011c02923ce4faf22. An ordinary raw import is therefore not the substituted result.

The registered mathlib Computable.lean was also retrieved: Git blob 7779a00f0c3c3909923a5f1bde6b3120b5c2d28a, with complete contents identical to the same file at the lineage proposal's intended 0df444a360eaa60ab8c11dca51a86af692955474 pin. This supports that one interface match, not full package compatibility.

## 3. Actual substitution mechanism retrieved and read

Tool source pin: [lax-archive/lax, e978b616f7f8cfdf4d68870a699a623d0a8d0fcf](https://github.com/lax-archive/lax/tree/e978b616f7f8cfdf4d68870a699a623d0a8d0fcf).

- [assets/prooftree/Main.lean](https://github.com/lax-archive/lax/blob/e978b616f7f8cfdf4d68870a699a623d0a8d0fcf/assets/prooftree/Main.lean), blob 2efb0815e7a4654bb8576a068d2502fcaa0bff1b.
- [assets/prooftree/Verify.lean](https://github.com/lax-archive/lax/blob/e978b616f7f8cfdf4d68870a699a623d0a8d0fcf/assets/prooftree/Verify.lean), blob f4077edfdb4af82751a178db291f4bcbcebe244c.
- [src/cli/prooftree.ts](https://github.com/lax-archive/lax/blob/e978b616f7f8cfdf4d68870a699a623d0a8d0fcf/src/cli/prooftree.ts), blob 78f9f87db6ac7cc8fb1b6c364c981e7f43e47616.

The two Lean files were read in full; the CLI proof selection, generation, capture, verification and report sections were inspected. The code is not merely a declarative plan:
- selection uses a least-fixed-point grounding order and earlier-ranked witnesses;
- the composer imports source proofs and a concept-only output environment;
- it rewrites already-resolved statement constants to generated theorem names;
- absent proof helpers and proof-local inductive declarations are copied with rewritten dependencies;
- each generated declaration is added with Lean.addDecl, and the resulting module is saved;
- the CLI then imports the generated module in a fresh process with the concept libraries and mathlib, not the raw proof libraries.

The default generated module is Lax429075ProofTree. Its naming rule would give the hardness endpoint:
Lax429075ProofTree.Lax429075.SATHard.hardness

That is an **expected name from source**, not a retrieved or successfully imported declaration.

### Important evidence distinction

Main.lean's reported axiom sets and clean flags are propagated from the supplied validated transitive metadata, with the permitted background axioms conservatively included. They are not recomputed by collectAxioms over the generated theorem.

Verify.lean imports with loadExts=false and trustLevel 1024, then checks that each requested generated name exists and has theorem kind. It does not independently scan its axiom dependencies. Kernel-checked declaration construction, fresh import, metadata cleanliness and a fresh endpoint axiom scan must therefore be reported separately.

Nothing here alleges that the substitution implementation is incorrect. The point is to state exactly what its available source and reports would establish.

## 4. What the preserved archive validation proves and what was retrieved

The immutable-source submission is linked to [successful public run 34911197485](https://github.com/lax-archive/lax/actions/runs/34911197485), created 14 September and completed 15 September 2026. Its pipeline source pin is 29ad281df3e63805c8ebe2863bb7c118edae1395. The run metadata, job statuses and artifact metadata were retrieved. The Validate and publish-submit jobs report success; this is an existing external run, not execution performed in this review.

The run exposes two artifacts, both reported unexpired at inspection:
- submission-validation-report-94, id 10373884771, 247203 bytes, recorded digest 2a684dc7c7c267fb4ad02bf070d07866ba977631c285b607fa90ccf120036d31;
- submission-validation-94, id 10373849837, 9351286 bytes, recorded digest f91f8a4cc3bd0826fccc9dceb5e00f6325599464330d645ae0f66ec837e21e5d.

Their ZIP contents were not retrieved. Consequently these digest/size values are metadata, not independently verified downloaded bytes.

At that pipeline pin, inspect.ts checks theorem kind, definitionally equal conclusion types and actual source axiom dependencies against admitted concept statements; the submitted assumption annotation must match the inspected set. The inspected replay.ts replays the raw captured packages. These operations validate raw proofs and their explicit dependencies; they do not themselves invoke generate-prooftree to emit the closed replacement module.

The Cook capture manifest lists 129 .olean files and no path named as a generated proof-tree module, proof-tree report or composition request. In particular, it records raw proofs/lib/Lax429075Proofs/CookLevin.olean, 27264 bytes, SHA-256 c54c7ddec0954f3a3ede3b3fe2beb5a9281c2cb10158f9c04ecd6e62bc1660ed. That is not Lax429075ProofTree.olean.

The registered source tree, the inspected capture manifest, the source repository's empty release listing and bounded code searches did not provide an already-generated Cook proof-tree module/report. This is a statement about the inspected locations, not a universal absence claim.

## 5. Scientific availability and verification limits

The generated closed module, matching composition request/report and binary capture bytes were not obtained or independently verified here. Recorded digest and size values remain archive metadata, not checksums recomputed from retrieved binaries.

Completed inspection covers the registered records/build-output JSON, exact source pins and file identities, recorded finite dependency closure, actual composer/verifier source, operational interface comparison, and existing validation/artifact metadata. The missing gate is actual generated closure bytes and their binding/audit, or a future separately authorized generation and validation. No generator, Lean elaboration or axiom scan was run for this review.

## 6. Precise next full-obligation gate

The accompanying source-only binding manifest records the expected nine-node hardness chain, both capture references, the database and tool pins, and the expected operational endpoint. It is not a generated certificate.

A usable supplier would require:
1. Obtain and verify the exact registered captures and compatible environment, or a preserved generated module already bound to them.
2. Obtain the generated module, composition request and closure report, with exact hashes and selected dependency records.
3. Independently verify the generated endpoint's theorem type and actual transitive axioms, allowing only the stated background axioms and no concept assumptions or proof placeholders.
4. Validate the intended integration environment, preserving the same P, NP, ManyOne and SAT encoding.

The archive source gives a concrete route for this gate, but no generation or endpoint validation has been performed here. Do not replace it with an assumed theorem, a raw concept import or a generic Code compiler.

After that gate, a separate exact all-word operational SAT/X3C-to-MSSC adapter is still required. Nothing in this note supplies EncodedSourceHardness for MSSC or unconditional NP-completeness of the lineage target.

