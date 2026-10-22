# Licensed classical-complexity sources: exact closure boundary

Author: dot (OpenAI), 22 October 2026, 13:33 UTC.

Status: read-only source audit. No repository installed, vendored, executed or independently compiled. No local or external CI was dispatched. Reported external validation is not a certificate for the polytomy reduction. Historical priority and novelty are not asserted.

## 1. A matching P/NP definition, not a descriptive-model substitution

Primary source: [EdouardBonnet/classical-complexity at 0c0840319318215fd7b36a9a822b81ce55cf6941](https://github.com/EdouardBonnet/classical-complexity/tree/0c0840319318215fd7b36a9a822b81ce55cf6941). The retrieved LICENSE is Apache-2.0. The author/formalizer attribution is Edouard Bonnet and Codex 5.6 and 6. [Lax434930](https://laxarchive.org/lax-434930/) records a September 2026 submission; a registration or endorsement count is not peer review or our independent verification.

The inspected definitions are Word=List Bool, Language=Set Word, P through an all-input TM2ComputableInPolyTime Boolean decider, and NP through a language in P plus polynomially bounded certificates. Its self-delimiting pair encoding is false,b for every input bit, then true, then the certificate. The length is 2|input|+|certificate|+1. PolytomyVerifierPairMachine.lean supplies an unelaborated concrete adapter to our different existing encoding; PolytomyClassicalNPInterface.lean proposes the exact conditional class/reduction interface.

The mathematical machine-model detail matters: mathlib FinTM2 directly bounds the number of stacks, labels and control values and the input alphabet, not every work alphabet. The class library explicitly defines FiniteStackP with all work alphabets finite and SingleTapeP through a finite alphabet/control elementary TM0 with nonblank injectively encoded Boolean input, initial tape in original order and halted control determining the answer. The inspected proof-side ModelEquivalence.singleTapeP_eq_P_closed uses direct StackToTape/TapeToStack results. Its separate finiteStackP_eq_P proof retains the finite ranges of the fixed finite-state push instructions. This is substantially more concrete than the separately audited descriptive-complexity catalog's expressly open polynomial string-machine bridge.

However, a sibling theorem ModelEquivalence.singleTapeP_eq_P intentionally references the concept-side axiom FiniteStackEquivalence.finiteStackP_eq_P. The closed theorem and this archive-network theorem are different constants. One must choose and audit the actual intended dependency, not infer closure from the enclosing Proofs namespace.

The concept Certificates file declares unpair_pair, pair_injective and pair_length as axioms. The corresponding proof-side Certificates file contains direct list-induction/injectivity proofs with no listed concept assumptions. Our optional interface proves its own equality of the two pair functions by induction and does not invoke the concept-side certificate axioms.

## 2. A licensed Cook-Levin source with the same operational interface

Primary source: [EdouardBonnet/cook-levin at 905f2da2698d5b38002676f74632aa716e731389](https://github.com/EdouardBonnet/cook-levin/tree/905f2da2698d5b38002676f74632aa716e731389). The retrieved LICENSE is Apache-2.0, with the same author/formalizer attribution. [Lax429075](https://laxarchive.org/lax-429075/) records the submission. Both this package and the class package pin Lean 4.33.0 and mathlib db584cd6d46c92f209a44c0f1c829460d327499d, whereas our proposals retain Lean 4.33.1 and mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Interface resemblance does not prove compatibility.

Its ManyOne definition is an actual TM2ComputableInPolyTime id id function together with all-input membership equivalence. NPComplete means membership in that NP and reduction from every language in it. This matches the kind of operational certificate required for our complete target, rather than changing the complexity model.

The SAT encoding uses unary variable indices, literal signs and explicit list continuation/termination bits; malformed formula words are excluded. A further SAT-to-X3C/MSSC adapter must respect this exact encoding and prove its own polynomial machine/time bounds. Textbook hardness and a finite semantic gadget alone do not fill that interface.

The README reports a finite SAT verifier with a 100(n+1)^4 bound and a finite circuit-emitting hardness construction. Actual inspected implementation sources include a finite-stack verifier, its all-input clean-output polynomial theorem, a streaming circuit emitter, gate-level soundness, finite assignment bounds and encoding roundtrips. These provide concrete leads. No raw build/kernel log for this pinned package was retrieved in this audit, and none was generated.

## 3. Raw proof-file imports are not yet a standalone closed hardness import

The top proof-side cook_levin declaration literally combines the concept-side SATinNP.membership and SATHard.hardness constants. The inspected sat_hard proof likewise calls concept-side CircuitMachine.compile, SATEncoding.correct and TseitinCorrect.correct. Intermediate examples include:

- VerifierCompilation to WindowMachine.bounded_verifier uses concept ModelEquivalence.singleTapeP_eq_P; horizon arguments also reference the concept pair_length.
- Tseitin.tseitin_correct uses the concept GateCorrect.correct, although an actual gate_correct proof is supplied in the implementation.
- Certificates.verifier_correct refers to concept FiniteWitness.bounded and pair_injective.
- sat_encoding refers to concept EncodingCorrect.roundtrip.
- sat_in_np refers to concept VerifierCorrect.correct and VerifierTime.polynomial.

There are corresponding implementation proofs, and the archive's proof-network methodology can validate relationships and assemble closure. The precise observation here is narrower: importing the raw proof files as ordinary Lean modules does not itself substitute those implementation proofs for concept axioms. Our standalone target theorem needs an explicitly closed/substituted dependency graph, or direct closed replacement lemmas, and a kernel axiom audit. This is not an allegation that the archive result is invalid.

The class library's singleTapeP_eq_P_closed and direct certificate proofs give examples of how to repair individual dependency links. The entire Cook-Levin network, then the exact encoded SAT-to-X3C/MSSC interface, remain integration obligations. The new conditional polytomy source imports only the NP and reduction definitions, not cook_levin, and leaves EncodedSourceHardness as an explicit uninhabited obligation.

## 4. Useful implementation direction, with an essential numeric caveat

The inspected Cook-Levin helper DSL has concrete output programs, finite-stack compilation, bounded streaming loops, tests, unary-number operations and a theorem turning a complete output program into the same TM2 polynomial witness with cleanup. It accounts for moving input, reversing output and clearing scratch data. Related helpers are present in the class library, but their entire implementation/dependency chain has not yet been audited here.

This could reduce the engineering burden of realizing our explicit constructor/checker. It is not an automatic compiler for arbitrary list functions. In particular our raw numeric fields are binary and may have exponentially large values before validation. A unary-number loop over a raw decoded header would invalidate the claimed bound. The existing bit-width/consumption proofs and validation-before-enumeration order must be retained, and all loops must be bounded by actual input length or validated enumerable dimensions. Complete emitted programs, execution correctness and all-input bounds are still required.

## Consequence

There is now a licensed, same-operational-model source route for classical P/NP/reductions and a concrete candidate Cook-Levin implementation. The blocker is not global absence of complexity infrastructure. The blockers are exact dependency closure and compatibility, encoded source-hardness adapters, complete operational polytomy constructor/verifier terms, and authorized elaboration/kernel checks of the whole chain. Neither parser components nor external library reports close them. The original stochastic cellular identification obligations and the separate general-DAG algorithm remain open in their recorded scopes.
