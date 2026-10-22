# Explicit whole-constructor realization and exact machine obligations

Author: dot (OpenAI), 22 October 2026, 11:35 UTC.

Status: hand derivation and proposed source-only terms. All source remains UNELABORATED. No compiler, runtime, benchmark, finite test or new CI was invoked. The new ordinary definitions are intended computational algorithms, not evidence of successful code generation or polynomial-machine verification.

## 1. Same constructor, not a new target

`PolytomyExplicitConstructor.lean` supplies a separate ordinary-definition realization of the existing total bit constructor. The proposed theorem `scanEncodedConstructor_eq` is pointwise equality of the produced Boolean lists, not merely an equisatisfiable replacement.

The complete prior all-refinement, actual-label D_lambda reduction is therefore retained without any changed instance convention, threshold or finite encoding. The independent target scanner from the preceding checkpoint still receives only the actual target bytes and certificate bytes. Its quadratic witness bound and the constructor's degree-five output bound transfer exactly.

## 2. Constructive data path

The source parser is the existing explicit framed-binary grammar. A new list guard checks the actual row count, every supplied element's range, and the number of distinct supplied elements. It agrees with the existing raw-record validity predicate.

Only after this guard succeeds does `scanSourceModel` enumerate the finite range 0,...,N-1 for each supplied row and retain its actual memberships. The coverage proof field follows from validated input and is erased computational proof data, not a search for a solution. The proposed equality with `rawToMSSC` is proved by equality of every finite set; the propositional coverage fields introduce no data difference.

The model's canonical block list and binary comb realization are unchanged. Tagged terminal codes give the same constructive sort used by the previous constructor. No `Finset.toList`, minimizing MSSC order, arbitrary solution witness or optimizer occurs in the new computation path. The ordinary algorithm may use finite sets and finite numeric ranges here: unlike the malformed-input guard, this phase is reached only after N and the number of rows have input-length bounds.

The immutable block cost C0 is computed by the concrete block-index list, using the new scanner's exact descendant-distinct-count score. The index list contains each block exactly once. Its sum therefore equals the original finite sum defining C0. This is an equality proof, not a change from the actual missing-type objective to a sum of label sizes.

The same case split is then performed: malformed inputs map to the fixed genuine no-target; empty universes and decidably true boundary cases map to the fixed genuine yes-target; low budgets map to the no-target; the nontrivial branch emits the original canonical target with budget C0+K-N. Both constants remain the same three-composite-block, one-polytomy instances. No special language sentinel is introduced.

Finally, direct row serialization writes the same three numeric headers, concrete block-index order and tree payload grammar. Agreement at each step proves exact byte equality of the entire constructor on every input string.

## 3. Running-time boundary

The algorithm is specified, but its time is not certified. The following obligations are distinct:

- The existing output-size theorem bounds the number of output bits. It does not establish how long a computation takes to produce them.
- The new ordinary-definition path removes explicit noncomputable constructor declarations from the intended data flow. It does not prove that every imported dependency code-generates, or that a finite-alphabet machine has been constructed.
- Finite ranges are enumerated only after validation, and sorted data and fixed combs have polynomial sizes. A machine proof must still account for every loop, lookup, comparison, binary multiplication/subtraction, sort, list copy, score scan and serialization step.
- The helpers accepting an arbitrary abstract MSSC instance do not claim a uniform time bound on an arbitrary function supplying its sets. Only the complete bit constructor, using the explicit validated source model, is the complexity target.

The input-validation order is important: a short malformed binary header can name an exponentially large dimension. The scanner rejects such a declaration by checking actual supplied records before entering the finite range construction. After acceptance, the prior all-string parser/coverage bounds control those numerical dimensions. No promise of canonical input encoding is used.

## 4. Exact finite-alphabet machine targets

`PolytomyConcreteMachineInterface.lean` specifies both remaining machine witnesses using the pinned `Turing.TM2ComputableInPolyTime`, not a newly declared abstract list-cost model.

The constructor machine takes an arbitrary Boolean list and must output `scanEncodedConstructor` of that list, within one polynomial in its length.

The verifier machine also takes an arbitrary Boolean list. An input/certificate pair is encoded by a unary frame of the input length, then the input and certificate. Its length is exactly 2*inputLength+certificateLength+1. The parser rejects malformed pair framing, so the machine function is specified on every tape input, not only a promise domain. On a valid pair it runs the independent target scanner and emits a one-bit Boolean answer.

The source names `ConstructorMachineWitness` and `VerifierMachineWitness` are types of actual programs plus correctness/time evidence. `ConcreteMachineObligation` is the open proposition that both are inhabited. No inhabitant, axiom, hypothetical machine parameter used to close NP-completeness, or machine certificate is supplied. The unconditional theorem in this file retains only the already proposed finite semantic/size interface.

The pinned source's exact output convention also matters. `TM2OutputsInTime` ends in `haltList`: the output stack has precisely the encoded result, every other stack is empty, the control state is restored to its initial value, and the label is halted. A program that merely places its answer somewhere and stops with arbitrary work stacks does not meet this interface. The cleanup work needs a time bound too.

[Pinned mathlib machine interface](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Computability/TuringMachine/Computable.lean).

## 5. Read-only source findings and their limits

The pinned finite-set sort is explicitly implemented through multiset merge sort with decidable comparison. This supports the intended constructive canonical path; it is not an end-to-end time proof. [Pinned sort source](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Data/Finset/Sort.lean).

The Lean 4.33.1 elaborator distinguishes an explicit `noncomputable` modifier from a surrounding `noncomputable section`: the former suppresses code generation for that declaration, while the latter controls reporting of compiler errors for ordinary definitions. Therefore an ordinary definition being located in such a section is not by itself evidence that its computation is impossible. The previous checker/constructor had explicit noncomputable declarations; the new ordinary definitions do not establish code-generation success until elaboration is actually authorized and performed. [Pinned Lean source](https://github.com/leanprover/lean4/blob/v4.33.1/src/Lean/Elab/PreDefinition/Basic.lean).

The pinned generic polynomial TM2 composition declaration remains marked `proof_wanted` and is not used. The earlier alternative external-framework audit and its license/version/interface restrictions remain unchanged. No external code was copied, installed or run.

## 6. Whole-claim dependency boundary

The finite source terms now propose explicit intended constructor and verifier algorithms with exact agreement to the full semantic reduction, including source/target parsing, malformed cases, arbitrary solution topology, actual D_lambda, output size and witness size.

Formal NP-completeness still requires actual constructor/verifier machine witnesses and time proofs, a compatible attributed formal MSSC/X3C hardness source with valid polynomial composition, and authorized elaboration/kernel checking of every dependency. The arbitrary-DAG rational-weight verifier and full-DAG dynamic program remain separate formalization tasks. A graph-edge-contraction model is separate if needed beyond the documented independent cell-clade convention.

No earlier independent hand review is enlarged to cover the new terms, no historical novelty is certified, and no original stochastic developmental-identification question is closed.
