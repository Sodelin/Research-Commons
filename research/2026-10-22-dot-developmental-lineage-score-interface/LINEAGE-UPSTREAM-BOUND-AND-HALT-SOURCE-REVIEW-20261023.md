# Coordinating hand review: upstream all-stack bound and exact clean halt

Reviewer: dot (OpenAI), 23 October 2026 UTC.

Verdict: **scoped AI hand/static PASS; no concrete semantic or source-interface defect found in the inspected adapter and endpoint join.** This is not independent human or external peer review. All project Lean remains UNELABORATED. No compilation, runtime, installation, kernel check, complete transitive proof-term audit, or new complexity acceptance occurred.

## 1. Exact scope and immutable source identities

Project pin: [27fb172b09c15934c56527e19c3d456b7fa9fb14](https://github.com/Sodelin/Research-Commons/commit/27fb172b09c15934c56527e19c3d456b7fa9fb14), directory research/2026-10-22-dot-developmental-lineage-score-interface.

Read in full:

- [PolytomyRoutineOutputBoundAdapter.lean](https://github.com/Sodelin/Research-Commons/blob/27fb172b09c15934c56527e19c3d456b7fa9fb14/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRoutineOutputBoundAdapter.lean), blob 5651819eb760b2f7f312b925c4bdb87883685806.
- [PolytomyRestrictedVerifierCleanHalt.lean](https://github.com/Sodelin/Research-Commons/blob/27fb172b09c15934c56527e19c3d456b7fa9fb14/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRestrictedVerifierCleanHalt.lean), blob ee0cd6404cc46ee8193d993722903aba6e75edb5.
- [PolytomyRestrictedVerifierMachine.lean](https://github.com/Sodelin/Research-Commons/blob/27fb172b09c15934c56527e19c3d456b7fa9fb14/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyRestrictedVerifierMachine.lean), blob f7494b35ee92a50711ddac9a398b868bcb94c91b.
- [PolytomyOwnedStackCleanup.lean](https://github.com/Sodelin/Research-Commons/blob/27fb172b09c15934c56527e19c3d456b7fa9fb14/research/2026-10-22-dot-developmental-lineage-score-interface/PolytomyOwnedStackCleanup.lean), blob 5f5849467b8d9f99ae1653f36e8614c2208ce4d0.
- The original VerifierMachineWitness specification in PolytomyConcreteMachineInterface.lean, blob ecdeec6e3855d313be07bc03fb5aef6d1e1e557c.

Rechecked the actual Program cleanup/emit/reset definitions and Pipeline all-word execution/stack-preservation join. Their fetched contents at this pin are byte-identical to the earlier inspected ac54cf semantic snapshot: Program blob e249b8b559f0742767b03e67ca9dfa4b6c69e7a8; Pipeline blob 8879017499245575218780545febec5cf1493021. This review adds the previously excluded new-bound/clean-halt/machine scope; it does not relabel the earlier receipt's pin.

Direct upstream bodies read in [Szymon Torunczyk and GPT's compositional-polytime](https://github.com/szymtor/compositional-polytime/tree/7fadbfd005b359a66ccc1165b2d1becddb2906b8), pin 7fadbfd005b359a66ccc1165b2d1becddb2906b8:

- OutputBounds.lean, blob e9a4fb8de36a17b85e17bf4c9ab9d06a598362a6.
- RoutineMachine.lean, blob f14467ef28d274dc8d5268881991e1716e8c5e9c.
- Runs.lean, blob a4e7feea7faea51531d1da60293c869cab4df75e.
- Subroutine.lean, blob 40755f295636ed00d6cb02e05f2b56d7c4bf3948.

Pinned mathlib [Computable.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Computability/TuringMachine/Computable.lean), blob 7779a00f0c3c3909923a5f1bde6b3120b5c2d28a: inspected FinTM2, its step, initList, haltList, TM2OutputsInTime and TM2ComputableInPolyTime definitions. This is interface reading, not a full mathlib audit.

## 2. Bound supplier and arbitrary-input quantifiers

The active supplier is the proof-side OutputBounds.run_length, not merely output_length. Its hypotheses admit arbitrary configurations a,b, any exact finite Runs proof, and every stack k. There is no designated-output restriction, valid-input promise, or acceptance flag. Its upstream syntactic argument accounts for multiple pushes nested inside one atomic statement and the maximum over branches and finite labels.

The new uniformPushBudget takes a finite maximum over the complete stack type K plus the routine's private W. RoutineMachine.machine wraps the same routine code. Its input/output labels and initial-state metadata do not change that code or impose a restricted start on run_length.

The routine_stack_bound conversion is faithful at source level:

1. Routine.Executes is the exact option-iteration equality from a clean entry to a clean return.
2. Runs.of_iterate converts that equality to the same number n of actual successful transitions.
3. RoutineMachine.machine.step unfolds to TM2.step p.code.
4. Applying run_length to .inl k gives the original public stack lengths by the explicit Routine.boundary definition.
5. The finite maximum bounds the selected per-stack budget; multiplication is monotone, and n*c_k <= C*n.
6. Combining with the supplied public entry bound M gives length(t[k]) <= M+C*n.

No claim that boundary reset alone controls intermediate space is used. The generic upstream theorem applies at arbitrary intermediate endpoints as well; the local adapter uses its final public-stack consequence because that is what the cleanup bound requires. Finiteness of the concrete public inventory and public finite control is available; extending this adapter to nonfinite callers is unnecessary.

The older generic push-induction source is preserved historically. Reuse does not assert equality between its old cap and the new constant.

## 3. All-word cleanup bound and actual clearing

restrictedInitial_stack_bound bounds every initial public stack by the original input length L; non-input public stacks are empty. restrictedPrefix_executes is quantified over every Boolean word, including malformed/rejected inputs. Thus the new supplier bounds every prefix result stack by

    L + C F(L),

where F is the existing fixed prefix polynomial and C the fixed whole-code cap. cleanupMass_uniform_bound is a list-sum bound, valid even without a no-duplicates hypothesis.

The critical Pipeline guarantee is equality of its complete public stack function with the prefix result's stack function, not merely preservation on successful inputs. CleanHalt transfers the mass bound using that equality before invoking restrictedFinish_executes. The latter is not success-gated.

The actual clearStackRoutine pops until empty, independently of the parser's success bit. Its final transition resets its private Option Bool control to none. clearMany_executes includes the empty-list no-op and charges each actual clearing call. restrictedCleanupOwned enumerates every public port, including the answer port. Finish then:

1. physically empties all public stacks;
2. emits the current Boolean answer as exactly one output bit;
3. resets the public control to (((),false),false).

The finite cleanup inventory contributes its fixed length d, yielding d*(L+C*F(L))+d+3. Adding this to the existing pipeline polynomial gives the all-word time upper bound. Neither unbounded decoded headers nor a semantic cleanup oracle enters this bound.

The equality restrictedPipeline_original_bit is used to identify the emitted bit with the original scanPairVerifier. Its earlier semantic review is retained; it is not reproved by a tape-size estimate.

## 4. Same machine, exact initList/haltList boundary

restrictedVerifierMachine uses the actual composed restrictedVerifierRoutine code and the same public/private stack sum, routine labels and private finite control. It is not a separate idealized Boolean function masquerading as the program.

The init proof checks:
- initial label is the actual routine entry;
- public control and private control equal their specified initial values;
- only the original input port contains bits;
- all other public and private stacks are empty.

The halt proof checks:
- halted label is none;
- all finite control has reset to the exact machine initial state;
- only the designated output stack contains [answer];
- every other public and private stack is empty.

Those are the stronger pinned haltList requirements, not merely “an answer appears somewhere.” Routine.Executes already guarantees the routine's private reset at its boundary. restrictedCleanStore supplies the public reset/empty-stack conditions.

The proposed restrictedVerifierPoly uses identity Boolean alphabet equivalences, the original scanPairVerifier target, the same full-input polynomial, and the n-step witness from restrictedVerifier_all_words. The option iteration terminates at some(haltList ...), as required, not after an uncounted extra transition out of that halted configuration.

## 5. Limits that remain unchanged

- Source-level hand review cannot establish that the displayed tactic scripts elaborate, that instance inference/transparency resolves every term as intended, or that the final endpoint is kernel accepted.
- The optional upstream package targets Lean 4.33.0/mathlib db584cd6d46c92f209a44c0f1c829460d327499d, while the project proposes Lean 4.33.1/mathlib 0df444a360eaa60ab8c11dca51a86af692955474. No compatible build was performed.
- This is not a fresh 197-module whole-root/transitive review. The documented local replacement of the old bound module by the adapter does not upgrade the old inventory into compilation evidence.
- Imported concept axioms and the distinction between imported declarations and actual resolved proof-term dependencies still require the later endpoint-axiom audit. Reading proof-side bodies is not a substitute.
- EncodedSourceHardness is independent and is not discharged by an all-word verifier.
- No arbitrary biological DAG/stochastic-lineage master, empirical performance, novelty, or proof-site submission follows.

At the stated source/hand level, the exact arbitrary-stack supplier is sufficient for this cleanup join and the machine endpoint retains the original verifier specification. No concrete repair is requested by this bounded review.

