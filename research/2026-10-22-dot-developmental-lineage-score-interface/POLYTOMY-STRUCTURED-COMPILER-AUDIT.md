# A concrete compiler route and its exact remaining conditions

Author: dot (OpenAI), 22 October 2026, 12:20 UTC.

Status: read-only primary-source audit, elementary hand derivation and optional unelaborated source proposals. No external package was installed, imported by a running toolchain, vendored or executed. No local compiler, runtime or new CI was invoked. Existing pins and execution holds are unchanged.

## 1. A licensed external route exists

Szymon Toruńczyk and GPT, *Compositional polynomial-time computation with black-box subroutines*, Lax218471, registered 19 September 2026. Repository `szymtor/compositional-polytime`, pinned commit `7fadbfd005b359a66ccc1165b2d1becddb2906b8`, includes an Apache-2.0 license. This is a different repository from the previously audited unlicensed candidate. [Pinned repository](https://github.com/szymtor/compositional-polytime/tree/7fadbfd005b359a66ccc1165b2d1becddb2906b8), [archive](https://laxarchive.org/lax-218471/index.html).

Its manifest pins Lean 4.33.0 and mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`. Our source remains pinned to Lean 4.33.1 and mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. The complete `Mathlib/Computability/TuringMachine/Computable.lean` file was retrieved at both revisions and found text-identical. That is a useful interface check, not a proof that every dependency or tactic is compatible.

## 2. The concepts/proofs distinction must not be skipped

The package's `concepts/Lax218471/Combinators.lean` and `Substitution.lean` literally declare their theorem statements as axioms. This is the Lax concept/statement mechanism, with corresponding proof files separately recorded by the archive. Outside that mechanism, importing only the concepts and calling the concept-side theorem would not supply the proof we require.

The actual proof terms are in the separately named `Lax218471Proofs.Combinators` and `Lax218471Proofs.Substitution` namespaces. Their composition and compilation proofs were read, along with the operational compiler, transfer, call-simulation, routine-machine and execution definitions. The candidate adapter uses these explicit proof namespaces, not the similarly named concept-side axioms. The imported environment still contains concept declarations; a future dependency/axiom audit must establish the actual theorem's dependencies rather than relying on a text search alone. [Proof-side composition](https://github.com/szymtor/compositional-polytime/blob/7fadbfd005b359a66ccc1165b2d1becddb2906b8/proofs/Lax218471Proofs/Combinators.lean), [proof-side substitution](https://github.com/szymtor/compositional-polytime/blob/7fadbfd005b359a66ccc1165b2d1becddb2906b8/proofs/Lax218471Proofs/Substitution.lean).

## 3. What the actual compiler requires

The source language has push/pop/peek, finite-control updates, sequencing, branches, loops and calls. Final caller stack indices, alphabet and control state are finite. A call contract is a relation on lists, but each library entry must have a real finite TM2 implementation and a polynomial time bound. The contract certifies every admitted input/output pair; it cannot be filled merely by naming an arbitrary mathematical function.

The source `Executes` relation counts every atom, call, branch test and loop test. Every call argument and reply must satisfy an explicit size bound. The caller must end in a clean store with only its designated output populated and the original control state restored. The compiler proves preservation of unrelated caller data and cleanup of private work storage.

The exact call cost is the callee's actual step count plus twice the argument length, twice the reply length and four transitions. This includes two pairs of reversing transfer passes via temporary storage, with each pair preserving word order overall. If source instruction count is at most s(n), all call arguments/replies have size at most b(n), and Q is the program-dependent overhead polynomial, the compiled bound is s(n)*Q(b(n)). The inspected proof constructs an actual `TM2ComputableInPolyTime`, not a new unit-cost list model. [Operational call proof](https://github.com/szymtor/compositional-polytime/blob/7fadbfd005b359a66ccc1165b2d1becddb2906b8/proofs/Lax218471Proofs/CallSimulation.lean), [compiler](https://github.com/szymtor/compositional-polytime/blob/7fadbfd005b359a66ccc1165b2d1becddb2906b8/proofs/Lax218471Proofs/Compiler.lean).

## 4. Existing evidence, with its provenance

The archive records checked relationships for the five exposed proof statements. The repository's `CURRENT_STATE.md` reports full build/kernel replay on 19 September 2026 and an axiom audit restricted to propext, Classical.choice and Quot.sound. These are external records, not runs performed here.

The complete pinned repository tree does not include the referenced workspace-level validation/audit logs. The public Actions query returned zero runs. Thus this audit retrieved the source and the external verification reports, not their raw build/replay logs and not an independently reproduced build. No statement about our own unelaborated source changes follows from those reports. [External status report](https://github.com/szymtor/compositional-polytime/blob/7fadbfd005b359a66ccc1165b2d1becddb2906b8/CURRENT_STATE.md).

## 5. A small actual-machine primitive, precisely scoped

`PolytomyConstantBranchMachine.lean` supplies our own proposed concrete TM2 term for a fixed output literal: one Bool stack is both input and output, one loop label is used, and the control state is Boolean. Each nonempty input step pops one symbol and loops. On the empty stack, the machine writes the fixed literal in the correct order and halts with its initial false control state. There are no auxiliary work stacks.

Induction on input length gives n+1 pinned-TM2 statement steps. The final statement contains finitely many pushes determined by the fixed literal; there is no input-dependent output oracle hidden in that statement. The pinned model counts one finite program statement per transition, with a machine-dependent constant translating that count to elementary pushes/pops.

The terms `fixedYesBranchPoly` and `fixedNoBranchPoly` use the existing genuine marked-star target encodings. They do not replace the target language by Boolean sentinels. They only emit a fixed target, and DO NOT implement the guard that selects a branch, parse an input, construct a nontrivial gadget or check a refinement. This is a component, not a substitute for the full constructor/verifier. All its proof terms remain UNELABORATED.

## 6. The optional adapter retains the full claim

`PolytomyCompilerAdapterProposal.lean` references the external proof-side compiler by fully qualified name. Its constructor wrapper requires an actual structured program, actual library witnesses, and an all-input source execution proof whose exact output is `scanEncodedConstructor`. Its verifier wrapper requires the independent total pair-tape function `scanPairVerifier`, emitting exactly one Boolean.

Both wrappers are explicitly CONDITIONAL on those programs and execution/size/step proofs. They are not inhabitants of either complete machine-witness type. The fixed-literal primitive can furnish a genuine constant-output contract, but it cannot justify arbitrary other library entries. A composition wrapper uses the proof-side theorem with the same Boolean intermediate encoding.

No Lake manifest was changed and no dependency was installed or copied into this packet. The optional file cannot be treated as a successfully elaborated part of the existing package. It is a source-level integration proposal whose external imports need authorized dependency preparation and compatibility checking before any validation.

The full actual-D_lambda/all-refinement finite reduction, all-string malformed/boundary handling, independent scanner and resource bounds remain unchanged. The substantive missing work is explicit structured constructor/verifier programs, real subroutine implementations, uniform all-input execution and polynomial bounds, compatible upstream formal MSSC/X3C hardness, and kernel validation of the complete dependency chain. The compiler route does not supply those domain algorithms by itself.

No historical novelty, full formal NP-completeness, compiled performance or biological-identification closure is claimed.
