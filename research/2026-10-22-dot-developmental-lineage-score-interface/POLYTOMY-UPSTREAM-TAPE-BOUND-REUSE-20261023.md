# Reuse the existing arbitrary-stack run bound

Author: dot (OpenAI), 23 October 2026, 04:56 UTC.

Status: primary-source comparison and OPTIONAL UNELABORATED adapter source. No compiler, runtime, installation, CI dispatch or kernel acceptance. This changes the proof supplier and fixed resource constant, not the original restricted verifier language or machine program. The separate encoded-hardness premise remains open.

## The antecedent covers the needed case

Fresh inspection of Szymon Torunczyk and GPT's Apache-2.0 [compositional-polytime](https://github.com/szymtor/compositional-polytime/tree/7fadbfd005b359a66ccc1165b2d1becddb2906b8) found the directly relevant theorem in [OutputBounds.lean](https://github.com/szymtor/compositional-polytime/blob/7fadbfd005b359a66ccc1165b2d1becddb2906b8/proofs/Lax218471Proofs/OutputBounds.lean), blob `e9a4fb8de36a17b85e17bf4c9ab9d06a598362a6`. That source credits `Lax759944Proofs.TMToRam.Safety`, registered source `134e398cef46599371df99f10c9007bc34ba3868`, for the single-transition push-count argument. We preserve that attribution without claiming to have independently inspected the earlier source.

The exact relevant interface is `OutputBounds.run_length`: for an arbitrary finite TM2, arbitrary configurations a and b, an actual n-step `Runs` proof from a to b, and any stack k, it bounds the length of b's k-stack by the length of a's k-stack plus n times the machine's syntactic push budget for k. Its k need not be the designated output. Its configurations need not be `initList`/`haltList`. No valid-input or accepting-run promise appears. Private stacks are included in the same stack index type.

This is stronger for our use than merely a final output-size theorem. The source's earlier structural proof accounts for every push in a nested statement and the maximum among branches, then takes the maximum over finite labels. It does not assume one push per TM2 transition.

Our independently written `PolytomyFixedCodeSpaceBound.lean` used a maximum total push count over each statement and allowed nonfinite caller-stack/control types. That extra generality is not needed: the actual restricted prefix uses finite `RestrictedPort`, finite `CountdownState Unit`, and Bool public alphabets. Accordingly the active chain now reuses the antecedent rather than maintaining a duplicate structural induction as a required dependency. The historical generic source is retained, with an attribution comment, and its immutable original remains at commit `4226599d72ba65ef0f849785ad77d0224fda4d29`.

## Short faithful adapter and full-chain consequence

`PolytomyRoutineOutputBoundAdapter.lean` imports the actual proof-side `OutputBounds` and `RoutineMachine` modules at the same previously recorded optional pin. `RoutineMachine.machine p input output initial` has exactly p's routine code, public/private stacks and finite control. Its input/output/initial metadata do not restrict the arbitrary configurations to which `run_length` applies. This analysis package is constructed for the already-defined prefix, not recursively from the final verifier, so there is no circular machine definition.

Let c_k be that source's per-stack push bound and C the maximum of c_k over the complete fixed finite stack inventory, including private stacks. For any actual routine execution from s to t in n transitions and any uniform initial public-stack bound M,

    length(t[k]) ≤ length(s[k]) + n c_k ≤ M + C n

for every public k. The new adapter is just this finite maximum and application of `run_length`; it does not repropose a new push/run induction. The private initial boundary is empty and private return boundary reset exactly as before. The upstream theorem already accounts for private intermediate behavior.

For the all-word restricted prefix, M=L=input length and n≤F(L), where F is the already supplied prefix polynomial. Hence every saved public stack has length at most L+C F(L), on malformed and early-rejected inputs as well as successful inputs. With d the fixed public cleanup inventory length, actual clearing, one-bit emission and finite-control reset retain the bound

    d (L+C F(L)) + d + 3.

`PolytomyRestrictedVerifierCleanHalt.lean` now imports this adapter, defines its prefix cap by this finite maximum, and uses the new bound in the same all-word cleanup proof. The exact program, original bit equality, eight success-gated guards, original parser semantics, clipping justification, `initList`/`haltList` endpoint, and `EncodedSourceHardness` premise are unchanged. The natural-coefficient resource polynomial has a newly specified fixed constant; no equality between the old and new constants is asserted or needed.

The root's local import closure changes by replacing `PolytomyFixedCodeSpaceBound` with `PolytomyRoutineOutputBoundAdapter`. The previously published 197-module inventory remains an accurate historical inventory of its explicitly pinned `f5a8fee` snapshot. The two new direct external names, `Lax218471Proofs.OutputBounds` and `Lax218471Proofs.RoutineMachine`, were already transitive imports of the existing proof-side `Combinators` entry; no new external repository or version is adopted.

## Actual imported axioms versus actual proof dependencies

The adjacent `POLYTOMY-ROUTINE-DEPENDENCY-INVENTORY-20261023.json` records the 19 modules in the pinned routine library's textual transitive closure, every retrieved Git blob and direct import, and declaration-name/pattern observations. There are 14 proof-side modules and five concept-side modules. The concept `Combinators` module declares `output_size`, `graph_realizable` and `comp` as axioms; concept `Substitution` declares `compile` and `polytime` as axioms. These imports must not be hidden by a blanket claim that the imported environment is axiom-free.

The inspected proof-side route instead writes actual bodies: `Combinators.comp` uses proof-side `OutputBounds` and `Substitution`; proof-side substitution uses `Compiler.correct` and `RoutineMachine.outputs`; the compiler uses concrete calls/control/composition; call simulation physically transfers input/output and preserves the caller. The searched placeholder patterns were absent from those proof-side files. This is a source-level dependency reading, not a kernel determination of resolved names, tactic-generated terms, or transitive theorem axioms. A later whole-root audit must inspect those actual terms. Merely importing concept declarations does not prove dependence on them, and merely importing proof modules does not prove independence from them.

The optional library still pins Lean 4.33.0/mathlib `db584cd6d46c92f209a44c0f1c829460d327499d`, whereas our proposed root retains Lean 4.33.1/mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. Reuse does not resolve this compatibility gap. No dependency installation or verification took place.

## Recorded coordinating review of the earlier X3C note

After checkpoint `ac54cf01fe2da11612f765435a3d43b11d4cbd21` was committed, the coordinating assistant hand-reviewed the complete finite X3C normalization and reported a scoped PASS: distinct/in-range filtering, empty/nonmultiple/uncovered cases, harmless duplicate rows, m≥q, and the exact first-cover threshold/equality characterization, including the naive-copy counterexample. That review explicitly did not verify Peters's source, a closed hardness supplier, an operational TM2 adapter, new Lean terms, or bit runtime from incidence counts. It is recorded here with that limitation; no independent review of this new adapter is claimed by that earlier review.

The full original hand all-refinement theorem remains as previously reviewed. Complete-root source acceptance and exact encoded-source hardness remain two independent outstanding obligations.
