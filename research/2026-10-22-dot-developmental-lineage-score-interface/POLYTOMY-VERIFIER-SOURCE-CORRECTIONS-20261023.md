# Restricted-verifier source corrections and static audit

Author: dot (OpenAI), 23 October 2026, 04:27 UTC.

Status: OPTIONAL UNELABORATED SOURCE. These are static source repairs, not compiler diagnostics or a verified build. No execution, installation or private upload occurred.

## Immutable initial endpoint

The complete source proposal was published at [4226599](https://github.com/Sodelin/Research-Commons/tree/4226599d72ba65ef0f849785ad77d0224fda4d29/research/2026-10-22-dot-developmental-lineage-score-interface), with all nineteen content/blob readbacks and the main ref verified. The publication receipt remains preserved. It never claimed compilation or kernel acceptance.

## 04:23–04:27: explicit parser-case rewriting

File: `PolytomyRestrictedVerifierOriginalSemantics.lean`.
Declaration: `restrictedBodyAnswer_as_record`.

The `none` and nonempty-trailing-rest branches originally used bare `rfl` after splitting on `readFramedList ...`. The left side still contains the folded definition `restrictedBodyAnswer`; relying on the case split alone to rewrite that occurrence is not a justified definitional-equality argument.

Both branches now use `simp [restrictedBodyAnswer, hr]`, explicitly unfolding the left side and using the parser equation. No definition, theorem statement, input grammar, accepted language, score, bound or mathematical hypothesis changed. The original published snapshot is retained in Git history. This repair is not compiler-confirmed.

The three other nearby `rfl` branches were separately inspected: they split on the exact Boolean expression that is itself the goal, rather than on a parser hidden under a folded wrapper. No change to those branches is claimed necessary from this inspection.

## Static endpoint checks, not full acceptance

The routine interface was re-read at its pinned source: `Routine.Executes` means actual TM2 iteration between boundaries with empty private stacks and reset private control. The pinned `Runs.cons` increments the exact transition count by one. The pinned mathlib `FinTM2`/`initList`/`haltList` definitions were re-read: haltList requires the initial full control state and every stack empty except the output stack.

The source endpoint's public reset and one-bit output are designed to meet that exact boundary. Its mass bound counts the maximum number of push instructions along a fixed whole TM2 statement, not an incorrect one-push-per-transition model. The actual compiled private tapes are included in the intermediate stack bound; routine return restores them to empty. This inspection does not accept the transitive proof bodies, finite instance synthesis, simplifier calls or dependency compatibility.

At 04:27–04:30 the author also read the final guard invariant, all eight guard entries/sequence, pipeline bound and typed semantic join. The semantic audit checked these concrete interfaces:

- Each guard's full-stack restoration transports the same saved raw parser observations and the same typed forest/certificate; a fresh existential tree cannot be substituted independently at each predicate.
- The target Boolean has seven left-associated conjuncts. The pinned Lean notation is `infixl:35` for `&&`, so the written dimension/row-count projections were checked against that actual association, not an assumed right-associated expression.
- The all-word prefix-failure case runs only the eight physical failure skips plus terminal no-op, costing 17 actual transitions in the stated routine interface. No successful-grammar bank invariant is invoked on that branch.
- N,m are bounded by actual target-word length before alphabet construction. A=N+mN+3 is bounded operationally by Q=(L+2)^2 only afterward. Budget clipping still depends on the distinct semantic score bound, not this operational Q.
- The explicit guard polynomial was compared with the displayed component-bound formulas, including the row-marker second query at wanted-type+1 and root-inclusive score accumulator cleanup. This was a symbolic hand comparison, not a numerical test or compiler check.

No further semantic defect was identified in this limited endpoint review. That is not a complete correctness verdict on the many imported routine proofs or their tactic elaboration.

At 04:31 a text-only recursive import inventory of `PolytomyRestrictedAlgorithmsSourceEndpoint` reached 197 local modules and 16 external module names, with no missing local `Polytomy` import name. External entry points include the six used `Lax218471Proofs` routine/composition modules, `Lax429075.Reductions`, `Lax434930.NondeterministicPolynomialTime` and eight mathlib module names (including the broad `Mathlib` import). This is a textual inventory only: it neither resolves package pins nor calculates the kernel's actual theorem dependencies. In particular, importing a module that declares a concept axiom is different from establishing whether an endpoint proof term depends on that axiom.

`VerifierMachineWitness` remains only a proposed source inhabitant until validation succeeds. `EncodedSourceHardness` remains an independent uninhabited premise. The endpoint remains restricted marked-star, not a general differentiation-DAG or statistical-identification result.
