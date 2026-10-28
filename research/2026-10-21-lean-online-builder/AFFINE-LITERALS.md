# Six exact authored affine certificates

All SIX exact authored source bodies at Rust source commit
c4d82e7357b0276cedc93ed6e7d336b7d06b7923 passed the existing hosted Lean check,
unchanged. This is actual checking of those literal sources, not just reuse
of the earlier generic receiver result.

The cases are a strict interval, strict contradiction, the feasible system
whose strict row has zero exclusion multiplier, weak negative-bound exclusion,
duplicate rows on two shared coordinates, and EMPTY Fin0 with zero rows.
Each has value_checked plus its original_rows_hold or
original_rows_infeasible endpoint. All twelve selected complete types and
standard-axiom dispositions are in CHECKED-FOLLOWONS.json, case
affine_literal_certificates. AFFINE-LITERAL-SOURCE-MAP.json pins every exact
standalone source and its two names, plus the combined source identity.

The37997B virtual document, SHA256
f53cc55980257d7f57352e760def69b20d4c62dcf222f3d9cc9c9bd2c70b0ccf,
contains unchanged StrictAffineElimination, G6RationalAffineWitness, the exact
previously checked corrected receiver and all six unchanged literal bodies.
Local imports are removed, external imports hoisted; the complete proof/body
sequence is unchanged. All declarations elaborate, only those twelve have
selected printed audits.

Actual context is Lean4.35.0/mathlib56a005. Selected audits use only
propext/Classical.choice/Quot.sound, no errors. Inherited deprecation and unused
section/simp warnings remain. The empty Fin0 proof also has harmless unreachable
tactic warnings after fin_cases closes its impossible index. No warning was
converted into a sorry or an unsafe acceptance.

These remain AUTHORED EXPECTED sources. The new Python codec/emitter, eight
altered-input refusals, UNKNOWN/budget/runtime binding controls and native
execution are UNEXECUTED under their existing hold. Request/certificate hashes
in Lean comments do not authenticate transport or prove a parser/emitter's
correctness. No native refinement, pinned Lake/object custody, physical cell
row admission or unrestricted source exclusion is inferred.
