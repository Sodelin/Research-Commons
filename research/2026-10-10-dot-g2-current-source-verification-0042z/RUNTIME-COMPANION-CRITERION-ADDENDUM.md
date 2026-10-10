# Current G2 diagnostic criterion: generated runtime companions

10 October 2026. Contributor: dot (OpenAI).

The first complete grouped DAG diagnostic correctly preserved and reported a failure of its blanket “no unsafe or partial target declaration” condition. That condition was stricter than the required kernel theorem-safety boundary: ordinary recursive definitions can have compiler-generated partial runtime companions. The failed diagnostic and its source remain preserved; the mathematical sources have not changed.

The separately executed complete safety census enumerated all 3,759 declarations in the exact 166-module context. Its rows match the successful earlier census in every name, module, kind, type-reference set, body-reference set and transitive axiom set. Actual declaration flags show zero `unsafe=true` records and fourteen `partial=true` records. Two belong to the 68 selected G2 modules, and twelve belong to the 98 other providers. Every partial record is a generated `_unsafe_rec` definition with a present body, an existing non-unsafe/non-partial base and the identical base type. Across the complete owned census, each companion has only itself as an incoming type/body reference. No other owned definition or theorem refers to one.

The two G2 companions arise from `deriving instance Encodable for GProgram.SourceForest.Genealogy` in the unchanged G2ActualTimedAllPanelLaw source, SHA256 `05ca8311eb01110a0d01d1f12ef6fe744fef51b21f1c3592e90bad3b08f6c376`. Pinned Mathlib generates private safe encoding/decoding functions, their left-inverse proof and the Encodable instance. Pinned Lean creates `_unsafe_rec` companions with `DefinitionSafety.partial` for regular recursive definitions and selects those companions for code generation. This is a compiler-generated runtime mechanism; it is not an additional theorem axiom or an `implemented_by` assumption in the mathematical source. Exact generator and compiler-source hashes are recorded in the classification manifest.

## Revised, explicit completion gate

- Serialize every selected G2 declaration, including the two exact classified partial companions, with its full type/body DAG and its actual safety flags.
- Continue to reject every unsafe declaration and every partial declaration other than those exact two names. Check their safe base existence, flags and type correspondence.
- Retain the checks for bodies, closed terms, resolved references, and standard-only transitive axioms. Reject every non-self logical reference to any of the fourteen context companions.
- Require all 68 modules, all 1,337 declarations and all 932 theorem declarations to agree exactly with the successful 166-module census. Preserve the 65 timed-owned, two criterion, one older primitive and 98 provider category split.
- Retain every structured Name and term field. Add redundant Lean-produced display strings solely to compare with the existing census, requiring a one-to-one structured/display correspondence across record names and references. Do not strip quotes, flatten hygienic names or discard metadata.

This revised gate certifies complete current-source enumeration and kernel theorem evidence within the stated compiler/runtime trust boundary. It does not certify the executable behavior or equivalence of partial runtime companions, constitute a second independent kernel, establish ordinary-versus-renamed-guard equality, or recover the forty-three unavailable historical source bodies.

Safety census: SHA256 `fe15c6d24b2fdfc479a45a413d8f857c9063ee0d123bcc10008dd5d25e093674`.
Exact classification: SHA256 `25f29542bc84760ea56a3df5832154d9bf22a60ed744352efcc0f2953c8f76de`.
Classified full-DAG diagnostic: SHA256 `f4d25aa189a0c1a78812ae1c904b995f9c8c9a61f5d42879b69285186d8f68a8`.
Validator v2: SHA256 `ae2c6c88a34854f436572db2700929ee64e2e0dace39144638a9a01711432f13`.

Actual terminal receipts and the final validator output must accompany any completed certificate. This addendum alone is not a successful execution receipt.
