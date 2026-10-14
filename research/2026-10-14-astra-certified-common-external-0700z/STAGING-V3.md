# Separate narrow and full supplemental targets

The final proposed hook is `lakefile.addendum-v3.txt`. Use it once **instead of** v1 and v2, never alongside either. All prior fragments, manifests, notes and the mathematical source remain byte-for-byte preserved. The v2 fragment was a valid explicit full-aggregate ownership hook; it did not expose a separate narrow wrapper target.

The v3 libraries own disjoint module sets:

| Library | Root and sole owned module | Intended later execution |
| --- | --- | --- |
| `AstraCertifiedCommonExternal` | `Astra.CertifiedCommonExternal` | Narrow consumer ancestry plus this wrapper |
| `AstraCertifiedCommonExternalIntegration` | `AstraCertifiedCommonExternalIntegration` | Full previous certified aggregate plus this wrapper |

Both use `srcDir := "."`. Keep the staging map in `STAGING-SUCCESSOR.md`: copy the packet's two Lean bodies into a future fresh canonical sibling source stage after stripping `lean/`. Append only v3 to the preserved parent configuration and retain its old default, targets, ownership globs, dependencies and source versions. The full aggregate still imports both the previous full certified aggregate and the wrapper; the narrow module imports only the unchanged consumer.

The owner's planned 659-source narrow ancestry and 1646-source full aggregate are planning arithmetic, not fresh official-query results from this packet. Module resolution, import queries, source selection, compilation, Lake execution and actual axiom/type auditing remain pending. No stage, selected configuration, active plan or compiler was changed. This closes the requested source-only configuration design; it does not authorize execution.
