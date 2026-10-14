# Supplemental library ownership clarification

Source-only correction to the initial Lake hook. The original six payloads and `PACKET-MANIFEST.json` (`4694e7bf…`) remain byte-for-byte preserved. The mathematical source is still `48b26222…`; no proof or declaration changed.

Use `lakefile.addendum-v2.txt` **instead of** the original `lakefile.addendum.txt` in any future selected configuration. It explicitly sets `srcDir := "."` and owns exactly `Astra.CertifiedCommonExternal` and `AstraCertifiedCommonExternalIntegration` with `.one` globs. The aggregate remains the supplemental root. This prevents relying on an implicit owner for the non-root wrapper or attributing it to an existing Astra library.

The proposed source stage is a new sibling of the canonical 0600 materialization, with all canonical source/configuration bytes preserved before the authorized additive configuration change. Copy these two packet files, stripping only their leading `lean/`:

- `lean/Astra/CertifiedCommonExternal.lean` → `<stage>/Astra/CertifiedCommonExternal.lean`.
- `lean/AstraCertifiedCommonExternalIntegration.lean` → `<stage>/AstraCertifiedCommonExternalIntegration.lean`.

The staged canonical `lakefile.lean` remains at `<stage>/lakefile.lean`; the v2 fragment is appended once to that selected successor configuration. Do not add both fragments. Preserve every old target/default, dependency pin, explicit ownership glob and existing source. The supplemental aggregate imports the unchanged `AstraCertifiedCommonIntegration`, whose earlier libraries continue to own its dependencies.

Static inspection of the pinned canonical configuration found no existing ownership of either new module, and its older libraries use explicit `.one` lists. This is source-level configuration review, not Lake's actual import/ownership query. No stage, selected configuration, runner, existing plan or namespace was mutated here. Materialization, configuration/import queries, compiler/Lake execution and type/axiom audit remain pending under the owner.
