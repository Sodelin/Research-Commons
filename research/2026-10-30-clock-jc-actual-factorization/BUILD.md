# Reproduction and evidence interpretation

## Prepare exact dependencies

Use Research-Commons at commit14be42189b8a72fcaced51ceda4e86445dc09e90, its packages/research source preparation, source-lock.json and pinned Lean/Mathlib/Lake dependencies. Materialize the170 selected project modules listed in SOURCE-MANIFEST.json using their original content-addressed vendor sources and package lean sources. Verify each SHA256 before compilation. This packet is not a standalone copy of Mathlib or the whole dependency tree.

Add the exact repaired file at packages/research/lean/ResearchCommons/MSCI/JC69Factorization.lean (or an isolated source overlay with that module path). Do not replace any inherited sources. Use an output overlay separate from sources and inherited objects. Build dependencies in their selected import order, with the exact pinned toolchain, or validate pre-existing compatible object receipts explicitly. Provider-object reuse and an all-fresh provider build are different provenance claims.

Once the dependency LEAN_PATH is established, the essential commands are:

```sh
lean -j1 -M6144 -Ddebug.skipKernelTC=false --root="$SOURCE_ROOT" \
  -o "$OUTPUT_ROOT/ResearchCommons/MSCI/JC69Factorization.olean" \
  "$SOURCE_ROOT/ResearchCommons/MSCI/JC69Factorization.lean"
LEAN_PATH="$OUTPUT_ROOT:$LEAN_PATH" lean audit/NamedAudit.lean
sed 's|/workspace/tooling-delivery/setup/jc-candidate/owned-audit.json|owned-audit.json|' \
  audit/OwnedAudit.lean > OwnedAudit.portable.lean
LEAN_PATH="$OUTPUT_ROOT:$LEAN_PATH" lean OwnedAudit.portable.lean
```

Create output parent directories first. Run the owned audit in an isolated writable working directory; the command above changes only its historical absolute output filename to a local file. The original audit source is preserved; no proof/type-check logic changes. Record stdout, stderr, exit codes, source hashes, provider identities and object hashes. Do not infer success from a generated object after compiler failure. Check the ten full types and axiom sets, not only names. Reject owned axioms, sorryAx, nonstandard axiom rows and missing modules.

The original execution scripts under history/ preserve the actual environment-specific commands, not a portable one-command installer. They refer to historical runtime directories and should not be blindly executed elsewhere. No tool installation or external job launch is part of this packet.

## Recorded sequence

1. Exact original candidate2287f3dc… failed with singleton type inference and lintegral rewrite elaboration errors. compile-context-results.json retains all44 attempted entries (43 dependency successes and candidate failure).
2. factorization-repaired.patch supplies source130d71ba… with those elaboration repairs.
3. recheck.log records the repaired module's warnings and standard axiom output; SCOPED-CANDIDATE-RESULT.json records its acceptance and exact hash.
4. audit-execution.json records named/owned audit exits0. NamedAudit.log prints all ten types/axioms. owned-audit.json.gz retains all3986 declaration records.
5. A separate AI-assisted read-only review reconstructed the repaired bytes and checked source semantics against the exact types and receipts. This did not rerun compilation or constitute human expert peer review.

The stale source/manifests in the original exported bundle are retained only as history. The top-level SOURCE-MANIFEST.json and source under lean/ bind the repaired accepted version.
