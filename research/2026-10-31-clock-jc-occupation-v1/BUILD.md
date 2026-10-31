# Reproduction and evidence interpretation

Use the existing Research-Commons package at immutable commit 14be42189b8a72fcaced51ceda4e86445dc09e90, Lean 4.33.1 commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6, and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 with its pinned dependencies. SOURCE-MANIFEST.json lists all 117 unchanged project provider source hashes/imports/build order. Recover them from the package's exact lean/content-addressed vendor sources, not branch-tip substitutes.

Verify every source hash before compiling. Materialize accepted new files with their module paths under an isolated source overlay; preserve inherited sources/objects. Establish LEAN_PATH using exact compatible dependencies and a separate output overlay. Reusing verified objects and rebuilding every dependency fresh are distinct provenance claims. The recorded run reused 117 project providers; no archive-level provenance stronger than the supplied manifest is claimed.

After the exact environment is prepared, the essential new-source order is:

1. ResearchCommons.MSCI.JC69Occupation
2. ResearchCommons.MSCI.JC69CurrentPartition
3. ResearchCommons.MSCI.JC69TraceOccupation

For each module, create its output directory and run the pinned compiler, e.g.:

```sh
lean -j1 -M6144 -Ddebug.skipKernelTC=false --root="$SOURCE_ROOT" \
  -o "$OUTPUT_ROOT/ResearchCommons/MSCI/JC69Occupation.olean" \
  "$SOURCE_ROOT/ResearchCommons/MSCI/JC69Occupation.lean"
# Repeat for CurrentPartition and TraceOccupation in that order.
LEAN_PATH="$OUTPUT_ROOT:$LEAN_PATH" lean audit/NamedAudit.lean
LEAN_PATH="$OUTPUT_ROOT:$LEAN_PATH" lean audit/OwnedAudit.portable.lean
```

Ensure OUTPUT_ROOT is on LEAN_PATH for downstream compilation. The portable owned audit differs from the historical executed file only in writing OwnedAudit.json relative to the current working directory. It has not been separately rerun here. Original hash and exact edit are recorded in REDACTIONS.json. No audit/type-check logic was changed.

Record stdout/stderr, exit codes, exact source/object hashes and imported-provider identities. Check full theorem types and axiom sets, not just theorem names or object-file presence. Reject sorryAx, owned axioms, nonstandard axiom rows or missing selected modules. No dependency installation, external job or whole-package rebuild is performed by this packet.

## Recorded chronology

- Frozen original source failed elaboration; INITIAL-FAILED-compile-result.json and FAILED diagnostic logs are historical failures. They may contain compiler-generated sorryAx output from rejected attempts; this is not accepted evidence.
- The supplied patch adds only proof elaboration repairs and equivalent ENNReal type spelling. Definitions, hypotheses, source objects and conclusions are unchanged.
- CURRENT repaired sources passed the later named and owned audits. Exact reconstructed source equality, all 117 provider hashes and both scope/target sets were checked independently of the execution report.
- A separate AI-assisted read-only review checked repair semantics and receipt binding without another build. This is not independent human peer review or fresh kernel replay.

The three repaired hashes, not the failed inputs or later draft extensions, delimit this result.
