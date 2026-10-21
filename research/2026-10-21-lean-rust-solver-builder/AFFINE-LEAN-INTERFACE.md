# Request-bound AFFINE value projection and literal proof source

SOURCE ONLY. Neither new Python module nor the six authored expected sources
has run/been checked. The existing Rust engine, parser and native_rc1 runtime
entrypoint are reused and unchanged. No workflow is enabled.

affine_codec.request/decode accepts complete ORIGINAL RC1 AFFINE request and
certificate bytes. The transport projection follows the retained protocol:
printable ASCII, canonical single spaces/naturals/reduced p/q, dimensions<=8,
rows<=64, projection cap<=4096, request<=65536 bytes, certificate<=4MiB and
original raw256-bit rational inputs. The extra adapter arithmetic budget is
2048 bits: decode/bind raise Budget on exhaustion; render maps it to UNKNOWN.
It never becomes exclusion or a restriction on the original native engine.

SAT checks every ordered original row and reported evaluation. UNSAT checks
nonnegative original-row multipliers, zero combined coefficients and the
negative-bound/positive-strict-multiplier condition, plus BOUND/STRICT.
UNKNOWN stays a non-certificate. This is an exact value checker, not another
elimination solver or a native parser/refinement proof.

emit_affine_lean.render(request_literal, certificate_literal, *, checker)
prepares standalone source against the exact checked receiver hash
62d4569e436aadb3202118a818c0ed7635c27a54b8e39b27a1e23188d80b5fc6.
It emits the supplied finite Row bank and witness or multipliers, then uses
the existing receiver for the real-matrix conclusion. Source over256KiB stays
UNKNOWN. Metadata binds both literal byte hashes, dimension, ordered row count,
source hash and required receiver hash. A required hash does not authenticate
an installed import or act as a mathematical equality premise.

affine_codec.bind_checked_return additionally binds the complete ORIGINAL
unified_research_solver_v1/native_rc1 envelope and runtime return, including
literal/canonical identities, exact RC1 request/certificate, original native
binary/manifest, completed independent native check and unchanged finite scope.
Supply the real externally authenticated runtime/MCP return. This PURE function
does not authenticate a caller dictionary's origin. It retains the complete
original return; the caller must also preserve it when binding refuses or
exhausts budget. An original UNKNOWN/refusal cannot be relabelled as success.

Use the hash-authenticated original certificates.py helpers from
codec.original_checker. Both new modules are pure RAM interfaces with no
process, solver, CLI, compiler, file writer, network or implicit logging.
The caller's existing encrypted sink must protect runtime source/metadata
BEFORE their first file/database/temp persistence. Later reviewed source
publication does not authorize plaintext raw records.

fixtures/affine-literals.json contains six AUTHORED certificates: strict interval,
strict contradiction, feasible zero-weight-strict control, weak negative bound,
duplicate rows/two shared coordinates and empty Fin0. The six Lean bodies are
authored expected bytes, not claimed Python outputs or native executions.
Eight refusals, one UNKNOWN and later binding/budget controls are staged but
UNEXECUTED. Exact hashes/names are in
evidence/AFFINE-LITERAL-SOURCE-PREPARATION.json.

Remaining: actual Python/codec byte equality and falsification under the real
writer binding, exact authored-source hosted checking, pinned module/object
acceptance, native refinement, physical row/chart/provider correspondence and
full master assembly. No new task/CHART admission, physical YES, all-size NO,
profile adoption, old-job replay or privacy-owner retry is supplied.
