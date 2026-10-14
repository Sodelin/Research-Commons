# Source-reviewed handoff; no full query executed

Root authenticated the full source/header inventory and read the complete query
and capture successors. The Rust lane independently reviewed the source paths,
all eleven Mathlib routing checks, core Std/Lake handling and literal3593 prefix.
The capture's initial absent-scratch failure was repaired without changing the
query runner, selected bodies, active plan or limits. Original capture bytes and
the exact repair diff remain in this packet. No actual query, capture or theorem
elaboration has run for this packet.

The compiler owner may choose one finite source-query profile in a quiet window,
after preserving the existing build checkpoint. The packet does not launch a
process itself. Keep the existing4GiB physical stop,8GiB disk floor and1GiB RAM
floor; choose finite CPU/wall/address-space/file limits within the reviewed
ceilings. A conservative candidate is240 seconds wall,180 CPU seconds,512MiB
address space and16MiB per file. These are a proposed profile, not an execution
receipt or a requirement to increase any existing limit.

Before execution, create `RUN-CONFIG.json` with schema
`astra_full_query_capture_run_config_v1`, the exact query SHA, fresh canonical
scratch path, guarded/output sibling paths under this packet's `evidence`, exact
child command, working directory and all seven limits. Supply its literal SHA
to the eventual capture command. `capture_query.py` defines the exact accepted
keys; no run configuration has been created here and no successful outcome is
preselected. Guard the query with the pinned existing guard, one process at a
time. Capture only the actual closed result using that unchanged configuration.

Successful capture authenticates every request/source/env/receipt/import path,
all eleven original/materialized/upstream source routes, the old source-query
prefix and the actual new DFS preorder/postorder. Additional transitive count is
derived from the recorded walk. Missing/extra data, changed source, budget
exhaustion, stop or failure cannot establish closure. An absent scratch directory
preserves the closed guard/configuration evidence as UNVERIFIED; its presence
or absence does not imply query execution. Unexpected paths/symlinks or exceeded
capture budgets fail closed with the original inputs retained.

Actual source-query success would still be distinct from component compilation,
object reuse authentication, final Lake target execution, theorem-type/axiom
audit and verified publication. The current319/3591 build remains unchanged.
This handoff supplies no physical representative, native correctness proof or
arbitrary-input G3 closure.
