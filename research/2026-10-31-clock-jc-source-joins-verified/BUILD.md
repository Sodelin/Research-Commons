# Reproduction boundary

Use Lean 4.33.1 commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474 with its pinned dependencies. Recover the original selected project source closure at 14be42189b8a72fcaced51ceda4e86445dc09e90 and exact accepted occupation providers from c2c441886886e7fc1fe10a495ec081453c4b5c8e. Verify all 120 source identities in evidence/provider-context.json. Do not silently substitute unrelated cached objects.

In an isolated exact-context project, put the four lean/ sources at their module paths. Build BoundaryOccupation, CalendarOccupation, WeightedTrace, EndpointWeight in that order using the pinned Lean compiler and existing project/dependency search path. Then run audit/NamedAudit.lean and audit/OwnedAudit.portable.lean with the same environment. The latter writes OwnedAudit.json in the working directory. Compare source hashes, nineteen named types/axioms, the exact124 selected module set and rejection lists against evidence/. Compilation commands are reproduction instructions, not another claimed local execution.

Full exact source/object identities and failure history are retained. The provided archive is evidence, not a bundled installation or provenance certification for all historical dependency objects.
