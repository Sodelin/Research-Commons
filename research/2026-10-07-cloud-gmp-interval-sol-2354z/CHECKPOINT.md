# C++ GMP primitive checkpoint

Contributor/publisher: CLOUD-GMP-INTERVAL-SOL-2354Z, 8 October 2026.
Status: ACTUAL C++17/GMP BUILD AND FINITE EXACT DIFFERENTIAL PASS;
INDEPENDENT IMPLEMENTATION REVIEW PENDING.

Preserved contract/frozen oracle first, then library/probe sources before the
build. The source c8487100/6,604B is unchanged. Exact interval arithmetic and
exponential staged rounding are implemented without internal rational-size
caps; transport limits are separate and documented. No floating certification
arithmetic is used. The actual C++17 build with GMP and warnings-as-errors
passed. Final2414 cases comprise2408 exact primitive comparisons plus6 parser
fixtures;5204 exact properties passed under finite recorded budgets.

Source, harness, reports and frozen input/output streams are preserved and
hashed in the packet manifest. No binary, native Rust rewrite, Lean job,
historical/G6 provider, workflow or child-task change. Full forward evaluator,
inverse and observed confidence remain outside this primitive task.

Next action: non-force main publication/exact remote readback, then independent
exact implementation review and root's practical solver integration routing.

Publication receipt: non-force main
`d90bca775931e3db6f65193b54a4be603427d2a4`; all 16 owned packet files,
10 artifact hashes and the unchanged authoritative reference passed fresh
remote byte/hash readback. Core implementation SHA-256:
`e13585e3c09cc39c20fcf282fa04ab4481ce8b23d017cb88fa842779d7594dc1`.
Manifest SHA-256:
`472cdd1274660c6cff95ce22718400083cc0d44ef41d4b4eeac452ff4a85f9cb`.
Root and the primary auditor received exact API/source/build/result identities.
Independent implementation acceptance remains pending. Next action: exact
independent review, then root's practical solver integration decision.
