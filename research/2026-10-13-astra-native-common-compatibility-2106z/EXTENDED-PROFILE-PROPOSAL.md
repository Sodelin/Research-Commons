# Isolated six-copy COMMON profile: feasibility and proposed next increment

Status: source-inspected proposal, not implemented or compiled. Contributor:
Astra Rust integration lane, 13 October 2026. The recovered four-copy core and
its authenticated executable remain unchanged.

Four copies is an implementation profile, not a mathematical arity restriction
in the ordinary-population coefficient formula: the existing
`forest::ordinary_path_coefficients` supports 1–64 lineages. The forward DP uses
vectors and exact rational polynomial operations. The current hard bounds occur
in both the RC1 LAW header/sample parser and `law::Request::validate`; the
canonical snapshot `Context::validate` independently caps copies at four.

A constant-only change would not be responsible. `law::routes` materializes
`2^copies` groups for INDEPENDENT routing, and `compile_inner` collects branches
before its STATE/TERM checks. Increasing input limits could therefore allocate
substantial intermediate data before an UNKNOWN result. The recovered source
must not be patched in place, and raising runtime memory limits is not the
proposed fix.

Proposed bounded increment:

1. Derive an isolated, hash-pinned patch against the recovered source. Keep the
   default four-copy parser, compiler and certificate behavior byte-for-byte
   as a regression reference. Factor the same existing parser/DP through an
   explicit profile; do not write another source decoder or polynomial solver.
2. Add an explicit `COMMON6` profile limited to six copies and COMMON inheritance.
   Reject unsupported profile sizes/mechanisms/budgets with an explicit UNKNOWN
   profile result before expansion. A changed profile must be bound into both
   request/certificate checking and execution receipts; a caller flag alone is
   not a mathematical proof.
3. Check branch, kernel, term-product and output budgets before materializing
   each expansion. Use bounded/exact integer counts and checked arithmetic.
   Reuse existing exact coefficient and full-joint DP methods. Conservative
   budget exhaustion is UNKNOWN; do not substitute marginal products or remove
   baseline copies. Keep existing default-profile resource/error behavior.
4. Begin with a supplied small four-taxon source and exactly six labelled
   copies, preserving every baseline and selected copy. Its computed output
   remains a formal native full-joint forward table. The COMMON-menu certificate
   alone does not supply a graph, protected occurrence map or physical parameter
   assignment, so those inputs and their unverified obligations stay explicit.
5. Retain original edge occurrences, hybrid order and parameter identity.
   Reuse the established fitted-bank complement for parent-zero/Gamma when a
   validated mapping is present. Do not change original edge order. Supporting
   joint forced-mask/readout menus remains a separate correspondence step; six
   copies alone does not establish it.

Narrow deterministic checks should cover unchanged ≤4-copy behavior, one full
six-copy COMMON table, exact total mass/nonnegativity at admitted rational
points, the existing ordinary-population coordinate formula where its contract
applies, permuted external labels with explicit bijections, parallel edges and
parent-bit complementing, and early UNKNOWN at deliberately tiny/oversized
budgets. Malformed IDs/graphs and altered request-bound certificates remain
refused. These finite checks are not a native refinement proof.

Only after source review and a free compiler slot should one fresh serial Rust
build run in a new target directory under conservative guard limits. No native
build may overlap the Lean lane. Preserve failed runs and old binaries. A
successful six-copy example would close one executable profile gap; arbitrary
levels, the full 6–17-copy padded menu, source admission and general G3 would
remain open.
