# G-program Lean source and assumption frontier

Dedicated Sol6.1 lane, 2026-10-01. This is an incremental formalization and
assumption-audit record, not a claim that the entire G1-G7/CG programme has been
machine verified. New contributions are attributed to this lane; original
Samuel source and Commons hand proofs retain their original attribution.

## Verified new actual-source results

- G5BridgeBarrier: original directed bridge components equal their target's
  directed descendants; the original hybrid child edge is unique by its degree
  rule, and its selected descendant set is exactly its child component
- G5CalendarRoutes: original edge-ID routes exist from original rootedness;
  every downstream route crosses the child bridge; positive original edge
  ages give a unique active population edge; every descendant occupies that
  edge on `[age(child),age(hybrid))`, and outside routes cannot cross it
- G5ProtectiveBlock: for any selected original tips and any actual original
  no-merger route family, the child population's fiber equals the whole selected
  hybrid descendant set. This is stronger than possible pair co-location or
  inclusion in a larger random block
- G7OriginalCensus: original degree rules and original edge identities imply
  `|V|+1=2n+2r` and `|E|+2=2n+3r`. No compressed-core actuator interpretation or
  supplied count identity is assumed
- G1SharedRegisterStress: actual exponential pair holding-time laws at positive
  rates, normalized/nonnegative register-forest kernel, and an exact exposed
  shared-register countercontrol to independent marginal resampling
- G2LiveLineageRouting: actual original hybrid/parent-edge IDs, surjective
  original-copy membership in live ancestors, preservation of merged ancestors,
  and an exact countercontrol to incorrectly re-coining each original copy
- G5MinimalGraphInterface: bridge/descendant equality generalized to every
  rooted acyclic edge-indexed graph without LSA, binarity, finiteV, galledness or
  planarity
- G5CutChildNecessity: explicit four-tip positive-calendar binary LSA source
  demonstrates why child-cut cannot be dropped from the protective-route proof

Each has an actual matching-compiler run, source SHA-256, and explicit axiom log.
The successful logs show only standard Lean axioms, with no placeholders.

## Necessary hypothesis stress test

The accepted G5 older-side convention survives the formal check. Opposite
`(child age,hybrid age]` intervals need not have an earliest point. The accepted
hand proof already states the correct older-side convention. This is not a new
mathematical gap or a promotion of full G5 to machine-verified status.

## Critical unformalized source steps

- G1: actual graph-to-forest-kernel extraction and grafting, retained root blob,
  conditional shared-register composition, source realizability, and decorated
  core bound. The recovered original hand acceptance relay is not an accessible
  complete proof payload. No blocked local payload was copied or used
- G2: original-ID control primitive semantics, all joint rows with one original
  parameter assignment, shared/independent routing over live lineage forests,
  stochastic projection/coupling, and complete calendar response compiler
- G3/G4: current mathematical source boundaries remain explicit; no complete
  final source theorem is inserted as an axiom
- G5: a stochastic coalescent path-law construction must imply the actual route
  representation and positive feasible-route support; then observable frozen
  generators, germ uniqueness, chronological contraction and Q/S assembly must
  be formally connected. The graph/calendar lemma alone is not that connection
- G6/CG2: source-fixed rare insertion, finite Kingman expectation bound,
  all-copy coupling, adaptive stopping/weighted-path lower bounds and resource
  substitution still need a complete formal stochastic source semantics
- G7: the original census is proved, while correlated frontier/forest compiler,
  same-source control laws, quantified policy extraction and optimal frontier
  statements remain unformalized

## Original NANUQ baseline boundary

Exact baseline: Sodelin/Work-on-Samuel-Alexander-Research- commit
e2502c82ab9a77c00543932f775a71e5374221f7. All 117 top-level Lean source files match
the original Git blobs and publication-manifest source hashes. The three
explicit draft/probe exclusions remain excluded.

Fresh rebuilding uses matching Lean 4.33.1 and mathlib commit
0df444a360eaa60ab8c11dca51a86af692955474. The terminal result is 96 of 114 included
modules freshly passed, five finite certificates resource-blocked, and thirteen
dependent modules unchecked. No certificate retry is running. Exact attempt
history, memory_exception logs, successful source hashes and axiom logs are
preserved. See BASELINE-TERMINAL-PARTIAL-RECEIPT.md.

AnchorComposition and CircularComposition still contain explicit biological
graph-composition/contiguous-port hypotheses. CanonicalTheta is a local canonical
shape theorem. Raw source classes do not obtain the missing final theorem by
importing those conditional components. The source theorem and whole G-program
completion remain unclaimed.
