# Rust solver pilot: authorized staged integration

Date: 2026-10-07 23:15 UTC. Contributor: dot.

Nolan has authorized starting the staged best-language solver integration discussed today. This is a bounded new execution-layer pilot, not a replacement of accepted mathematics or a change to G3/G4 scope.

## Ownership and boundary

Dot owns a new isolated Rust count-certificate library and CLI pilot, differential/adversarial testing against the immutable Python reference, and independent review. Reference: `research/2026-10-07-cloud-g6-sol-ultra-1601z/count_certificate.py` at `c9a6934ecb09ea22dc0204def2ad6398dfb43fa2`.

No existing source, shared provider, Lean package, workflow, or production default will be changed by this pilot. Cloud retains current formal/source integration, practical receiver work and sole Lean compilation. Please report an existing overlapping Rust pilot before duplicating it. The broader architecture is Rust-owned contracts/runtime with specialized mathematical backends where justified; it does not require rewriting established numerical/CAS libraries.

## Acceptance gates

Preserve exact rational arithmetic, first qualifying cutoff, normalized-prefix versus residual-lumped distinction, outputs and resource-limit semantics. Freeze reference bytes and exact inputs. Test malformed inputs and boundaries, compare complete outputs, and independently check mathematics. Release-mode performance is measured only after semantic validation; no speedup is presently claimed. Existing Lean certificates do not transfer automatically to the new executable.

## Current status and request

Design completed; implementation launched in a separate owned location. No Rust build or benchmark is yet verified. Request coordination on an available isolated Rust execution route after the source packet is ready; do not interrupt or duplicate the active Lean run. Source-only work can proceed without a build claim. New tooling/permissions are being handled separately and are not implied by this public checkpoint.

Public/private data boundaries remain unchanged. Only public-safe source and evidence may enter this repository. General G3/G4 and full practical solver endpoints remain open.
