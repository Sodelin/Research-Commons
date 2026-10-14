# Distinction-preserving Lean extension: exact owner handoff

Packet ID: `codex-g4-algebraic-jet-review-20261014-0706z`.
Authority: Nolan's continuing research/Commons authorization and explicit
instruction to put the supplied deductions in Lean.
Sender: Codex G4 lead. Recipient: existing Lean/Rust integration owner.
Scope: one additive module and its audit. No new compiler/device operator.

## Frozen sources and dependency

- New `G4DistinctMargin.lean`, SHA256
  `b1ed53000accd9de2edb31a452f5473e9606ceb8b0e856bce6544dba4896f710`.
- Sole direct import: `G4StrictMargin`, frozen SHA256
  `a78e639389a08a5d9ab384956d82d4f650cc23842208dde2b978b4a8fcc5fdb4` at
  `1361cd7fbd7bcfa2f13409578cefb0d368485084`,
  [canonical predecessor source](../2026-10-14-codex-g4-astra-review-0630z/lean/G4StrictMargin.lean).
- The predecessor import closure and intended Lean 4.33.1/Mathlib reference
  remain in its own source inventory. It has not yet acquired a new compiled
  acceptance receipt in this authoring lane.

The endpoint is
`G4DistinctMargin.eventually_exists_strict_distinct_zero_of_order_gap`.
It derives `exists z, F(z)=0 and StrictCube(z) and h(z)!=0` on one tuple
below a positive cutoff when `max(r,s)*R<q`. Scaling the original radius
bound gives `(L*e)^R <= (L^R*C)*residual`; separate power comparisons preserve
the domain and value margins. The nearby zero is selected only once.

The five declarations and their type/axiom requests are listed in the
source inventory and audit file. External error/nearest-zero/value-error
inputs are premises, not custom axioms. Strictness and corrected-value
nonvanishing are not fields of the input witness.

## Exact execution request

1. Select and authenticate this immutable packet and its predecessor hashes.
2. Resolve `G4StrictMargin` to the canonical frozen module; do not substitute
   a similarly named later file. Preserve the existing selected sources,
   Lake defaults, active serial job and resource gates.
3. When your source-adoption gate allows, select the two new own files and
   their exact dependency closure in a fresh additive selection. The
   `lake-appendix.txt` fragment is an unapplied proposal; it assumes the
   predecessor library is selected and owns its module.
4. Proposed scoped target after adoption: `lake build CodexG4DistinctMargin`.
   Compile the new source and `G4DistinctMarginAudit` under the existing
   supervisor. Preserve actual commands, source/object identities, stdout,
   stderr, exit and every failure/repair. No blanket parent rebuild or
   dependency update is requested.
5. Return full explicit/universe-aware theorem types and axiom prints for all
   five declarations. Source directives are not observed outputs. Any repaired
   source requires a new hash, review and subsequent receipt.

No local Lean/Lake executable is available in the author's inspected toolchain
locations. This packet is therefore **SOURCE AUTHORED / UNCOMPILED** and awaits
owner adoption and actual compile/type/axiom results. No selected graph or
compiler command was changed here. Reply on the existing
[Commons issue](https://github.com/Sodelin/Research-Commons/issues/1).

## Applicability that a compile pass would not establish

The entire algebraic-jet equivalence additionally uses ordered-ring transfer,
Nash selection, Taylor approximation and primitive-element representation.
Those classical providers are hand reviewed but not formalized by this module.
Actual physical residual completeness, legal observation binding of `h`,
source admission and successful jets at every cap remain separate duties.
A compile pass of this conditional consequence would not close G4 or prove
the reference checker universally correct. Astra retains its full original
quantified proof attack; this authoring task does not redirect it to another
conditional bridge.
