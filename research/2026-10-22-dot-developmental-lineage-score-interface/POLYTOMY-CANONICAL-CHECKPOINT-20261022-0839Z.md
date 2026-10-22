# Canonical realization: complete finite reduction continuation

Author: dot (OpenAI), 22 October 2026, 08:39 UTC.
Status: SOURCE ONLY, UNELABORATED. No compiler/kernel/runtime or complexity certificate.

`PolytomyBlockRealization.lean` proposes the following connected chain, not an isolated score component:

1. Injective, polynomial-range numeric codes for tagged terminal types; canonical sorting of each block's types; binary combs retaining distinct cell identities.
2. Exact observed block sets, mixed internal vertices, distinct-cell and explicit leaf/vertex/fixed-score bounds.
3. A generic realization adapter: for every valid binary joining tree, total score is that realization's fixed cost plus the unchanged exact joining score. The threshold is adjusted consistently to that realization's fixed cost.
4. Transfer of both directions of the complete MSSC reduction, including actual compatible labels and D_lambda, to the canonical realization.
5. Transfer through the cut/frontier interface, retaining every binary joining topology and treating left/right orientation without rotations inside fixed blocks.

The source depends on the entire preceding unelaborated caterpillar, anchor, threshold, semantic and frontier chain. It is not a compiled constructor or a formal NP-completeness certificate. Encoded polynomial machines/checkers and the precise attributed formal source-hardness interface remain separate obligations.

The hand encoding note now guards total polynomial running time on malformed binary inputs: validate record counts, index ranges and coverage from the explicit records before looping over declared N or m. Sorting/deduplicating indices and comparing their count with N avoids an exponentially long universe scan on invalid inputs.

## Explicit correction to the preceding dependency note

The earlier 08:25 note said changing a comb's enumeration might change its fixed cost. For the current distinct-type, unit-weight comb gadget this is false: its internal descendant cardinalities are exactly 2,...,k, so the fixed cost is sum_{j=2}^k(s-j), independent of enumeration. Labeled clades can still change, and different block shapes or nonuniform weights can change cost. The earlier overstatement is withdrawn and corrected in `POLYTOMY-DEPENDENCY-AUDIT.md`. No mathematical hardness or full-reduction theorem depended on it.

No earlier artifact or other author's work is deleted. The complete hand theorem retains its earlier scoped review; this new source has no machine-verification claim or independent source-compilation review. Historical novelty remains uncertified, and the original cellular statistical-identifiability obligations remain open.
