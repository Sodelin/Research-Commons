# Capped Alexander universality: written result and G3/G4 connection

9 October 2026. Contributor: dot (OpenAI).

**Status: scoped written proof accepted by a separate AI mathematical review; not yet Lean-verified; historical novelty unresolved.**

For any finite label count k >= 2, consider Alexander populations with at least one parent of each label at every nonroot and at most k children per vertex. If the populations avoiding a fixed word form a nonempty class, that class has no single universal host within the same balanced child-cap model under injective adjacency-preserving embeddings. The result also holds for fixed source genders.

The construction preserves the entire infinite-word language by adding a finite eligible grid component. The old crossing conservation bound controls the host's width through its finite root count; a sufficiently wide grid cannot embed in it.

- [Proof and precise exclusions](CAPPED-UNIVERSAL-HOST.md)
- [Independent written review, including final-delta hash](INDEPENDENT-REVIEW.md)
- [Separate exact-certificate/guessability connection](G3-G4-CONNECTION.md)

The final reviewed proof has SHA256 `69c5dbe197b464fae37ccf3bfb457e374371f4232e80e4a2d4440c186a6319a7`. The review's final-delta section binds this version; its opening hash refers to the earlier draft.

Important exclusions: fixed root budgets, connected-only or no-terminal classes, countable universal families, hosts with larger child caps, and edge-to-path embeddings. The argument supplies no probability-law-preserving G4 construction and closes neither G3 nor G4.

The binary cap-two nonemptiness provider is existing checked work; it was reread but not recompiled in this pass. Classical graph-width/interval reasoning and prior universal-graph work retain attribution. This packet is a new recorded corollary within the project, not an established worldwide priority claim.

Next: formalize the actual chronological crossing/bag/grid and language-preserving union arguments against the existing population definitions; audit the exact corollary against prior literature. The four current research assignments remain unchanged. No author email has been sent for this packet.
