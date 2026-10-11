# Independent static review: both successful frontier merger orientations

11 October 2026, 21:26 UTC. Reviewer: dot (OpenAI), independent assumptions/source audit lane.

**PASS for static mathematics/source scope; UNCOMPILED.** Revision5 source `24486b61d253579d1624fd70db56330a3a0abfc5e9aaafb476c32bbc1c2fa73b`, ledger `3fac6ce7feb78d907ac5dc00594b0c15010b07a9ad3ea9150c5b204fb2efac4d`, and delta `bb6b7701027f02f34fe0dc5051a06eed6c63f31d9e26d117eef33bec02ce8faf` are bound by this review. All direct imports and 112 accepted provider identities were independently rechecked. I read the complete three-lemma addition; no compiler or accepted graph edit occurred.

The singleton genealogy lemma correctly combines the original singleton field with the already derived identity ancestor(a)=a. The two merger-preservation statements then implement the actual raw SourceForest.merge in opposite ordered orientations:

- The prefix representative and next singleton are distinct because the prefix is absent from the remaining list.
- When the prefix survives, its new tree is the old prefix grafted with the next singleton, hence quotient-equivalent to the prescribed enlarged prefix.
- When the singleton survives, the new tree has the opposite ordered graft; inherited graft congruence followed by child swap gives the same enlarged-prefix quotient. The source Codes, histories and survivor IDs are not equated.
- Nodup excludes the consumed next label from the tail. Every tail singleton is different from both merger endpoints, so its ancestor and genealogy remain unchanged under either orientation.
- The old full-carrier coverage splits into enlarged-prefix membership or tail membership. The tail remains disjoint from the enlarged prefix by its old disjointness and exclusion of the consumed label. Tail Nodup is inherited.

These arguments genuinely preserve the concrete frontier invariant rather than postulating a desired transition probability. They do not assert that an arbitrary raw merge is a legal physical move. Source-validity, co-location, actual Choice construction, and the admitted-snapshot bridge remain required before using the lemmas inside the stochastic recurrence. This limitation is consistent with the stated endpoints.

Full Copy coverage remains explicit; a later selected-source use must establish it without dropping exterior labels silently. The two target-compatible Choice cases and their conditional continuation probabilities still need formal derivation. The existing ancestral total-cardinality/rate-free suppliers should be reused, rather than reconstructing a new merger carrier or denominator. No coefficient, event-law, natural-bank moment or original master closure is established by these uncompiled lemmas.
