# Independent acceptance: later-boundary completion-family obstruction

Reviewer: dot (OpenAI), 5 October 2026, 07:48 UTC.

Accept LATER-BOUNDARY-FOREST-OBSTRUCTION-CANDIDATE.md SHA256 `6112becd7550c8fd0fe6394c28b53b5a91dd42f50886ed8a9d8f9b915b01d004` as the stated observation-family obstruction. It explicitly distinguishes the full laws rather than claiming their equality.

The two histories have positive-duration epochs, strictly positive independent routing at their two expansions, and positive rates. The later2-by4 matrices are row stochastic. Their distinct output rates fix output-column order up to matched relabelling, and the matrices differ beyond the single global hidden-row swap permitted by the symmetric past.

The known past is invariant under exchanging the two hidden population names. Marginalizing any observable prehistory therefore gives invariant weights on assignments of surviving blocks. Swapping the entries of one later routing column composes its all-block-to-one-population probability with this global exchange. Its integrated contribution remains equal separately for each column. This proves equality of all the stated local single-block completion observations, including all sample sizes and temporal coefficients, with arbitrary observable prehistories. It does not expose population flags or assert equality of every future event.

For the four-label event with exactly the two specified disjoint pair mergers, independent routing gives coefficient K_(z1,z2)K_(z3,z4), where K=Gamma*diag(r)*Gamma^T. The two merger orders supply two simplex factors1/2. Additional mergers affect orderdelta^3, so the exact-two-block restriction leaves the displayed quadratic coefficient unchanged. The pre-second-boundary assignment weights and the additional1/64 survival factor before the first expansion are correct.

The stated sums yield unconditional difference -9delta^2/4096000+O(delta^3). It is nonzero for small positive delta, proving that an observable two-block forest event, and therefore the full timed genealogy law, separates these sources.

Control source `399530fc081460d0698d6915a6d84d668a79899ed44678d703d5faeb99be54a9` was read and independently rerun. Result/stdout `ec4177ecb54d5dd85d1cc381699464d5888ee744b495d850220361d226cc9f8c` matches exactly, including8,176 symmetric-orbit column checks and both rational forest coefficients. The finite orbit checks support the general symmetry proof; they are not its only justification.

This is a concrete obstruction to iterating the first-boundary single-atom completion/Prony method, even with arbitrary earlier observable histories. It directs attention to joint forest observations. It does not prove a global multi-expansion identification theorem, full-law ambiguity, minimal sampling, finite-data accuracy, historical novelty, original G3/G4 closure or Lean verification. The accepted first-boundary and nonexpanding results remain unchanged.
