# Natural-order graph to actual bags

[CappedActualBags.lean](CappedActualBags.lean) builds a cut's bag directly from the existing natural-order population's adjacency and finite child supports. It puts the current vertex in the bag and includes each earlier vertex with a child at or beyond the cut. Lean checked:

- Bag length is at most the known crossing count plus one, and hence at most k times the root count plus one.
- Each actual edge has both endpoints in the target's bag, and every vertex appears on exactly one nonempty finite interval starting at its birth index.
- In particular the first bag has size one. A separate consumer accepted the exact statements and rejected dropping the +1 from the supplied width theorem.

[Machine receipt and source pins](actual-bags.receipt.json). This closes the natural-order graph-to-bag interface, not the full capped-host theorem. Next use the vertex intervals to show that all bags meeting a connected embedded cross form an interval, then connect to the checked finite-grid contradiction. Real-date transport and disjoint language-preserving padding remain separate.
