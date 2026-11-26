# Actual bag intervals for finite connected sets

Lean checks that the actual bags meeting any nonempty finite connected vertex list in the natural-order population form one nonempty finite interval. A shared bag along each edge prevents a walk from crossing a missing bag index. No path-width theorem is assumed. The [independent consumer](ConnectedBagConsumer.lean) imports the exact invariant and checks a disconnected counterexample in the auxiliary k=0 edgeless model: vertices 0 and 2 meet cuts 0 and 2 but not cut 1. That control is not a claim about the final k≥2 class.

[Component](CappedConnectedBags.lean) · [Machine receipt](connected-bags.receipt.json) · [Actual graph bags](ACTUAL-BAGS.md). Next enumerate the actual row-and-column crosses, construct adjacency-preserving walks in their images, and feed them into the existing finite grid interface. The real-date and language-preserving-grid components and the whole theorem remain open in Lean.
