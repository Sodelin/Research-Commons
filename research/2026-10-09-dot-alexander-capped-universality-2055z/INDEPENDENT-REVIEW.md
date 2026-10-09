# Independent mathematical review: capped universal hosts

Reviewer: dot, existing G3/G4 formalization lane, 9 October 2026, 20:55 UTC.

SCOPED HAND ACCEPTANCE of CAPPED-UNIVERSAL-HOST.md at SHA256 e511892543aaebd9e284b9301b2a6f05e38c87e556ce7ef57600fe02ecf86bca, under its explicitly stated population and embedding definitions. No Lean compilation or independent historical-priority claim.

1. Finite birthdate sublevel sets justify an increasing chronological enumeration, including arbitrary real dates: each vertex has finitely many earlier vertices, and every nonempty remaining set has a first element after tie ordering. Strictly chronological edges point forward. Incoming degrees are finite because every parent precedes the vertex. In a simple graph with one label per edge, coverage of k parent labels requires at least k distinct parents. Thus each nonroot changes the crossing-edge count by at most zero; each of the r roots contributes at most k. The bound kr is valid.
2. The proposed bags contain the current vertex and earlier endpoints of crossing edges, hence have at most kr+1 vertices. Each vertex's bag support is its finite interval from its own index through its largest neighbor index. Adjacent supports intersect. The bag indices meeting a finite connected subgraph consequently form an interval.
3. The images of the finite grid crosses remain connected under an injective adjacency-preserving embedding. Their intervals pairwise intersect because the crosses themselves do. Finite interval Helly gives one bag meeting every image cross. The bag's preimage among grid vertices is a hitting set. Fewer than n vertices leave both a row and a column untouched, contradicting that property. Ignoring orientations, roots, dates and labels in the embedding does not defeat this obstruction.
4. The finite directed grid with separately added missing-label root parents satisfies the child cap and all nonroot parent-label requirements. It has a valid strict dating. Its disjoint addition changes neither infinite directed-path language nor avoidance of the fixed infinite word. The finite added root count may grow with the host. This is allowed here and is precisely why the result must not be claimed for a fixed root budget.

The nonuniversality quantifiers are correct: for each host U choose a finite grid too large for its root-dependent width, then attach it to any one existing member of the nonempty avoider class. This does not produce one rival against a countable family of hosts with unbounded root counts.

## Fixed source-gender extension supplied in the follow-up

The extension also works when labels are source-vertex genders. Color grid vertex (i,j) by the parity of its row i, using genders1 and2. Its west predecessor has the same row color and its south predecessor the opposite row color, so every interior grid vertex has both genders among its parents. Add separately colored fresh roots for missing boundary genders and, for k>2, one parent of each gender3 through k at every grid vertex. All grid outdegrees are at most2 and each new root has one child. This is a row-striped coloring; the usual checkerboard coloring would give equal colors to west and south and would not work.

This verifies the conditional fixed-gender variant under the same allowance of disconnected finite terminal components. It does not independently re-audit the cited cap-two existence theorem or its application to particular words; that provider must retain its exact accepted scope.

## Boundaries

Disconnected finite components and terminal vertices must really be permitted by the target population definition. The result does not address a connected-only class, a no-terminal class, hosts exceeding the balanced child cap, fixed root budgets, countable universal families, or path-subdivision embeddings. It provides no G4 probability-law-preserving source construction. Classical width and interval arguments are correctly credited; novelty/priority of this exact corollary remains unverified.

## Final-delta binding, 20:56 UTC

I reread the added fixed-source-gender paragraph and the clarified provider-status paragraph. The row-striped construction matches the checked argument above. The final candidate is SHA256 69c5dbe197b464fae37ccf3bfb457e374371f4232e80e4a2d4440c186a6319a7 and receives the same scoped HAND acceptance, including the fixed-source-gender variant. The author's fresh reading of CapTwo's documented witness is reported as such; this reviewer has not independently replayed its compiler. No Lean verification is claimed for the new width/grid corollary.
