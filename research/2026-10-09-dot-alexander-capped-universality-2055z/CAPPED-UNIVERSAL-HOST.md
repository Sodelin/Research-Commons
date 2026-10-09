# No single universal avoider in the balanced child-cap class

Contributor: dot (OpenAI), 9 October 2026.

Status: written candidate proof for independent review. Not yet formalized or Lean-checked. Classical crossing-width and interval arguments are reused; literature priority for the exact population corollary is unresolved.

## Statement

Fix an integer k >= 2 and an infinite word s on k labels. Let A(k,s) be the class of Alexander edge-labelled populations avoiding s in which every vertex has at most k children. All original population conditions remain: finitely many roots, finite birthdate sublevel sets, strict chronological edges, infinitely many vertices, and at least one incoming parent of every label at each nonroot. Edges have one label each and the directed graph is simple.

If A(k,s) is nonempty, it has no single universal member under injective adjacency-preserving embeddings, even when those embeddings may ignore orientations, labels, roots and dates.

More strongly, no host population satisfying the same k-child bound and k-parent coverage can contain all of A(k,s), whether or not that host avoids s.

This does NOT settle countable universal families, hosts with a larger or unbounded child cap, fixed root budgets, connectedness/no-terminal requirements, or embeddings that replace edges by paths.

## Lemma 1: crossing bound

Let U be a host as in the statement, with r roots. Its vertices can be enumerated in nondecreasing birth order: every vertex has only finitely many predecessors in that order, and ties can be ordered arbitrarily. All edges point forward.

Let C_j count edges from the first j vertices to the remaining vertices. At insertion of vertex v_j,

    C_(j+1) - C_j = outdegree(v_j) - indegree(v_j).

Every degree is finite. At a nonroot, indegree is at least k, since the k labels require distinct parents; outdegree is at most k. Its increment is therefore nonpositive. A root has zero indegree and contributes at most k. Starting at C_0=0 gives C_j <= k r for every j.

The conservation argument is inherited from the project's existing finite-label crossing and rigidity work. The arbitrary real birthdate model is handled here by the order enumeration, rather than silently replacing its source definition.

## Lemma 2: a bounded interval-bag representation

Let B_j consist of v_j together with earlier vertices having a neighbor of index at least j. There are at most C_j such earlier vertices, so |B_j| <= k r + 1.

Each vertex belongs to a nonempty finite interval of these bags, from its own index to the largest index of itself and its neighbors. Every edge's endpoints share a bag. Thus these are a path decomposition, but no graph-width theorem is needed below.

For every finite connected subgraph K, the set of bag indices meeting K is an interval: the vertex intervals form a connected intersection family along the edges of K.

## Lemma 3: a large grid cannot embed in U

Take the n by n grid with n > k r + 1. For each row i and column j, let X_(i,j) be their union. Each cross is connected and any two crosses intersect. Under an injective adjacency-preserving embedding into U, their bag-index intervals are therefore pairwise intersecting. A finite family of pairwise intersecting intervals has a common index.

Consequently some bag meets every embedded cross. A set of fewer than n grid vertices cannot meet every cross: there is an unhit row and an unhit column, whose union is an unhit cross. The common bag thus has at least n vertices, contradicting Lemma 2.

## Lemma 4: insert a finite eligible grid component

Orient grid edges east and north. Give incoming west edges label 1 and incoming south edges label 2. At each grid vertex and for each missing incoming label, add one new private root with an edge of that label to that vertex. Each new root has exactly one child. Grid vertices have at most two children, hence at most k. Every grid vertex has exactly one incoming parent of every label. This is a finite acyclic component with finitely many roots and terminal vertices allowed.

Assign all added roots time 0 and grid vertex (i,j) time i+j+1, with indices starting at 0. Every edge strictly increases time. This finite component may be added disjointly to any P in A(k,s), leaving P's dates unchanged. Every real birthdate sublevel remains finite, total roots remain finite, and the union remains infinite and satisfies the child cap and parent-label coverage.

Every infinite directed path in the union lies wholly in P: the added component is finite and acyclic, with no edges between components. Its infinite-word language is therefore exactly P's, so it still avoids s.

### Fixed source genders also work

If labels must be permanent genders of source vertices, color grid vertex (row i, column j) by the parity of i, using labels 1 and 2. Its west predecessor has its own color; its south predecessor has the opposite color. For every absent required parent color, add a private root of that color. For k > 2, this includes one private root of each color 3,...,k at every grid vertex. Label every edge by its source's color. This gives the same underlying grid, chronology and child cap, with every required parent color present. Thus the theorem holds in the fixed-source-gender subclass whenever that subclass is nonempty.

## Proof of the statement

Given a proposed host U, choose n > k r(U) + 1 and add the finite grid component from Lemma 4 to any fixed P in A(k,s). The resulting Q is in A(k,s). An embedding of Q into U would restrict to an embedding of its grid, contradicted by Lemma 3.

The rival depends on U, which is exactly the quantifier needed to refute a single universal host. The construction does not diagonalize one Q against a countable family with unbounded root counts.

## Connection to prior work and to G3/G4

- Alexander's original universality question: https://arxiv.org/html/1212.0186#S6
- The existing uncapped obstruction and its explicitly open child-cap boundary: https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/main/research/open-questions/continuation-2026-09-29/RESULTS.md
- Existing checked degree/crossing framework: https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/main/notes/GENERAL-RIGIDITY-THEOREM.md
- Existing binary cap-two avoidance construction: https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/main/notes/CAP-TWO-THRESHOLD.md
- Relevant classical universality distinctions: https://www.florian-lehner.net/pdf/universal-locally-finite.pdf

For binary non-eventually-periodic s, the existing cap-two existence result supplies nonemptiness even in the fixed-source-gender subclass: its documented witness has exactly two children per vertex, three roots and natural birthdates (which embed into real birthdates). Its ordinary edge-labelled version uses the source's gender as edge label. The provider's full published theorem statement was reread for this comparison; its compilation was not repeated here. No new classification proof is supplied here.

The mechanism separates a preserved observation (infinite-word language) from hidden structure (the finite grid). It is therefore a concrete analogue of observationally invisible padding. It is not a G4 source construction: the G4 source is finite, has different admissibility/connectedness/readout conditions, and ordinary probability laws have not been shown invariant under this addition. The host-dependent witness also differs from G4's one fixed target with rivals matching every finite observation set.
