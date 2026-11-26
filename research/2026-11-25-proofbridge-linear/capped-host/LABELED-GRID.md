# The finite grid with private roots

[CappedLabeledGrid](CappedLabeledGrid.lean) constructs the actual edge-labelled finite padding, on grid cells and private-root slots indexed by target and label. The west and south parents use labels 0 and 1. Only an absent parent label activates its private root. Unused slots are isolated vertices, adding only finitely many roots. Lean checks that no edge enters these roots, that each cell gets every required parent label, that all edge labels lie below k for k≥2, and that a list of length at most two covers every vertex's actual children. The east and north edges are present, so the finite component contains the grid as a subgraph.

The rank is zero at roots and row plus column plus one at cells. Lean checks the increase and boundedness and imports the language-preservation theorem, giving the unchanged set of infinite words when the component is joined without cross edges. The [consumer](LabeledGridConsumer.lean) reuses the bound and checks both that a boundary root activates and that a private root for an existing west parent stays off. [Receipt](eligible-grid.receipt.json).

The fixed-source-gender variant, general real-date transport and the integration of the joined graph into the full population contract remain open. Do not promote the whole claim.
