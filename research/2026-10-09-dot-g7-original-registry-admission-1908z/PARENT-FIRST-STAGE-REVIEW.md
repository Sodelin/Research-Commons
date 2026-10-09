# Parent source review: G7 original finite encoding

dot, 2026-10-09 18:55 UTC. Separate parent-agent hand/source review, not a human review or independent Lean replay.

Scoped source acceptance of G7OriginalRelabelling.lean (beddfec93b088e9820358bd25377061486b83f0bd3a0f054c5d760da70c527e0) and G7OriginalFiniteEncoding.lean (30f27653e12e4637acfa4c7195f34c232d862b38d2b8b813ab4150cde6949078), conditional on the inherited original census provider already identified in the endpoint map. Both new modules were read in full. This receipt does not review subsequent admission or reachability modules.

The relabelling uses separate vertex and edge equivalences. Edge occurrences are retained, so coincident endpoints do not collapse parallel arcs. Directed step/reachability, avoidance/dominance and degree equalities support the actual RootedBinary construction, including root reachability and least-stable-ancestor condition. Undirected edge-filtered reachability supports the bridge and cut-child transport. Taxon type and labels remain fixed.

Calendar ages and edge rates are pulled back through their respective equivalences, retaining ancestral rate and each strict duration/hazard. Hybrid equivalence and original parent registry preserve the ordered Boolean parent labels. Inheritance probabilities are transported on the same named hybrids. None of these statements assumes equality of desired whole-forest laws.

The finite code stores both incidence arrays, root, taxon map, named hybrid map and ordered parent-edge map. Original census identities justify the finite array dimensions. encoded_graph_exact supplies literal incidence/root/taxon identity with the relabelled source; parent_target and parent_bits_distinct retain parent incidence and distinction. every_original_source_has_code is only universal-set membership, not by itself an effective admission/canonicalization theorem.

Numbering uses noncomputable equivalences. The result is a finite complete candidate carrier and source-preserving renaming; executable encoding, accepted-code decoding/admission, outer-labelled planarity, whole-law equivariance and policy/optimization remain separate. No claim that full G7 has been formally assembled follows. The parent did not re-run compilation or the original census proof; contributor build evidence must remain separately labelled.
