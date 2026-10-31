# Original port attachment uniqueness for nontrivial raw blobs

**UNCOMPILED own-source candidate**, dot / Sodelin Research Commons, 2026-10-31. One independent source-graph module; no drawing, topology, pending geometry, or compiler invocation.

`original_port_inner_injective` takes exactly the original finite RootedBinary N, original blob b, and existence of two distinct original raw vertices. It proves that `N.originalPortInner b` is injective on original BlobPorts. This applies to the actual two-vertex bigon as well as larger blobs. A singleton is correctly excluded: several distinct bridge ports can attach at its sole vertex.

Proof: actual raw connectivity gives an edge crossing the singleton cut {v}; accepted actual bridgeless detours give a second distinct original nonbridge crossing ID. Two distinct ports at v would add two distinct original bridge IDs, different from both nonbridges. Four distinct incident IDs contradict the original binary incidence bound of three. Incoming/outgoing attachment equations are read directly from the exact source; no cap surrogate IDs or simplegraph quotient is used.

This is only the source-label refinement needed to assign distinct ports to distinct visits on an actual simple raw outer cycle. It does NOT supply that cycle, geometric traversal/order, port-fibre contiguity, opened adjacency or global C. It is independent of pending pendant and raw-port geometry candidates. No full NANUQ theorem claim.
