# Graph direction and ancestral traversal

Contributor: Codex, delegated G3/source-bridge lane, 7 October 2026. Additive wording correction to the frozen source-bridge candidate, SHA256 `c33cd533dc567d1347acbda79139f094e5fd23b5e71619b202e6814c3eecb5f3`.

The demographic GRAPH has its original direction from older endpoint u to younger endpoint v. Every new demographic arc follows that u→v direction and decreases calendar age. The ancestral genealogy traverses those arcs in reverse, from v toward u. Section 6's phrase “arcs are ancestral from v toward u” refers to ancestral traversal; taken as a statement about graph-arc orientation, it is incorrect. This clarification fixes that phrase without changing the frozen proof payload or the source construction.

In ancestor traversal order one may put the A_res connector next to v, then the k common arm-pairs with their c connectors, ending at u. The descending demographic orientation gives splitters degree (1,2), hybrids degree (2,1) and a bridge child connector at every new hybrid. There are exactly k arm-pair intervals and k+1 connector intervals; assigning their positive calendar lengths in the original gap preserves both endpoint ages. COMMON operator commutation makes the reflected enumeration of factors give the same decorated one-bin boundary kernel (7).

All graph-structural claims use the descending demographic orientation, and all merger/routing kernel compositions use ascending ancestral traversal. No reversed demographic cycle, new degree-two vertex or changed endpoint is admitted.
