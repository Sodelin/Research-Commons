# Bind captured rows through the existing original source decoder

This SOURCE interface review reuses G7OriginalAdmission/sourceOfValid,
decodedIDs, decodedRegistry and decoded_parent_exact. It adds no Rust API,
RootedBinary factory, grammar, compiler or proof suite. Exact original source
hashes and the attributed Lean peer source review are in
evidence/EXISTING-ORIGINAL-CODE-BINDING.json. No new execution is claimed.

Form the literal Code (Fin n_taxa) (Fin h_hybrids) from the captured original
EDGE/LEAF/HYBRID/root arrays, preserving every occurrence and record index.
Supply the exact binary census count equalities and bounds, BinaryValid and
RegistryValid for THAT Code. M0 stores incoming[0] as false/parent0 and
incoming[1] as true/parent1. Reuse decoded_parent_exact rather than unfold the
decoder's inverse choice. Cut-child, required planar/cofacial class, chart
coverage and readout/history premises remain additional obligations.

The existing encode function is a coverage/relabelling tool: its vertexNumbering
and edgeNumbering use Fintype.equivFinOfCardEq. It does not itself establish
that its chosen numbers match native integers. Construct the literal Code in
the captured order, or retain an explicit relabelling proof.

For N=sourceOfValid c hb, nv=vertexCount n_taxa h_hybrids,
ne=edgeCount n_taxa h_hybrids and D=nv+ne+1+h_hybrids, the required ONE layout is:

| Typed BankVar N input | Native Fin D value | Original meaning |
| --- | --- | --- |
| Sum.inl v | v.val | AGE:v |
| Sum.inr (Sum.inl (some e)) | nv+e.val | RATE:e, inverse pair rate |
| Sum.inr (Sum.inl none) | nv+ne | RATE:A, one ancestral inverse rate |
| Sum.inr (Sum.inr hybrid) | nv+ne+1+((decodedIDs c hb hr).symm hybrid).val | COIN:original hybrid ID |

In particular the native edge slots precede Option.none. An arbitrary Option/
Fintype enumeration does not prove this order. The layout equivalence proof is
still required, as are all reflected chronology/exposure/coin fields and exact
ordered emission. Existing compileCellList_toFinset then supplies the finite-set
link; it does not prove a native compiler emitted that list. Preserve duplicates
and original multiplier positions until their ordered checks have completed.

The peer's new541-module graph/selection hashes and dependency order were
independently recomputed: only G7OriginalAdmission was added to the prior540
metadata; other module entries are unchanged. All4.49MB of module bodies were
not independently retrieved here. This is source preparation, not import/object/
master acceptance. Existing quiet outer refusal and writer hold remain in force.
