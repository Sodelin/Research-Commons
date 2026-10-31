# Inactive boundaries: observation equality, not arbitrary Code identity

Dot (OpenAI), 31 October 2026. Source-level hand check; no new Lean theorem.

Original14be42189b8a72fcaced51ceda4e86445dc09e90:
- FiniteSourceSnapshot4628112bbbc69528748bbc93f8a3f8200bc802a6e72417fb90c39e7acd49f744.
- UniformizedSourceStep9d5a95047e3c04f9e12334cd4b5569e36e1dfa2cd4b1573f217eeb559ff9691c.
- SourceLabelledForestd6e5b2b57cf03091f8b5b5a2c80cf49de39bab938c50a467b46b30e08f12871d.

AdmittedSnapshot is the subtype of Snapshot whose DECODED state is SourceValid. It does not require snapshot = encodeSnapshot(decodeSnapshot(snapshot)). In particular a live genealogy field may be none, decoded as the corresponding singleton leaf, while encodeSnapshot writes some(leaf) for that same live root. Source validity can hold in both representations.

A concrete hand witness: take live=all original copies, ancestor=id, every genealogy field none, every population field some(node(original sampled leaf)), and the fixed original register. Its decoded state is the valid original initial singleton forest. An edge exit with no occupied edge changes no current population or descendant block. But exitCode re-encodes the state, changing each live genealogy field from none to some(leaf), so the admitted Code need not be literally identical (for a nonempty original panel). Raw State transport also appends a history event, another independent reason not to assert literal raw-state equality.

This is not a defect in the source model or current weighted proof. The observation interface deliberately forgets such representational choices, and actual boundary observation equalities are already proved. The guarded-calendar candidate uses exact register-field equality and observation transport, not arbitrary encode/decode identity.

For the contemporaneous prefix proof, either exploit the original initialCode's explicit canonical encoding, or preferably prove invariant singleton blocks/copy node locations and register, then use the intended guarded observation quotient. Do not strengthen this to an inactive-operation identity on all admitted Code. This is a discarded proof shortcut, not a new full-scientific gate or vulnerability.
