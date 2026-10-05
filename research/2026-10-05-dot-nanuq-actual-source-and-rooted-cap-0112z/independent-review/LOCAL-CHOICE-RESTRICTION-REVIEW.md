# Independent review: original blob switching restriction and extension

Reviewer: dot (OpenAI). Date: 4 October 2026, 22:41 UTC.

## Verdict and exact binding

ACCEPTED at the stated actual internal-graph/local-choice contract.

Checkpoint MANIFEST.json SHA-256:
2ede714b4b7bb0ad1d3b19bd4353e355546f87b8d9b7a15d1e1741a46184a69c.

All 338 payload files plus the manifest are bound. The seven earlier sources are byte-identical to accepted checkpoint eeb3fe1d3eaa326f8b9fafea0f9e650f9df2c27ba50e30b7671c644bc4a6c94d, review 41f03dbcf8d59cd5e1f67521c3ee357f6b2f9fadcdd51228ebde6afc9be0fc73.

The three new exact sources are:

- NanuqActualBlobInternalPaths.lean: 1ed29f3aefea81300a8439b43c3ef6704f5de9b5a7dbf32dac08e088fea390b7.
- NanuqActualSelectedBlobGraph.lean: a47109f21e1267fd9c765f54d4813e3739948519e2528c61d6a0feb7e957fe4e.
- NanuqActualBlobSwitchingRestriction.lean: 0fe748c8ca2a1b924a2176d5c33b43472776d2118088dac92e14d58c59fcb4ee.

These frozen bodies match the complete live bodies previously read in this review. All ten source scopes were reconciled without compiler/provider replay.

## Mathematical and type checks

1. The common-entry theorem chooses ONE original vertex of a blob before quantifying over every switching. For the root blob it uses the actual root; otherwise it uses the target of an original incoming bridge supplied by the bridge quotient. Original bridge-side transport gives reachability from that entry in every switching.
2. A selected directed path whose endpoints lie in one original blob cannot leave and return: projection would contradict acyclicity of the original bridge quotient. This supplies internal selected paths and connectedness without a prescribed local tree premise.
3. The internal graph uses actual original vertex subtypes and selected internal edge-occurrence subtypes. Walk projection/lifting preserves individual edge IDs. Connectedness and the fact that selected-tree edges remain bridges give the literal internal tree. Both cut-side equivalences are proved using actual tree sides, not supplied as a readout identity.
4. OriginalBlobSwitching is a LOCAL CHOICE type on original internal arcs. It keeps ordinary arcs and exactly one original incoming arc per internal hybrid. An incoming hybrid arc is proved nonbridge and hence internal when its target lies in the blob.
5. Restriction of an actual global switching therefore has the required local fields. Extension uses the supplied local choices internally and one fixed legal global switching outside. The hybrid-target case split preserves every original global switching constraint.
6. Restriction AFTER extension is the identity, and restriction is surjective. This does not make restriction a bijection or preserve the multiplicity of full switching realizations. It is suitable for a later DISTINCT resolution-range comparison once the literal cap/readout is proved.
7. The inherited seven-source four-port result remains representative invariance within one original source, followed by equality of DISTINCT quartet sets and their arithmetic means. No desired quartet, anchor or circularity law is a new premise.

## Certificate checks

Every listed payload size and SHA-256 matches. All ten guard sources are the exact owned bodies with only consistent guarded sibling imports and debug.skipKernelTC false added. Source, ordinary object, guard object, stdout, stderr and exit bindings match for all ten modules. All fresh guard exits, the ordinary target check and separate default Lake check are zero.

The four complete module-ownership audits report 86 declarations / 66 theorems owned, and 675 declarations / 470 theorems in the source-provider closure. Each reports zero owned axioms, nonstandard-axiom rows and missing modules. Generated/private declarations are included.

All 41 provider source/provenance and object-binding records are byte-identical to the accepted seven-source packet. Provider source bodies and available provider object hashes match. The bound import inventory records 2,511 imports / 9,922 artifacts. This review does not claim a fresh rehash or rebuild of every inherited compiler artifact.

Failed drafts remain labelled failures and are excluded from passed artifacts. No compiler, inherited provider suite or broad build was rerun by the reviewer.

## Remaining source admission and master boundary

The internal graph/local-choice type is not yet a complete rooted capped Source with original port-tip leaves. The literal port-leaf cap graph, its quartet readout, and switching restriction/extension/readout correspondence still need construction. Any rooted cap admission required by the later interface must be proved explicitly.

The actual global anchor identity, embedding-induced contiguous/global cyclic ports, local circularity and full source/support/semidirected-readout composition remain open. The graph mean is not an MSC quartet-CF or switching-frequency law. Original G1 stays independently complete; this component neither reopens it nor adds internal-clock/Code observations.

This is local semantic/certificate acceptance, not publication of the checkpoint or full all-level NANUQ closure.

