# Next finite block receiver — exact source/API plan

Historical hand plan, now implemented as the five UNCOMPILED sources in this packet. Its duplicate-CyclicGap prerequisite has since qualified and is published at81bcbec04fd4174ad26fea48357073748ec6b433; this block package itself is not yet compiled.

The actual source already supplies the two missing combinatorial size facts without new hypotheses:
- NanuqActualPortCardinality.actual_nonleaf_blob_has_two_ports:2<=card(BlobPort b), used in actualEveryNonleafRootedCapSource itself.
- NanuqActualOpenedTipMultiplicity.actual_opened_tip_multiplicity: each original cap label has exactly one ordinary occurrence or exactly two hybrid-child occurrences; opened_tip_label_surjective covers every label.
A finite injective code of actual port labels into Nat preserves these facts. An arbitrary noninjective output code, allowed by the gap-only endpoint, is NOT sufficient for the multiplicity/block endpoint.

## Cyclic gap preservation under rotation
For the exact existing CyclicGap xs a b, rotation by one preserves it, including repeated a=b:
- LinearGap with empty prefix xs=a::b::post rotates to b::(post++[a]), a WrapGap.
- LinearGap with prefix z::pre rotates to pre++a::b::post++[z], still linear.
- WrapGap xs=b::(middle++[a]) rotates to middle++[a,b], a LinearGap.
Iterate only if needed. No distinct-label assumption is required for this lemma.

## Choose an actual block boundary
For a nonempty finite list with at least two distinct labels and count<=2 for every label:
- if first and last differ, its existing break is already between blocks;
- if first=last=x, there are at least three entries, and the second label differs from x (else at least three occurrences of x). Rotate once. The new last is x and new first differs, so this break is between blocks.
Thus a rotation by0 or1 suffices; this is not an arbitrary unrelated reordering. Preserve exact occurrence list before applying the label code.

At a break between different endpoint labels, a CyclicGap xs x x cannot be a WrapGap. Hence every doubled label has a genuine LinearGap xs x x.

## Linear block factorization
Induct on the remaining list. If the first two labels equal x, remove that two-element block; count<=2 proves x absent thereafter. Otherwise the leading x is a singleton: if x occurred later, count<=2 plus its LinearGap x x would force the second position to equal x (or produce three x occurrences). Remove it. For any y!=x, a LinearGap in x::tail descends to tail by the exact prefix case split; removal of two x's applies this twice. Counts of y are unchanged. This builds a Nodup base-label list and one Boolean duplication map with exact `xs=Restriction.blocks base dup`.

This is the SAME boundary label list after a documented cyclic rotation, not a supplied adjacent-copy list. Code injectivity is essential at the source-cardinality join, and singleton/trivial small-port cases remain separately scoped.

## Remaining tree/order join
The full opened binary tree is still needed to produce a syntax frontier in that induced cyclic order. All cut-side circular intervals must first be derived from the occurrence-level no-alternation endpoint. Choose a root-child interval break, orient actual children by their leaf intervals, then serialize with the accepted graph/label receiver. To move from that break to the block break, whole-root expose+swap iteration preserves exact quartet witnesses; `expose` alone leaves the list unchanged and is not a cyclic-reindexing theorem. No internal reassociation or arbitrary rotation system is permitted.
