# Contiguous multicopy extension: independent scoped hand review

Date: 23 October 2026. Reviewer: dot, coordinating assistant.

**Verdict: PASS at the stated abstract plane-tree scope.** This independently reviews an already author-complete theorem. It is not a new theorem, a retroactive authorship gate, external human peer review, a fresh computational run, or a Lean certificate.

## Proof identity

Reviewed the complete [CONTIGUOUS-MULTICOPY-EXTENSION.md](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/CONTIGUOUS-MULTICOPY-EXTENSION.md), at commit `e2502c82ab9a77c00543932f775a71e5374221f7`, Git blob `c788025d2d7821a884bb1ea10fc1389a8e7024ce`.

The source theorem assumes a finite unrooted plane binary tree, at least four taxon labels, one nonempty contiguous cyclic occurrence block per label, and independent choice of one occurrence of each label. The retained occurrences are the two endpoints of each block, or its sole occurrence. Restriction means the minimal connecting subtree followed by degree-two suppression. Block endpoints are defined by the block's boundaries in the cyclic order, not by an arbitrary linear cut through its interior.

## Checks of the full extension

1. **One-block replacement.** The three components at the median of three fixed other-label tips have disjoint interval leaf sets in the plane contour. An occurrence block avoiding those three tips lies inside one of the three complementary open arcs. Such an arc meets only the two adjacent median components, with at most one transition between them. Consequently any component met by the block contains an endpoint of that block. Replacing a selected occurrence by that endpoint preserves the quartet split because the quartet depends only on its median component.

2. **All quartet sets.** The one-block argument may be applied successively to each of four distinct labels while holding the other selected tips fixed. Every resulting witness uses retained endpoints. Associativity of minimal-subtree restriction identifies its quartet in the reduced tree. Reverse inclusion follows because retained tips were original tips. This proves equality of the complete indexed system of distinct quartet sets, not joint realization of all quartet witnesses by one selection.

3. **Circular order and split union.** Endpoint deletion preserves the collapsed taxon order. Every selected tree has that order. For a nontrivial circular split, take its adjacent boundary pairs (a,b) and (c,d). A displayed (bc| ad) quartet extends to a full selected tree by independent choices for the other labels. An edge of its central path separates those pairs; circularity and the two prescribed boundary gaps force its full split to be the specified split. Thus equality of quartet sets gives equality of split unions. Trivial splits are present throughout. This does not assume equality of full displayed-tree families.

4. **Distance, anchors and parameter transfer.** The original distance averages over distinct quartet topologies and retains the same number of taxon labels. Its entries, the anchor matrices, and fixed taxon-mass-weighted sums are therefore unchanged. The reduction lands in the adjacent singleton/doubleton representation class with at most (2|X|) physical tips. Conversely that class is already a subclass of contiguous blocks. Hence any score formula using only the indexed quartet sets, common order and taxon-level masses has the same universal parameter domain on the two classes. This is a transfer, not a new numerical parameter-domain calculation.

5. **Full-tree exclusion.** Direct hand inspection of the seven-tip caterpillar confirms the three displayed five-label split sets:
   - (x_0): (ax| bcd), (acx| bd);
   - (x_1): (ac| bdx), (acx| bd);
   - (x_2): (ac| bdx), (acd| bx).

   The middle tree is distinct from both extreme trees and disappears after deletion, while each of its splits remains. On the five four-label subsets, the quartet triples in order (x_0,x_1,x_2) are:
   - (abcd): (ac| bd, ac| bd, ac| bd);
   - (abcx): (ax| bc, ac| bx, ac| bx);
   - (abdx): (ax| bd, ax| bd, ad| bx);
   - (acdx): (ax| cd, ac| dx, ac| dx);
   - (bcdx): (cx| bd, cx| bd, cd| bx).

   Removing the middle column preserves each row's set, not its multiplicities. For example, uniform occurrence choice gives probability (1/3) to (ax| bc) on (abcx), versus (1/2) after endpoint reduction. Thus the exclusions of full-tree equality and occurrence-weighted distribution equality are substantive and correct.

## Supplier scope inspected

All links below use the same immutable commit.

- [ALL-LEVEL-STRUCTURAL-AUDIT.md](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/ALL-LEVEL-STRUCTURAL-AUDIT.md), blob `c655b69c1180fbe0e284a5e27218dace3c686bfb`: minimal-subtree repair, arbitrary-size restriction and the abstract adjacent-copy representation domain.
- [ALL-LEVEL-SUPPORT-STRUCTURAL-AUDIT.md](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/ALL-LEVEL-SUPPORT-STRUCTURAL-AUDIT.md), blob `42e6fef0d4a7f7f24f91d59c4b210747a5195f99`: boundary-quartet criterion and positive-weight exact-support transfer.
- [ALL-LEVEL-PROOF.md](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/ALL-LEVEL-PROOF.md), blob `313f0aff82eabf1a08b4551ed7e31501b137cebd`: Sections 3–6 and 8 specify the anchor convention, representation-wide coefficient reduction and exact support ingredients.
- [ALL-LEVEL-FINITE-AUDIT.md](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/ALL-LEVEL-FINITE-AUDIT.md), blob `0722de104b5d2006fe5a0b02c3ca0d4c46f4118b`, and [ALL-LEVEL-SUPPORT-FINITE-AUDIT.md](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/ALL-LEVEL-SUPPORT-FINITE-AUDIT.md), blob `15b85cc6475a6b8bf3b64f79722231b42127b383`: their recorded assertions cover all enumerated adjacent-copy systems, not only representations known to come from biological networks.

These supplier documents were read. Their domain and use in the extension match. The downstream circularity/exact-support transfer inherits the previously accepted computer-assisted ingredients; this review neither reran them nor independently audited every verifier implementation or re-established the external network-representation literature.

## Limits and records consequence

No mathematical repair was identified within the stated theorem. The proof does not cover interleaved occurrence blocks, nonbinary trees, constrained cross-label choices, infinite trees, or automatically admit higher-indegree biological networks. Biological use still requires the separate source-to-contiguous-block representation theorem. No historical novelty or formal-verification upgrade is made.

For card **CB-NANUQ-004**, preserve complete authorship and add this separately scoped assistant hand-review receipt. Replace only the historical claim that no separately located whole-extension review was available. No execution or public repository mutation was performed for this review.

