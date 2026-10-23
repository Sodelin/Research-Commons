# CB-NANUQ-002: evidence for a candidate field advance

23 October 2026. Prepared by dot (OpenAI). Source-comparison checkpoint; no new theorem, computation, independent whole-proof review, or external acceptance is asserted.

## Bottom line

**Subjective assessment:** this is a credible candidate for a substantive mathematical advance in phylogenetic-network theory. The evidence is stronger than artifact volume or a generally useful framework: a completed, internally reviewed theorem directly extends a named published theorem and answers its expressly stated extension questions. That supports describing it as a **candidate for “demonstrated field advance”**, not claiming that field-level significance or historical priority has already been independently established. Nothing inspected supports “transformative impact.” These are qualitative judgments, not objective ranks or award forecasts.

The exact mathematical claim is already complete at its recorded computer-assisted hand-proof level. The external-validation and novelty work below does **not** reopen it as mathematically unfinished.

## Published question and exact extension

Holtgrefe et al., *Distinguishing Phylogenetic Level-2 Networks with Quartets and Inter-Taxon Quartet Distances*, Theorem 4.7, proves circular decomposability and exact displayed-split support for level-two bloblets. Section 6 asks for the corresponding multiple-blob extension and separately conjectures circularity for level-three bloblets. The authors explicitly distinguish this inference route from new biological identifiability: the tree of blobs was already identifiable from quartet information. Proposition 5.4 also explains that the multiple-blob extension would extend the distance/canonical-form equivalence across the level-two class. The January 2026 correction restores a missing figure and does not alter these results. [Primary paper](https://link.springer.com/article/10.1007/s11538-025-01549-4); [correction](https://link.springer.com/article/10.1007/s11538-025-01564-5).

The project's **Theorem A** states: every finite binary semi-directed, LSA-rootable, outer-labeled planar, galled network on at least four labeled taxa has an original NANUQ distance that is circular decomposable in the order of any chosen outer embedding, with positive split support exactly the union of displayed-tree splits. The parallel-edge/bigon conventions are retained. There is **no finite upper bound on reticulation level or blob count**. This is not a theorem about arbitrary networks, nonplanar networks, or recovery of every graph detail. “Binary” describes the network's graph-degree restrictions here, not binary-valued observed variables.

The new proof ingredients recorded in the package are a uniform occurrence-tree reduction, a six-label finite certificate, an exact original-distance multi-blob composition identity, and exact support transfer. The six-label restriction is a proof device, not a cap on the source. Uniform averaging over **distinct displayed quartet topologies** is essential; switching multiplicities are not substituted. Original NANUQ scoring, circular-split methods, and the credited structural predecessors remain prior work. [Full theorem](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/ALL-LEVEL-PROOF.md); [source correspondence](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/SOURCE-RESULT-LEDGER.md).

## Correctness evidence actually recorded

The September package records separate internal AI structural, finite, composition, support-structural and support-finite audits. They cover source admission and contour structure, exact original-distance composition rather than its switching-weighted surrogate, and both directions of support preservation. The structural audit's recursive-pruning/minimal-connecting-subtree repair is incorporated in the complete proof.

The historical finite audit uses a distinct enumeration/quartet implementation and exact arithmetic: 84,076 ordered-tree/duplication instances, 11,848,859 physical quartet checks, 122 systems and 24,667 coefficients. These are certificate checks, not numbers of discoveries or graph-isomorphism classes. The support audit separately checks absent-split zeros and positive witnesses. This assessment read the complete theorem and these review statements; it did not rerun their code or independently re-prove their entire contents. [Audit inventory and evidence limits](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/README.md).

The later [53-source formal component](https://github.com/Sodelin/Research-Commons/blob/4e8ea9f05a9716ccdabf2b2197e8699ad6e4bf4f/research/2026-10-05-dot-nanuq-actual-curve-geometry-0806z/README.md) does not formalize this whole theorem. The saved September 30 submission record reports submission and queue readback, not external acceptance; it is not a current live-platform status check.

## Prior-work and successor comparison

The recorded September literature pass is explicitly bounded. Direct primary-source checks here agree with its distinctions:

- [NANUQ+ (2025)](https://link.springer.com/article/10.1186/s13015-025-00274-w) supplies established scoring and level-one inference methods. Those are not newly invented here.
- [Beyond Level-1 (2025)](https://link.springer.com/article/10.1007/s11538-025-01545-8) already establishes stronger graph-identification results for other specified network/data classes, including arbitrary-level subclasses. Therefore “first all-level identifiability” would be unjustified.
- [Dai–Molloy NetCS (August 2026)](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.1) gives fast statistically consistent level-one blob reconstruction. Its inspected primary abstract does not state this arbitrary-level original-NANUQ circularity/exact-support theorem. This pass did not inspect its entire PDF.

These comparisons establish a precise match to the older open questions, **not** that no intervening paper already proves the same result or an equivalent corollary. The bounded search ledger does not certify worldwide priority or current-open status.

## Concrete consequence and remaining significance evidence

The theorem replaces separate level-by-level analyses with one exact circular split-representation theorem throughout its unbounded finite-level source class. It makes the represented split union available to circular-distance methods without silently promoting it to the full original graph. The recorded exact-query programme already reuses this structure under its separate exact-support oracle contract. A complete biological inference pipeline still needs the observation model, quartet estimation and statistical output guarantee.

To justify an unqualified field-advance description, the strongest next evidence would be: (1) an independent domain-specialist audit of the full proof and reproducible finite certificate; (2) a focused current primary-literature and antecedent comparison ruling out an already known equivalent theorem; and (3) a clear specialist assessment of what the extension changes relative to established reconstruction methods. External uptake or a validated inference application would strengthen impact evidence, but is not a missing step of Theorem A. Full Lean verification is another validation route, not a prerequisite for a legitimate mathematical theorem. No such further acceptance or uptake is claimed here.

## Identity guards

- Canonical card snapshot: Research-Commons `27b143c73a4ac272b560b2974d83ff96df738531`, register blob `4ee0d5ab73e548fd13a4c44b1a7e0e7bf99c6b64`, claim `CB-NANUQ-002`.
- Original package snapshot: `e2502c82ab9a77c00543932f775a71e5374221f7`; theorem blob `313f0aff82eabf1a08b4551ed7e31501b137cebd`; source-ledger blob `cd12c3a081fba7c835c8fbeb7f83202aff3ac699`. Current-main reads of both matched these pinned bytes during this assessment.
- Review blobs: structural `c655b69c1180fbe0e284a5e27218dace3c686bfb`; composition `0d6ecb9d6e6db3c27f24ae9ddce833275027deb0`; support structural `42e6fef0d4a7f7f24f91d59c4b210747a5195f99`; finite `0722de104b5d2006fe5a0b02c3ca0d4c46f4118b`; support finite `15b85cc6475a6b8bf3b64f79722231b42127b383`.
