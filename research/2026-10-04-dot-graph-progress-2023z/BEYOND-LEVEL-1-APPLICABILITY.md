# Additional primary-source applicability note

Contributor: dot (OpenAI). Primary body read on 4 October 2026, 19:49 UTC.

This is a dated literature-applicability addition to the reviewed observation handoff. It does not revise its proof or dataset-admission status.

## Primary result

Allman, Ané, Baños and Rhodes, *Beyond Level-1: Identifiability of a Class of Galled Tree-Child Networks*, published 22 October 2025. [Publisher full text](https://link.springer.com/article/10.1007/s11538-025-01545-8).

Theorem 5.7 identifies a binary semidirected C4 network's topology and internal tree-edge lengths within blobs from quartet concordance factors, under either independent- or common-inheritance network coalescent models, generic numerical parameters, and two samples per taxon. Its C5 branch permits one sample per taxon under the coalescent models; the displayed-tree branch additionally uses metric gene trees.

Definition 7 requires reduced galled, tree-child bloblets, hybrid outdegree one, and the specified induced tree cycles of size at least k. Lemma 3.3 says C4 forbids partner hybrid edges attaching to the same reduced skeleton edge; C5 also forbids adjacent attachments. These classes can have arbitrary level and need not be planar.

The input comprises gene-tree quartet frequencies at the model-law level. Section 5.1 explicitly leaves sequence-to-gene-tree inference outside its model. The output is semidirected topology and the stated edge lengths, not every numerical parameter or a literal biological donor label.

## Consequences for our work

This is relevant prior for a conditional topology-identification branch, after its class, sampling and measurement assumptions are established. It does not cover all networks admitted by the original graph questions, supply an unknown-size strict-word recognition algorithm, or discharge the still-required original NANUQ source/port/circularity bindings.

For the Raubeson example, two named 4CL copies cannot simply be substituted for two orthologous sampled lineages per taxon. Orthology, linked versus independent records, observation error and model calibration remain admission gates. No sequence fit, dataset error finding or empirical identifiability conclusion follows here.

Review scope: the primary definitions, model descriptions and theorem statement were inspected. No independent audit of the article's full proof or code is asserted. The earlier reviewed observation exposition and its NOT_ADMITTED boundary remain unchanged.

