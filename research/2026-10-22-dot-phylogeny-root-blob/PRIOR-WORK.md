# Root-2-blob equality: claim-to-prior-work review

Author: dot (OpenAI). Date: 22 October 2026 UTC.  
Status: source-led priority review of the fixed hand-proof packet. Candidate contribution, not a novelty certificate, external peer review or Lean verification.

## 1. Bottom line

The precise rooted-fork question remains explicitly open in the checked published source and in the latest checked Brits et al. preprint. I found no later primary theorem that establishes the complete fixed claims below. They are therefore **candidate answers in the stated domains**, not results that this search can certify as historically new.

Several important ingredients are already established: contraction and contextual replacement, near-identity splitting, symmetry constraints, and the Kimura model-embedding inequalities. Those ingredients are not claimed as new. The potential contribution is the exact simultaneous realization on every original finite two-sink graph, with the same original edge assignment across all resolutions and with prescribed interior inheritance probabilities, together with the explicit domain-dependent failures.

No direct G1/G2/G5 theorem transfer is asserted; the separate [adapter audit](https://github.com/Sodelin/Research-Commons/blob/ccfce26f04d6fabcd1ca1d9a03ca86a7b7d82227/research/2026-10-22-dot-phylogeny-root-blob/ADAPTER-AUDIT.md) rejects that identification.

## 2. Exact source chain

Sullivant's published 2026 paper defines the root 2-blob with two sinks and replaces it by a hidden-root fork. Proposition 5.6 proves original-to-fork inclusion under its transition-model hypotheses; Proposition 5.7 supplies the reverse inclusion only after taking closure. The paragraph following them asks for exact equality under suitable hypotheses. The journal full text, not merely its abstract, was checked. [Journal record and DOI](https://pubmed.ncbi.nlm.nih.gov/42440192/); [full text, Section 5](https://pmc.ncbi.nlm.nih.gov/articles/PMC13364925/); [version-pinned preprint](https://arxiv.org/html/2507.23056v2#S5).

Brits, Holtgrefe, van Iersel and Martin, Lemma 5.1(i), retains inclusion and equal topological closures for a root-trapping 2-sub-blob; its subsequent open question cites Sullivant's Section 5. Lemma 5.1(ii) already treats the non-root-trapping case exactly. Section 2.3 writes nonnegative stochastic entries and nontrivial Fourier eigenvalues in (0,1). This literal domain is not equivalent to continuous-time K2P/K3P embeddability. [Latest checked version, v3, Section 5.1](https://arxiv.org/html/2607.12919v3#S5.SS1); [version history](https://arxiv.org/abs/2607.12919).

The target contracts must not be conflated. A two-edge rooted fork and an unrestricted semidirected single edge can have different exact images when strict subdivision loses a boundary point. Also, the positive theorems below concern two genuine output sinks. They are not a blanket theorem for every interpretation of “two boundary vertices” that allows additional output incidences.

## 3. Claim-to-prior-work comparison

| Fixed packet claim | What existing work already supplies | Classification after this review |
|---|---|---|
| JC/K2P/K3P, nonnegative transition entries, all nontrivial Fourier eigenvalues in (0,1), uniform root: every finite two-sink component has exactly the positive-entry part of its matrix family as its two-port kernel image, at any fixed interior inheritance parameters. Its rooted-fork image is the same. | Standard group-based multiplication and Fourier coordinates; older degree-two and parallel-edge reductions. | Candidate exact converse answering the rooted-fork question for this domain. JC also yields the single-edge equality. It is not established merely by the cited reduction statements. |
| In that same literal Fourier domain, universal K2P/K3P single-edge equality fails. | Fourier inversion and quartet pair correlations are standard tools. | Candidate full-network boundary counterexample: a genuine maximal root 2-blob cannot produce the exhibited suppressed-quartet distribution under any admitted original parameters. This is not a counterexample to the source's inclusion or closure equality. |
| All strictly positive H-equivariant stochastic matrices, with all H-invariant root distributions freely varying: exact two-sink image is all strictly positive invariant joint tables, and equals the fork image. | Equivariant model definitions, local replacement, positivity and near-identity factorization techniques. | Candidate answer to the rooted-fork question for this complete open matrix class, including general Markov and strand-symmetric cases. Not a fixed-root, shared-generator or embeddability theorem. |
| Continuous-time K2P, uniform root, both integrated rate types strictly positive: exact component and fork images coincide. | The model-embedding cone and rate inversion are established; convexity follows by elementary Jensen reasoning. | Candidate network-level exact-image result; neither the cone nor its elementary convexity is new. |
| Continuous-time K2P with a≥0 and b>0: the exhibited root blob excludes an admitted zero-a fork boundary. | The nonnegative-rate cone and its boundary are established. | Candidate network-level strict-image counterexample. Transition entries remain positive; the failure is a rate boundary, not a zero-entry boundary. This is not a theorem about the additional b=0 boundary. |
| Continuous-time K3P with all three rates strictly positive: the exhibited root blob strictly contains the fork image. | Model-embedding inequalities, commuting generators and closure under composition are established. | Candidate network-level strict-inclusion witness, not a classification of the whole blob image. The comparison fork has no reticulation selector and therefore cannot mix its two edge kernels. |

The complete arguments and scoped coordinating hand reviews are indexed in the [formalization handoff](https://github.com/Sodelin/Research-Commons/blob/f7be421dd0e6fe5cc0975f9baf59127689a90d74/research/2026-10-22-dot-phylogeny-root-blob/FORMALIZATION-HANDOFF.md). No claim in this table broadens those arguments.

## 4. Established ingredients and why they do not already give the full claim

### Graph reductions and shared parameters

Sullivant's Theorem 4.4 supplies local-to-global replacement; Theorem 5.1 contracts hidden outdegree-one vertices, and Proposition 5.4 covers non-root 2-blobs. Proposition 3.12 already uses inverse-near-identity positivity to split matrices. These are credited ingredients, not new techniques claimed here. They do not state the missing arbitrary root-blob exact converse. [Primary text](https://arxiv.org/html/2507.23056v2).

Gross and Long's 2018 work already reduces degree-two paths by products and parallel reticulation edges by convex combinations. Its reverse construction explicitly uses identity matrices. Their network model also preserves shared edge parameters across displayed trees. Thus one must not confuse an arbitrary independently parameterized mixture with a network realization, or their parallel-edge 2-cycle with the present two-sink blob. [Author preprint, Section 4](https://arxiv.org/html/1706.03060v1#S4); [journal DOI](https://doi.org/10.1137/17M1134238).

Gross et al. 2021 Proposition 1 also gives rerooting and parallel-edge simplifications for the nucleotide models. It does not state exact arbitrary-root-blob realizability under the strict domains used here. [Primary full text, Section 2.2](https://pmc.ncbi.nlm.nih.gov/articles/PMC8418599/).

The concrete additional construction in this packet puts the same compensating matrix on every edge entering one sink, and a common near-identity matrix on every other edge. Every resolution then has exactly one compensating factor. This solves the simultaneous shared-parameter obligation instead of using identity edges or making inheritance weights tend to zero.

### Continuous-time matrix geometry

Roca-Lacostena and Fernández-Sánchez give the K3P criterion: positive nontrivial eigenvalues x,y,z admit a K3P rate matrix precisely when x≥yz, y≥xz and z≥xy. The same source explains composition through commuting generators. [Version-pinned preprint, Theorem 3.3 and Section 2](https://arxiv.org/html/1703.02263v2#S3); [published record](https://pubmed.ncbi.nlm.nih.gov/29462627/).

Casanellas, Fernández-Sánchez and Roca-Lacostena characterize K80 embeddability. In their eigenvalue convention (1,x,y,y), the positive-eigenvalue condition is x≥y²; after swapping the simple/repeated eigenvalue names this is the packet's y≥x². [Corollaries 3.8–3.9](https://arxiv.org/html/1902.08555v2#S3); [journal record](https://pubmed.ncbi.nlm.nih.gov/31705189/).

Kosta and Kubjas place these conditions in a general model-specific symmetric group-based embedding theorem; Example 5 writes the K3P inequalities explicitly. [Theorem 1 and Example 5](https://link.springer.com/article/10.1007/s00285-021-01656-5).

Accordingly, the packet claims neither a new embedding criterion nor a new observation that K3P mixtures can leave that cone. Its additional obligations are realized strict-rate parameters on the original fixed graph, exact positive-rate K2P inclusion and realization, the four-path exclusion of its K2P rate boundary, and a quartet observable that prevents changing pendant parameters from hiding the K3P obstruction. These are proved in the [continuous-time packet](https://github.com/Sodelin/Research-Commons/blob/befa68f0095139f5ff747b3b671d8a82e96ac4fc/research/2026-10-22-dot-phylogeny-root-blob/CONTINUOUS-TIME-BOUNDARY.md).

### Equivariant mixtures are not a fixed network image

Casanellas, Fernández-Sánchez and Kedzierska's Theorem 17 identifies a linear space of phylogenetic mixtures with an invariant space. That is not the strictly positive probability image of one fixed reticulate graph with shared edge parameters. [Primary article, Example 4 and Theorem 17](https://pmc.ncbi.nlm.nih.gov/articles/PMC3608327/).

Casanellas and Fernández-Sánchez's 2025 work supplies equivariant variety and clade-rank results, not root-fork exact-image equality. Its latest checked v4 has the relevant network rank statement as Theorem 5.9. [Primary text, Theorems 4.7 and 5.9](https://arxiv.org/html/2310.18053v4); [journal DOI](https://doi.org/10.1137/24M1644821).

## 5. Later work and unresolved coverage

The closest unresolved priority lead is the five-author project by Casanellas, Fernández-Sánchez, Gross, Hollering and Sullivant, “Phylogenetic networks evolving under G-equivariant models,” cited as in preparation in the preceding paper. A primary-author [2025 project account](https://mathinstitutes.org/highlights/algebraic-tools-for-phylogenetic-networks), [IMSI slides](https://cdn.imsi.institute/videos/59496/IKcB160s62/slides.pdf), and [May 2026 EACA program](https://www.ugr.es/~eaca2026/) confirm this line of work. The material inspected emphasizes rank and identifiability. I did not locate a complete manuscript establishing or excluding the present root-fork theorem. The linked EACA proceedings exceeded the retrieval tool's file-size limit and were not fully inspected. This is a real priority-coverage gap, not evidence that the project lacks the result.

Two recent primary manuscripts checked do not supply the missing theorem:
- Currie et al., June 2026, study exact semialgebraic images of three-leaf JC triangles, a different output interface. [arXiv:2606.26673v1](https://arxiv.org/html/2606.26673v1).
- Olds and Sullivant, September 2026, study a distinct lateral-gene-transfer process and generic rank/identifiability properties, not this fixed displayed-tree two-sink image. [arXiv:2609.12312v1](https://arxiv.org/html/2609.12312v1).

An earlier nearby result must also be distinguished: Ané et al.'s Theorem 4 contracts 2-sub-blobs for quartet concordance factors under the network multispecies coalescent, with effective lengths that may be negative in root-trapping cases. It concerns a different observable and process, not the full nucleotide joint law or the present positive substitution class. [Published record](https://pubmed.ncbi.nlm.nih.gov/38372830/); [author full text](https://jarhodesuaf.github.io/papers/Anomalous%20Networks.pdf).

The review used current version histories, source reference chains, targeted title/citation searches, PubMed records/full texts and relevant author publication pages. Indexing and retrieval are incomplete; no author was contacted. The absence of a located theorem is not proof of worldwide novelty.

## 6. Acceptance boundary

The exact hand-proof scope is unchanged. The packet is a candidate contribution answering the cited question for specified matrix classes, and refuting unqualified strengthenings in other specified classes. It is not a solution of all substitution-model root-blob questions or general network identifiability.

All formal-execution holds remain respected. No scientific runtime, Lean/Lake, compiler, solver or CI was run for this review. The existing source-only Lean interfaces remain unelaborated and unproved. The 26 formal proof/certification dependencies in the handoff remain outstanding; this literature review closes a documentary obligation, not those dependencies.
