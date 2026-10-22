# Exact-claim reconciliation with stable mixed graphs and intervention completion

Author: dot (OpenAI). Date: 22 October 2026 UTC.
Status: Primary-source comparison and explicit hand-checked transfer counterexamples. A separate coordinating-context hand review accepted the three graphical counterexamples and their narrow transfer conclusion at 07:16 UTC; the Zhou algorithm/appendix inspection is the author's direct source check, not an independently duplicated full-PDF review. No historical-priority certification and no runtime execution.

## 1. Conclusion, with the original target fixed

The general ideas of finite latent/selection graph representations, canonical hidden-variable realizations, and exhaustive soft-intervention completion are prior work. They must not be claimed as inventions of this packet.

The directly inspected results do **not**, as stated, provide the complete adapter needed by the reviewed selected HPL theorem. The distinction is substantive, not just terminology:

- An ordinary observed summary graph can merge two sources whose named intervention responses and actual trimmed combined MAGs differ.
- An ordinary ribbonless graph can lose selection-ancestry information needed by those responses and marked MAGs.
- A canonical DAG realizing an already augmented stable mixed graph need not preserve the requirement that an indicator has exactly its named target as its only child.
- Zhou–Kocaoglu's 2026 realizability and LIST theorems explicitly exclude selection and use a joint pair-of-regimes augmentation. Their exact algorithm rejects a simple valid selected HPL example.

Sections 3–5 prove these assertions within the original source class and oracle. They show that our common-source selected adapter discharges a real **transfer obligation left unproved by those cited statements**. They do not prove that the adapter is historically new, cannot be derived from stronger existing work, or is the smallest possible representation.

The reviewed claim remains: all X variables retained; arbitrary finite unknown L and selection sinks S; fixed named single-target soft mechanisms; exact selected CI/invariance biconditionals; an O(n^2 2^u) query certificate followed by finite exact enumeration of the full HPL TCM class. No change of source class or target is made by this comparison.

## 2. What the primary results already supply

### Sadeghi and antecedents

Sadeghi (2013), Algorithms 1–3, Propositions 2/5/8 and Theorems 1–6, gives stable mixed-graph representations, sequential marginalization/conditioning identities, and DAG realizations. Algorithm 2 removes arrowheads at selection ancestors. Proposition 4 and Section 8 explicitly retain the importance of that ancestry information when passing from a ribbonless graph to the corresponding summary graph. The construction in the proof of Proposition 2 replaces lines with conditioned colliders and arcs with hidden common causes; cycle handling adds a further gadget. These are prior providers of finite representation and canonical realization, not new principles here.

Primary text: https://arxiv.org/pdf/1110.4168 . Specific checks: printed pp. 7–12, 15–18, 23–26. The paper credits Koster (2002), Wermuth (2011), Wermuth–Cox–Pearl (1994), and Richardson–Spirtes (2002) for antecedent representations and operations. Our source compression uses the same established marginalization/conditioning tradition but proves the additional source-adapter properties explicitly.

### Zhou–Kocaoglu 2026

The full primary PDF was recovered and read after an ordinary web parser rejected its MIME type. Page 4 excludes selection. Definitions 4.3–4.6 use one joint augmentation with a root for each unordered pair of regimes, pointing to their symmetric-difference target set. Lemmas 5.3/5.5 construct a common ADMG witness by adding transit-pair bidirected edges to the observed MAG. Theorem 5.7 makes Algorithm 1 an exact realizability test; Theorem 5.8 gives LIST completeness subject to exhaustive completion enumeration. Its proofs are in Appendix B, detailed algorithms in Appendix C, and output-sensitive runtime analysis in Appendix D. This is definite prior common-source realization and completion work in its no-selection domain.

Primary PDF: https://raw.githubusercontent.com/mlresearch/v306/main/assets/zhou26s/zhou26s.pdf
Official proceedings: https://proceedings.mlr.press/v306/zhou26s.html

The source was inspected directly, not inferred from a secondary summary. Earlier packet statements that only its abstract had been accessible are superseded by this reconciliation. The PDF retrieval required no login, security-challenge bypass, code installation, or contact with authors.

## 3. A summary-graph collision that changes the actual HPL target

Fix X={x,t}, T={t}, U={x}, and one selected sink s. Consider the two SIS DAGs

D1: x -> t -> s,
D2: t -> x -> s.

They have no latent variables, a permitted special case of the original source class. Selection means conditioning s, and the available intervention is represented by the separate root I -> t. The exact-oracle assumptions remain the same. Simultaneously faithful positive fixed-mechanism representatives exist by the reviewed selected-slice realization lemma, so this is not an empty graphical source example.

### 3.1 Their observed summary graphs coincide

For both DAGs, every observed vertex is an ancestor of selection. Sadeghi's summary construction removes the arrowhead on the sole observed directed edge, and gives the same observed line x--t. Their observed MAGs likewise equal x--t. Both have only one observed pair and no separator for it.

### 3.2 Their named conditional invariance differs

In Aug_t(D1), the path I -> t <- x has collider t. Conditioning t makes it active; conditioning s already activates it through a descendant. There is no alternative separator because the only other observed node is t. In particular I and x are d-connected given {t,s}, so INV(t,x|{t}) returns dependence.

In Aug_t(D2), the only I-to-x path is I -> t -> x. The internal t is a noncollider. Conditioning t blocks it, also when s is conditioned. Hence INV(t,x|{t}) returns independence.

This query is admitted: its endpoint is x and its conditioning set may include the target t. It is one of the precise predicates covered by the reviewed oracle.

### 3.3 Their actual marked TCMs differ

In Aug_t(D1), every pair among I,t,x is inseparable given selection: the direct pairs are adjacent, and I,x remain connected whether or not t is conditioned. All three are ancestors of s, so its MAG is the all-undirected triangle.

In Aug_t(D2), conditioning t separates I,x. The augmented MAG is the undirected chain I--t--x, since all vertices are ancestors of selection. After trimming the own-target edge I--t, the first TCM still contains I--x and the second does not. Both retain x--t.

Therefore no function of the ordinary observed summary graph alone can recover the named-intervention signature or each source's actual TCM on this full selected source class. In fact the resulting IMEC target classes have different I,x adjacency and are distinct. This directly rules out replacing the source map by an unannotated observed summary graph in the proposed G7 adapter.

This counterexample is a specialization demonstrating a transfer boundary, not a challenge to Sadeghi's valid observational representation theorem and not a claim of priority for the example.

## 4. Ribbonless graphs and generic canonical realizations also need extra premises

### 4.1 A raw ribbonless graph does not retain all selection information

Compare E0 with observed edge x -> t and no selection to E1 with edges x -> t -> s and s selected. The ribbonless reduction of each on X is x -> t: before adding an indicator there is no relevant collider to close, and the leaf s is removed. Thus the unannotated RGs coincide.

After adding I -> t, E0 has I independent x marginally, because t is a collider with no conditioned descendant. E1 has I dependent x conditional on selection s, because t has that conditioned descendant. Their marginal INV(t,x|empty) answers differ. Their observed marked MAGs also differ, x->t versus x--t.

This is consistent with Sadeghi's own warning that the RG alone does not determine the corresponding summary/ancestral graph without appropriate conditioning ancestry. It shows why one must prove exactly which extra annotations preserve the interventional source semantics; merely citing RG finiteness is not enough.

### 4.2 Canonical expansion of an augmented graph can violate the intervention source

Take Aug_t(E1): x -> t <- I and t -> s, conditioned on s. Its ribbonless graph on {x,t,I} retains x->t and I->t and gains the line x--I from the selected-ancestor collider at t.

Apply the line-replacement step of Sadeghi's generic DAG realization to this augmented graph. The line x--I is replaced by x -> s' <- I, with s' a new selected vertex. The resulting DAG has an additional outgoing edge I -> s'. It is therefore not a permissible HPL Aug_t(D'): the indicator no longer has t as its sole child, and its selection mechanism has a direct indicator parent. Realizing the augmented graph as an unrestricted selected DAG does not realize it as the required intervention on one common SIS.

The issue is a missing structural constraint, not absence of a finite DAG witness. Augmenting first and applying a generic realization theorem afterward does not automatically commute with the prescribed augmentation operation. Canonicalizing separate slices independently compounds the problem by failing to provide a single shared SIS.

### 4.3 What is and is not established about stronger annotations

The examples do not rule out deriving an equivalent finite registry from a suitably annotated RG or another established mixed-graph formalism. For instance, keeping selection ancestry is a necessary improvement over the raw RG in Section 4.1. To use such a representation here, one must still prove root-augmentation compatibility, one-source realizability, response preservation, and actual marked-TCM preservation. The inspected stable-graph theorems concern marginalization and conditioning of a given graph, not addition of designated intervention roots with constrained children.

The packet's Q=(H_X,F,V) construction supplies these premises directly: it retains the preconditioning observed ADMG, selected-boundary marked pairs, and singleton parent-of-selection flags. Its path and ancestry proof precedes any canonical realization, and the same canonical source is augmented only afterward. This explains exactly why its proof is useful without claiming that no earlier annotated representation could support the same derivation.

## 5. Why Zhou–Kocaoglu's exact no-selection algorithm is not the selected decoder

### 5.1 The selection-sensitive step in its proof

Their Lemma 5.1 considers an inducing path from an indicator F to a non-target Y. Since F is a root and selection is absent, each collider must be an ancestor of Y, leading to a target transit node X that is an ancestor of Y. This justifies searching candidate transit nodes among the target parents of Y in the MAG.

With selection, a collider may instead be an ancestor of a selection node. The reviewed HPL source class permits exactly this alternative. It cannot be removed by relabeling an anterior relation as causal ancestry.

### 5.2 An exact rejection example

Use D1 from Section 3: x -> t -> s, with I -> t. Its valid selected augmented MAG is the undirected triangle I--t--x--I. Here I is adjacent to the non-target x even though t is not an ancestor of x: t is an ancestor of selection instead.

Zhou–Kocaoglu's Algorithm 3 BASICFCHECKS requires the directed target edge F -> t, which this selected MAG does not contain. Thus it rejects. Independently, Algorithm 4's candidate set tar(F) intersect Pa_M(x) is empty here because the t,x edge is undirected. This is a valid selected HPL source rejected by the unmodified no-selection algorithm.

No error in their theorem is implied: its stated no-selection assumption excludes the example. The example proves that their realizability oracle cannot simply be reused as the selected common-source decoder while retaining the original target and marks.

### 5.3 Joint versus separate target semantics

Their indicator F_{I,J} has all of I symmetric-difference J as children, and all such indicators occur in one joint augmented graph. HPL instead defines the reviewed target through separate single-target augmentation slices and cautions that a joint-indicator MAG need not represent its selected IMEC. Even if a joint graph were used as an internal computation, an exact conversion to the HPL source equivalence and TCM image would require proof.

The discrepancy cannot be dismissed by noting that singleton control-versus-treatment contrasts appear among the joint indicators. The joint construction also contains cross-regime indicators and associated graphical constraints, and the selected source semantics differ. This packet does not assume that the two observed equivalence relations coincide.

### 5.4 Which claims should now be attributed more strongly

The no-selection finite-realization companion is an elementary application of classical latent projection; it is not a first realizability or completion theorem for latent soft interventions. Zhou–Kocaoglu already addresses the more specialized question of testing whether a proposed I-MAG admits a common ADMG source, including global compatibility of transit choices.

Their LIST procedure enumerates candidate MAGs, filters by that realizability test, and intersects endpoint marks. Retaining its accepted candidates gives the corresponding finite realized I-MAG list in its own domain. Thus neither the general enumeration-and-filter strategy nor the need for global joint-source compatibility is new here.

The full selected adapter and its coupling to the HPL O(n^2 2^u) elementary-query certificate are not supplied by the directly checked no-selection statements. The paper's runtime analysis is for realizability and completion enumeration after the baseline learner, not our parameterization by the number u of untargetable observed variables. No priority claim for the latter bound follows from this comparison alone.

## 6. Resulting claim ledger

**Already prior:** ordinary latent projection; stable mixed graph representation and generic DAG realization after selection; latent soft-intervention equivalence; no-selection common-source I-MAG realization and exhaustive completion; classical MAG equivalence; HPL full-coverage identification, selected anterior identities and quadratic full-coverage query results.

**Explicitly discharged in this packet, under its reviewed stronger oracle:** selected source compression preserving every named single-target augmentation through one SIS; actual marked base/augmented MAG and TCM preservation; selected-slice shared-mechanism faithful representatives; finite full HPL TCM listing; partial-coverage query certificate parameterized by u; a faithful informative-intervention specialization of the elementary-query lower family.

**Not established by this audit:** first historical priority for any of those synthesis results; superiority to annotated stable graph formulations; a complete literature exclusion argument; statistical recovery under HPL's minimal assumptions; polynomial total runtime; arbitrary hard interventions; samples; Lean verification.

The relevant conclusion is narrower and defensible: the adapter is not an automatic consequence of the cited raw representation/completion theorems, and the proof obligations it adds are necessary for this transfer. Whether the same complete adapter appears elsewhere remains a priority-review question, not a consequence of the counterexamples.

## 7. What remains for this exact claim

At the reviewed hand-proof level, no further mathematical gap in the selected exact-oracle theorem has been identified: the certificate identifies the separate augmented MAG equivalence classes; the common-source compression gives an effective complete finite carrier preserving the actual marked TCM; shared-mechanism faithful representatives prove realizability rather than merely graphical consistency; and filtering that carrier gives the full source-compatible TCM list. The elementary-query lower family and G7 transcript adapter have separate scoped reviews. This is a bounded completion statement about those manuscripts, not a guarantee against undiscovered errors.

The remaining delivery obligations are full source-to-kernel formalization, actual elaboration/checking when execution is separately permitted, and continued historical-priority review before any novelty claim. The formalization specification must prove the graph/separation and probabilistic source lemmas as well as the finite game, not replace them with axioms. The current proof-site gate remains unmet.

There are genuine mathematical questions outside the selected theorem: statistical recovery under HPL's weaker assumptions, quantitative finite-sample guarantees, stronger-oracle lower bounds, efficient total decoding, and hard interventions with selection. They are not missing premises silently delegated to a future proof, and they are not solved by the reviewed theorem. In particular this packet does not settle the unrestricted Section 7 partial-intervention problem under its weakest statistical assumptions. No easier replacement target is introduced to extend the completed exact-claim comparison.

## References and source-version notes

Sadeghi, Kayvan. Stable Mixed Graphs. Bernoulli 19(5B), 2330–2358, 2013; arXiv:1110.4168v3. Primary theorem and realization proofs inspected directly.
https://arxiv.org/pdf/1110.4168

Zhou, Zihan; Kocaoglu, Murat. Towards Completeness in Causal Discovery from Soft Interventions with Known Targets. ICML 2026, PMLR 306, 165069–165094. Primary pp. 4–7, Appendix B.1–B.5, Algorithms 1–7 and Appendix D.1–D.2 inspected directly. The word 'selection' in its 'transit selection set' means choosing witnesses, not selection bias.
https://raw.githubusercontent.com/mlresearch/v306/main/assets/zhou26s/zhou26s.pdf
https://proceedings.mlr.press/v306/zhou26s.html

Hou, Xiaotian; Park, Kwangmoon; Li, Hongzhe. Statistical Inference for Causal Discovery under Selection and Latent Variables via Single-Target Interventions. arXiv:2609.28856v1, 2026. Exact selected SIS source, separate-indicator equivalence and TCM target used throughout.
https://arxiv.org/html/2609.28856v1

[Full selected finite-realization proof](SELECTION-FINITE-REALIZATION.md)
[Exact query certificate](LATENT-SELECTION-IMEC-CERTIFICATE.md)
[Full-claim formalization specification](FULL-CLAIM-FORMALIZATION-HANDOFF.md)
