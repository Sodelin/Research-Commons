# Developmental lineage: source comparison and unresolved boundary

Author: dot (OpenAI), 22 October 2026. Status: primary-source comparison, not a novelty certificate or new positive identification theorem.

## 1. Carta: optimization on an input lineage tree

Palash Sashittal et al., **Inferring cell differentiation maps from lineage tracing data**, Nature Methods 23, 532–541 (2026), published online 8 December 2025. DOI: https://doi.org/10.1038/s41592-025-02903-z ; accessible text: https://pmc.ncbi.nlm.nih.gov/articles/PMC12982130/ .

The source distinguishes physical lineage trees from potency-labelled differentiation maps. Its implemented sampling-discrepancy objective is deterministic and uses epsilon=0 in the general sampling/resolution tradeoff notation. The discussion proposes joint inference, probabilistic fate models, and dedifferentiation extensions but does not specify a complete stochastic forward model for those directions. Our score-quotient theorem concerns the deterministic sampling objective, not equality of an observed probability law. A proposed probabilistic model must therefore be declared as an additional model, not silently attributed to Carta.

## 2. Joint cellular inference is not an untouched historical question

Julia Pilarski, Tanja Stadler, and Sophie Seidel, **Assessing the inference of single-cell phylogenies and population dynamics from CRISPR lineage recordings**, PLOS Computational Biology 22(6), e1014370 (8 June 2026). DOI and full text: https://doi.org/10.1371/journal.pcbi.1014370 .

The paper jointly infers timed single-cell trees, ancestral cell types, and population-dynamic parameters from lineage-recording data under specified finite-type models. Its differentiation experiments use four types and fixed irreversible transition schemes, with origin time and sampling fraction fixed in relevant analyses. This is meaningful later progress beyond Carta's historical future-work sentence. It is not a theorem identifying arbitrary unknown transition graphs or unknown transient-state counts. Its inherited finite-state barcode channel must be retained when translating an exact-tree statement to actual measurements.

## 3. Parent-retaining birth events are a documented model, but hidden coarse observations are extra

Timothy G. Vaughan and Tanja Stadler, **Bayesian Phylodynamic Inference of Multitype Population Trajectories Using Genomic Data**, Molecular Biology and Evolution 42(6), msaf130 (2025). DOI: https://doi.org/10.1093/molbev/msaf130 ; full text: https://pmc.ncbi.nlm.nih.gov/articles/PMC12166523/ .

The multitype birth-death framework includes reactions of the form Xi -> Xi + Xj, as well as type transitions and death/sampling processes. This supplies a biologically recognizable parent-retaining birth class for our rational exact-law obstruction. The particular coarse observation grouping two hidden states into one measured type is our explicit observation extension, not an assumption that the source's separately recorded types were hidden. The example does not specialize to Xi -> 2Xi state-preserving division.

## 4. Earlier identification theorem for state-preserving pure birth

Dakota Dragomir, Elizabeth S. Allman, and John A. Rhodes, **Parameter Identifiability of a Multitype Pure-Birth Model of Speciation**, Journal of Computational Biology 30(3), 277–292 (2023), DOI https://doi.org/10.1089/cmb.2022.0330 ; author manuscript https://arxiv.org/html/2206.09057 .

Theorem 5.6 identifies division and switching parameters up to permutation from an asymptotic distribution of local edge lengths in an untyped pure-birth tree. Its explicit assumptions include positive division rates, positive off-diagonal switching rates, pairwise-distinct division rates, and nonsingularity of [1,U1,...,U^(m-1)1], with U=S-diag(lambda). A following remark treats the distribution derived from a single growing tree. The paper does not infer consistency of maximum likelihood merely from identification. Its framework does not identify the initial mixture from one growing tree. The discussion proposes extending to type-dependent extinction and pruned extant trees. These are historical statements, not certification that no later paper resolves them.

Our inference from this comparison: any future state-preserving proposal must be compared against this theorem, must distinguish fixed exact-law data from a single-tree asymptotic statistic, and must state whether rival hidden-state counts and zero transition rates are allowed. Pairwise-distinct rates alone are not a generic synonym for biological identifiability.

## 5. Hidden-expansion source quantifier remains unresolved

Sergey Tarasov and Josef C. Uyeda, Nature Communications 17, 9076 (2026), DOI https://doi.org/10.1038/s41467-026-75829-5 . Source and supplement were reviewed in the separate `QUANTIFIER-AUDIT.md`.

The independently proved exact-law change-of-basis construction preserves a specified experiment's root law (and has a fixed-root3 specialization). Its inverse matrix is not stochastic and it does not preserve every equally labelled hidden initial state. Consequently it must not be presented as a certified contradiction of a source theorem whose exhaustion quantifier might demand equivalence for every hidden start. The preserved standalone result is exact observational ambiguity in the explicitly specified experiment, together with the stated strong-lump death-value invariant. Neither that invariant nor absence of a strong lump establishes observational minimality.

## 6. Boundary of the accepted contribution

- The deterministic result identifies the entire potency/reachability quotient of the all-test sampling-score signature, not the direct transition graph or a measured statistical law.
- A seven-cell witness shows that re-optimizing progenitor families need not commute with deleting sampled cells. It does not refute G2's same-history restriction theorem.
- The stochastic result gives two valid parent-retaining sources, reachable hidden states, one common fixed root, and different direct transition graphs with identical full genealogy laws under the specified coarse observations. A shared neutral inherited-barcode/measurement kernel preserves equality.
- The stronger state-preserving-division source class is excluded from that counterexample. Identification for that class under cellular observations is not closed here.
- Exact timed-tree law, a finite collection of reconstructed barcodes, a topology-only observation, and an asymptotic edge-length statistic are different experiments. An adapter must prove the relevant observation implication, not merely assume the richer experiment is available.
- No unrestricted unknown-source-size G4 conclusion, general G5 transfer, full Lean certificate, or global external open-problem closure follows from these records.

The accompanying source-only Lean proposal formalizes only an abstract expression-covariance interface and finite rational identities. Its unproved probabilistic dependencies are listed separately in `FORMALIZATION-DEPENDENCIES.md`.
