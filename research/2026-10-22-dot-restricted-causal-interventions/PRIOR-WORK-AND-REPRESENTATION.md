# Prior work and the representation boundary

Author: dot (OpenAI). Checked: 22 October 2026 UTC.
Status: Source audit and obligation ledger, updated through the reviewed selected finite-realization hand theorem; not historical-priority certification.

## Primary providers and what they already establish

1. **Hou, Park and Li (2026).** The starting paper supplies full-coverage TCM identification, quadratic full-coverage constraint-query complexity, the selected anterior/adjacency identities, and the separate-indicator IMEC criterion. The current certificate synthesis uses these as prior lemmas. It does not rename them as G7 consequences. Section 7's partial-coverage and hard-intervention directions have distinct assumptions.
https://arxiv.org/html/2609.28856v1

2. **Richardson and Spirtes (2002); Spirtes and Richardson (1997); Ali, Richardson and Spirtes (2009).** These provide MAG projection/separation and equivalence theory. The shared-separator certificate lemma is an explicit corollary of their discriminating-path argument, not a new MAG equivalence criterion. The 2009 paper notes that the 1997 computational complexity claim was incorrect; only the stated equivalence criterion is used here.
https://www.cmu.edu/dietrich/philosophy/docs/spirtes/annals2002.pdf
https://arxiv.org/pdf/0908.3605

3. **Kocaoglu, Jaber, Shanmugam and Bareinboim (2019).** Their soft-intervention latent-variable paper develops an augmented representation using controlled mechanism changes and invariances across regimes, and gives a sound FCI extension. Those contributions precede this packet. Its single joint augmentation and intervention-set differences should not be substituted without proof for HPL's selected single-indicator equivalence. The source's assumptions and target construction were read directly.
https://proceedings.neurips.cc/paper/2019/file/c3d96fbd5b1b45096ff04c04038fff5d-Paper.pdf

4. **Zhou and Kocaoglu (ICML 2026).** The full primary PDF and relevant appendices have now been read directly. Page 4 expressly excludes selection; Definitions 4.3–4.6 use a joint pair-of-regimes augmentation. Lemmas 5.3/5.5 and Theorem 5.7 give common-source ADMG realization and an exact test, and Theorem 5.8 gives exhaustive completion through LIST. These are definite prior common-source realization and enumeration results in their domain, not inventions of this packet. Their exact no-selection test rejects a valid selected HPL example, and converting the joint target to HPL's separate target requires proof. The earlier abstract-only access statement is superseded; no security challenge was bypassed. See the full theorem-by-theorem reconciliation and counterexamples below.
https://proceedings.mlr.press/v306/zhou26s.html
https://raw.githubusercontent.com/mlresearch/v306/main/assets/zhou26s/zhou26s.pdf

5. **Zhou, Elahi and Kocaoglu (2025/2026).** Their hard-intervention paper characterizes an interventional equivalence using a tuple of augmented graphs and gives a sound learner. Section 2 expressly assumes no selection bias; the new hard-intervention invariances can differ from soft ones nonlocally. We read the versioned primary text. It does not prove our selected soft-intervention theorem or settle hard interventions with selection. Conversely, the existence of a tuple target for hard regimes is their prior work, not an innovation here.
https://arxiv.org/html/2505.01037v2

6. **Luo, Li, Chen, Dai and Zhang (ICLR 2026).** Their latent/post-treatment-selection intervention work and F-FCI are relevant partial-coverage prior work. HPL explicitly distinguishes its equivalence from their joint-indicator representation. A transfer must reconcile the target, not merely compare algorithm names.
https://arxiv.org/abs/2509.25800

7. **Zhang, Shiragur and Uhler (2024); Franquesa Monés, Zhang and Uhler (2026).** Their observational elementary-CI lower-bound constructions supply the hard-family mechanism. The barrier manuscript's contribution is a concrete informative restricted-intervention specialization, faithful shared-source realization, and exact finite G7 game calculation, not the discovery of exponential CI lower bounds.
https://proceedings.mlr.press/v238/zhang24k/zhang24k.pdf
https://arxiv.org/html/2603.21844v1

Targeted searches for partial-intervention query bounds parameterized by the number of untargeted observed variables did not establish prior occurrence or novelty of the exact bound in this packet. This negative search result is not evidence of first priority. The complete-record and paper-version checks remain necessary before any novelty claim.

8. **Richardson, Evans, Robins and Shpitser (2023), following Verma and Pearl (1990).** Proposition 1 and Supplement A.3–A.4 supply the bow-permitting latent projection and its exact observed-separation preservation. Both finite-realization companions use this classical theorem, not new projection theory.
https://arxiv.org/pdf/1701.06686v6

9. **Sadeghi (2013).** Stable Mixed Graphs develops finite mixed graphical representations of DAG independences after latent marginalization and selection conditioning, with closure and DAG-representation results. Algorithms 1–3, Propositions 2/4/5/8, Theorems 1–6 and the realization proofs were inspected directly. These are essential prior providers, including canonical selected DAG witnesses. Explicit examples now show why an ordinary observed summary graph, an unannotated ribbonless graph, or unrestricted canonical expansion of each augmented graph does not automatically preserve the named HPL source and target. Stronger annotated stable-graph approaches are not ruled out, and historical priority of this particular application remains unestablished.
https://arxiv.org/pdf/1110.4168

## The representation obligation and its subsequent resolution status

The certificate manuscript determines every single-indicator MAG equivalence class and proves a bidirectional source-level decoder. If the requested output is this finite lossless descriptor, the exact query theorem is complete conditional on its stated graph facts and faithfulness assumptions.

If an application instead requires an explicit list of **all realizable TCMs**, one further theorem is needed:

Given the observed labels, available targets, and a proposed combined mixed graph, decide whether there exists one finite HPL SIS with arbitrary latent/selection sets whose separate augmented MAGs yield that graph, allowing the own-target edges to be restored before trimming.

Independent realizability of the separate MAGs is insufficient as a proof: the same original graph and mechanisms must serve every regime. A finite list of possible MAG markings does not supply a realizability decision or a bound on latent witnesses.

Three attempted shortcuts are invalid:
- Treating a Cartesian product of separately compatible MAG classes as a list of jointly compatible sources.
- Invoking the canonical DAG of each MAG separately; those canonical DAGs need not share a common underlying SIS with indicators attached only to their specified targets.
- Claiming that a finite observable response alphabet gives an effective complete source registry. A finite semantic quotient exists, but deciding which classes are realized is an additional problem.

The no-selection companion now supplies a reviewed finite registry through classical bow-preserving projection. The selected companion supplies a separately reviewed complete hand theorem: retain the projected observed ADMG, a flag set of direct observed parents of selection, and marked endpoint-pair possibilities through bidirected selection components. The source-compression proof includes complete path contraction/lifting, selection-only loop removal, ancestry preservation, named-indicator compatibility, marked MAG equality, and faithful fixed-selected-slice representatives. It yields a 2^n 96^choose(n,2) registry and exact TCM enumeration. Its own scoped hand-review pass was received at 06:51 UTC; this is not machine verification.

The earlier common-source obstacle is therefore addressed by a full reviewed hand proof rather than silently bypassed. The exact comparison with stable mixed/summary graphs and the full 2026 completion algorithm is now recorded in [PRIOR-WORK-EXACT-CLAIM-RECONCILIATION.md](PRIOR-WORK-EXACT-CLAIM-RECONCILIATION.md). Its transfer counterexamples have a scoped hand review; the author's direct Zhou source inspection was not independently duplicated by that reviewer. The cited statements do not automatically supply the selected named-root adapter, but no historical novelty follows. Full-law equivalence, efficient total runtime, minimal-statistical faithfulness, hard interventions with selection, and machine verification remain outside the claim.

## Verification boundary

All claimed checks were source reading and hand mathematics. No provider's software was installed or run. No theorem in this ledger is claimed to be newly kernel-verified. Each manuscript's own scoped review status is recorded in HAND-REVIEW-2026-10-22.md.
