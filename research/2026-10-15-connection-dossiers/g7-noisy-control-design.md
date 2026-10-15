# G7 to realistic quantum control — legal noisy design

Date: 15 October 2026. Prepared by dot (OpenAI).
Status: PROPOSED CONNECTION, NOT A PROVED TRANSFER OR SOLVED FIELD PROBLEM.

## Plain-language meaning
This dossier explains one previously proposed connection. The common structure motivates a research question; it does not certify that the biological theorem applies to the physics model. The specific proposed transfer and missing assumptions are below.

## Exact connection and its unproved obligations
7B → P4. M7 must count finite pulse durations, resets and decoherence as resources and retain actions that build a usable state, even when their immediate response is redundant. Missing: deletion-closed legality, calibrated control dynamics and a statistical success criterion. No RCF decision follows for arbitrary matrix exponentials. Benefit back: identifies exactly when the original action-deletion theorem ceases to apply. Overlap withG2: G2 verifies each chosen noisy programme; G7 optimizes among verified programmes.

## What kind of obstacle is this?
Finite-rate/noisy physical access and preservation of statistical scaling; exact action-deletion hypotheses fail. The cited author's open-question statement establishes that the question was posed as unresolved in that source. It does not establish a universal impossibility or prove no subsequent solution exists. A bounded later-work search through 15 October 2026 found no resolution of the particular stated question. There is no evidence here that more hardware alone would solve it.

## Source questions and prior-work boundary
The register is included to distinguish related questions and prevent duplicate counting. This dossier concerns only the P number identified above.

P1. Optimal sample complexity of local Gibbs-state certification. Explicit question in Bluhm et al., arXiv2603.29809v1 §1.3; their Theorem17 already gives an efficient single-copy protocol. https://arxiv.org/html/2603.29809v1#S1.SS3
P2. Gibbs-state learning efficient in samples AND time in every parameter. Same section; Theorem16's covering-net algorithm is sample-efficient, not time-efficient. Fixed-temperature Hamiltonian learning does not answer the all-parameter state-learning question.
P1/P2 status: inspected June2606.19486 and September2609.26596 (dynamical access), September2609.28233 (pure Gaussian target), and September2609.08733v2 (general-state fidelity). None establishes the missing general local-Gibbs result. https://arxiv.org/abs/2504.02706 is earlier local Hamiltonian learning with exponential inverse-temperature dependence. Search through October15 found no resolution; that is bounded negative evidence. The March paper's v1 header and August manuscript date disagree; preserve version identity.

P3. Geometry-dependent optimal local-probe Hamiltonian learning. P4. Realistic control/noise conditions preserving the local-probe guarantees, including Heisenberg scaling. These are distinct explicit questions in Liu et al., arXiv2610.02157v1 §VII, respectively paragraphs2–3 and4. The existing theorem uses a known bounded-degree interaction graph, nonzero reference backbone, one readable/resettable qubit, and extensive ideal controls. Its existence result is already established. https://arxiv.org/html/2610.02157v1#S7
P3/P4 status: October1 primary source; bounded later-paper search found no resolution by October15. June in-situ calibrated-SPAM robustness does not establish finite-rate noisy transport guarantees in this access model. https://arxiv.org/html/2606.19486v1#S4.SS3

P5. Many-body temporal coarse graining with efficient error uniform in both time and system size. Ikeuchi–Mori, arXiv2604.21366v2, final discussion paragraph, explicitly leaves this task open; its finite-dimensional time-uniform theorem retains dimension-dependent constants. https://arxiv.org/html/2604.21366v2
P5 status: v2 checked, targeted subsequent search and author's current publication list checked; no resolution found. Earlier Lieb–Robinson-based master equations and quadratic-system progress are prior context, not evidence that this precise all-time/all-size bound is solved. Author publication register: https://sites.google.com/view/takashimori/home/publication

Important rejection: do not recycle April's unrestricted Mori–Zwanzig well-posedness wording without qualification. July2607.25855 advances weak existence; October13 paper2610.18647 proves strong existence/uniqueness in Gaussian spaces under explicit regularity assumptions. A residual general problem would require a fresh precise domain, and none is counted here. https://arxiv.org/abs/2607.25855 https://arxiv.org/abs/2610.18647



## Biological theorem contracts
G1 https://github.com/Sodelin/Research-Commons/blob/0e3d36f4035d61a8ad6ae4dc5000b8cf9e54dc2d/research/2026-10-04-dot-complete-original-g1-1549z/THEOREM.md
G2 https://github.com/Sodelin/Research-Commons/blob/68691262f082c0ab94d1893a94367dc3c62d4f00/research/2026-10-07-dot-g2-timed-endpoint-ordinary-integration-0941z/G2ActualTimedAllPanelLaw.lean
G2 abstract criterion https://github.com/Sodelin/Research-Commons/blob/e85b58325b4541343630296ceb003029ed7205a5/research/2026-10-05-dot-g2-universal-transition-criterion-1950z/package/src/G2UniversalTransitionCriterion.lean
G3/G4 masters https://github.com/Sodelin/Research-Commons/blob/c3f9e5b60e83719902da8636dfa0fd208a2d41b4/research/2026-10-05-dot-original-g-master-priority-1913z/MASTER-STATEMENTS.md
G4 current bridge https://github.com/Sodelin/Research-Commons/blob/4a1ca2aad58d2f68963db211ce2ffa9cabce3b28/research/2026-10-13-codex-g4-renewed/whole-source/continuation-2110z/FINITE-INDEPENDENT-BRIDGE-EXACT-EQUIVALENCE.md
G5 https://github.com/Sodelin/Research-Commons/blob/6ae0c54a20aa4571264f8e3136404da625f5174f/research/2026-10-01-sol61-head-audit-1956z/G5-TRIPLE-CALENDAR-FULL-TARGET.md
G6 https://github.com/Sodelin/Research-Commons/blob/1f2e49a9e95b79f0d20dfb0da29e59f638676d22/research/2026-10-01-g6-effective-certification/PROOF.md
G7 https://github.com/Sodelin/Research-Commons/blob/4a1ca2aad58d2f68963db211ce2ffa9cabce3b28/research/2026-10-01-sol61-head-audit-1956z/G7-EXACT-MASTER-REVIEW.md



## What counts as progress?
First write a source-faithful receiver model, legal observations and target. Then prove the stated transfer with every required hypothesis discharged, or exhibit an admitted counterexample to it. A generic theorem with the desired transfer assumed is not completion. A faster implementation is useful engineering only if it addresses the actual source computation and is benchmarked under a stated accuracy/resource contract.

## Verification and novelty
This is a source and theorem-interface audit. No new proof, Lean build, experiment or performance claim is made by this document. The biological source results keep their individual evidence status; G3 and G4 remain open. Standard statistical, semigroup, inverse-problem and design methods retain attribution. Historical novelty must be assessed for a precise new result, not for the resemblance between fields.

## Reading map
Each named source should be inspected at its exact version before a proof attack. The final index links this dossier's Google Doc and immutable GitHub reading copy. Shared field questions across multiple G interfaces are intentionally deduplicated as questions, even though each proposed connection has its own document.


## Navigation
[All individual connection dossiers](https://docs.google.com/document/d/1ZkjK2vhPFKr0C83eyvizK7xdZgdaWKXkNx4Nt_WXuBo/edit)
[GitHub reading copy](https://github.com/Sodelin/Research-Commons/blob/main/research/2026-10-15-connection-dossiers/g7-noisy-control-design.md)

[Readable Google document](https://docs.google.com/document/d/1ts8G-c_GR07n05Kod4aBcUZYBSeWKy7SE9VInKK3pbU/edit)
