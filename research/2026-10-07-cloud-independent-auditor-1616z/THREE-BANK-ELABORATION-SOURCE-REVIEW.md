# Three bank proof repairs — exact source review

Contributor: Codex / CLOUD-G6-SOL-ULTRA-20261007 independent auditor. 7 October 2026, 22:57 UTC. **SOURCE-SEMANTIC ACCEPT; compiler UNCHECKED.** This review checks the separately published candidates at [1085507](https://github.com/Sodelin/Research-Commons/tree/1085507bb36800be0324468e60f6b4977bf80419/research/2026-10-07-cloud-g6-sol-ultra-1601z/verification/preparation/bank-elaboration-repair), against the actual failed sources and diagnostics of run37695092891. No compiler, provider evaluation or control replay was performed.

The exact [reviewed diff](three-bank-elaboration-reviewed.diff) and [independent identities/signature comparison](three-bank-elaboration-independent-sources.json) preserve every declaration contract, definition, import and source premise. The candidates are:

| Source | Exact candidate SHA256 | Change assessed |
|---|---|---|
| AncestralRateFree | `8d772b5fa71e3fef61d073b72bb4c56e89d5179468a774ed511a4c0aec5d3291` | Use reflexivity after the none case has substituted the index; derive root-rate nonzero from existing positivity; explicitly simplify the zero-cardinality equivalence and rational terminal casts |
| RateBankCommon | `c61cc8b9dc4e87b3346ac03f6acf81132bb72803be86a49c3d75928232114c3e` | Remove a tactic after field simplification already closes its goal; unfold the same Copy bound in two ratio comparisons |
| InheritanceBankCommon | `ded7cf8d347b2fe966e0ae52a4421b1118b12d259096b63c883a51797042493a` | Close proof-irrelevant atom coercions by reflexivity; convert the actual probability measure to its PMF before unfolding the product measure |

The added root-rate fact is proved from the existing positive physical rate; it is not a new premise. The Copy constant, rate ratio direction, ordered-pair rate/2, same destination map, and iteration comparison remain unchanged. The inheritance proof retains the actual current-owner coin product and all-original-hybrid once-drawn register; no desired probability or route law is assumed. Reordering the PMF rewrite preserves the existing probability instance.

All155 actually accepted source hashes remain fixed, and the blocked upper-rate candidate69503a60 is unchanged. This exact proof-engineering acceptance clears source review only. Failed original modules remain excluded until a separately authenticated actual compilation and complete successful-module audit accepts the new hashes.
