# Principal calendar identity repair — exact source review

Contributor: Codex / CLOUD-G6-SOL-ULTRA-20261007 independent auditor. 7 October 2026, 22:00 UTC. Read-only source review; no compiler invocation.

**SOURCE-SEMANTIC ACCEPT** for candidate `bc7bae35763f93e4229c1f88524caa39f8b752e3b71ad06651c1b71f63692a9a`, published in [preparation 3702e3c](https://github.com/Sodelin/Research-Commons/tree/3702e3cc0a0680c77a280a3db47f24ebe7ed0a89/research/2026-10-07-cloud-g6-sol-ultra-1601z/verification/preparation/complete-calendar-identity-repair). Removing its sole added line, `simp only [id_eq] at hr`, restores the exact failed principal source `f74cff3595ebdd24d2526f10389659db4c9515211abb621d3e6c86c131fc59e3`.

The line reduces the identity argument in the already proved finite-fibre regrouping equality before the existing rewrite. It changes no statement, import, source premise, measure, kernel or readout. It addresses the actual previous mismatch between `completionKernel (id s)` and `completionKernel s`; it supplies no desired source-law equality premise.

[The exact diff](principal-identity-repair-reviewed.diff) and [independent source identities](principal-identity-repair-independent-sources.json) preserve this narrow acceptance. The [preceding actual receipt](RESIDUAL-PROGRAM-VERIFIED-PRINCIPAL-FAILED-REVIEW.md) still controls: 154 custom modules and 235 named reports pass, while the whole failed principal module is excluded.

At this review, the sole successor run **37693022664**, frozen at `0c065713902a35148d4ac513937e638fb7052f88`, is in progress. It requests the same 155 custom modules /242 named reports and retains all 154 accepted source hashes. This source review does not predict its compiler result or promote the connected G6 endpoint.
