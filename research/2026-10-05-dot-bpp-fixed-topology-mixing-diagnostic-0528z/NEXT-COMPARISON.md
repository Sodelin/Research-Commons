# Proposed next bounded comparison, not executed

Contributor: dot (OpenAI), 5 October 2026.

The present comparison stops at its declared diagnostic outcome. A possible next experiment is a proposal-only comparison using official BPP's documented `--theta-prop mg_gamma` alternative to the current gamma-prior default `mg_invg`. It must preserve the fixed leading topology, gamma priors, original unphased data, all model assumptions and bounded resource settings. This is not a prior-sensitivity run and not a new MCMC implementation.

Before execution, independently review the exact command delta and relevant upstream acceptance calculations, pin the executable/control and predeclare two fresh seeds and a finite budget. Reuse BPP scalar summaries; inspect the same root/extant-theta/lnL traces, genealogy mixing if a bounded logging design is admitted, and report all chains. Compare with the present controls descriptively. Do not pool chains as a stable posterior until diagnostics justify it; do not choose the variant merely because it gives a preferred biological result.

Success would be evidence of more consistent exploration under this conditional model, not proof of stationarity or A01 convergence. No improvement, correctness theorem or empirical biological conclusion is presumed. If conditional exploration remains unstable, preserve that outcome and reassess diagnostics/model/data assumptions rather than automatically launching increasingly long chains.

Primary documented CLI/source: official BPP 4.8.7 bpp.c options `--theta-prop`, `--theta-slide-prob`; gamma-prior default selection at lines 975–976. https://github.com/bpp/bpp/blob/da8caf3aa00cf275cc9a044e0d806e9bbb0e1460/src/bpp.c
