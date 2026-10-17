# Reviewed 1 mK forward-model control

17 October 2026 UTC. dot (OpenAI), with Nolan.

The refined 64-cell exact enclosure certifies a sufficient measurement budget at 1 mK for the unchanged positive rational 60-site control at B=2 meV: ideal warm conductance is at most 0.46749492079652594 e²/h and every report within 0.001 e²/h yields the stated determinant lower bound above 0.05925, with zero model drift. These displayed decimals summarize the exact rational records.

This is a known-Hamiltonian forward-model validation. The bound uses its already certified zero-energy conductance, which independently gives a stronger sign certificate. It does not infer the sign of an unknown experimental device, validate the 1 eV barrier physically, establish a universal temperature threshold, or demonstrate a practical apparatus. No Lean verification or novelty is claimed.

## Evidence and provenance

- [Independent review](../refined-thermal-independent/INDEPENDENT-REVIEW.md): full interval argument, replay of all 60 valid inverse witnesses and inclusion of four worst-case cells, plus an independently authored rational Fermi-mass checker.
- [Exact refined result](RESULT.json) and [Fermi integration result](CDF-RESULT.json).
- [Coordinating replay](REPLAY-REVIEW.md).
- [Original candidate README](README.md), preserved unchanged with its historical pending-review status; the independent review supersedes that status.
- [Original enclosure argument](../piecewise-thermal-execution/ARGUMENT.md), original and reweighted failures, all prerequisite witnesses and scripts are preserved unchanged in the sibling directory.
- [Complete additive file manifest](../REFINED-PUBLICATION-MANIFEST.json).

Run saved-cell replay from this directory with its sibling directories intact. The previous thermal-budget-execution data remain prerequisites; no prior file is replaced. Floating-point inverse proposals are checked by exact residual arithmetic. All failed cells retain the full rigorous upper bound 4; none is omitted. Temperature-dependent Hamiltonians, contact uncertainty, dissipation and acquisition/model-error budgets remain separate physical obligations.

The relevant future inverse question concerns opposite-target observation separation over an independently admitted device class. The classical separation criterion alone does not establish a new open problem or solve that inverse question. Prior-work coverage must be checked before further research expansion.
