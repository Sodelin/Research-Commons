# P1 tactic decision after paid-prior calibration

18 October 2026, 09:08 UTC. Attributed research coordination note by dot (OpenAI), working with Nolan.

## Decision and reason

Prioritize **direct alternative-error analysis of the existing nonlinear mixture effect**. Further classical-prior acquisition obstructions are not the default next task. The [reviewed Gaussian and paid-calibration packet](https://github.com/Sodelin/Research-Commons/blob/67f84fd83415bcb36d63a13095cda56cc6692e9d/research/2026-10-18-dot-paid-prior-calibration-0901z/README.md) already identifies what its particular good-mass certificate costs. It does not establish a lower bound on the actual mixture test's error or on unrestricted P1 testing. Logarithmic improvements remain possible.

The expected benefit is a bound on the actual decision measurement, rather than another exclusion of a restricted method. This is a selected research direction, not a proved improvement or a claim that classical methods must be abandoned.

## Exact remaining mathematical step

Use the known, source-independent witness operators and weights from the [reviewed nonlinear-mixture construction](https://github.com/Sodelin/Research-Commons/blob/7ba73e425f8e26fdea8a03dea6bd536117c3e413/research/2026-10-18-dot-nonlinear-mixture-0654z/README.md). For paired input omega=rho tensor sigma, its effect is

    A_n = sum_j pi_j exp(-lambda sum_(i=1)^n D_j^(i)),
    E_n = A_n(A_n+tau I)^(-1).

The null error is already controlled. The next useful result would bound

    Tr[omega^tensor n tau(A_n+tau I)^(-1)]

uniformly over every admitted epsilon-far pair, while fully charging the 2n original copies and any additional acquisition. The goal is an improvement over the accepted [general upper bound13](https://github.com/Sodelin/Research-Commons/blob/809dcb6dcef78da700fddd888e9177bcff098b0f/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-CERTIFICATION-UPPER-13.md), which is O(M log M) at fixed parameters, M=sum_(j=1)^k 3^j binom(N,j).

The risk is precise: the existing noncommuting inverse comparison controls this error through a uniformly guaranteed mass of negative witnesses. Reusing that same sufficient bound, or assuming a source-specific prior or instrument is free, supplies no new decision guarantee. Any sharper analysis must retain the actual noncommuting operators and prove its uniform alternative bound, rather than infer it from parameter count, span or the null moment alone.

A quantum-output pilot is secondary. It requires an explicit instrument, a hard total-copy budget, and a joint error analysis with the retained program and later copies. Neither the classical selected-prior tradeoff nor an uncharged quantum-program intuition settles that route.

## Preserved scope and verification

The [current full-scope record](https://github.com/Sodelin/Research-Commons/blob/5511a0c0a11688ad47c638aed556b38efa1c18be/research/2026-10-07-dot-full-scope-reconciliation-1003z/CURRENT-SCOPE.md) remains authoritative. P1 retains two unknown coefficientwise-bounded k-local Gibbs states, common fixed known beta, unrestricted degree, full trace-norm separation, arbitrary collective/adaptive measurements and TOTAL physical-copy accounting. All accepted upper/lower bounds and their domains remain intact. The G3, G4 and P5 responsibilities and full targets are unchanged.

This checkpoint records a tactic decision only. It adds no proof, execution, historical novelty claim or full-master closure. New mathematical claims require their own stated assumptions and review.
