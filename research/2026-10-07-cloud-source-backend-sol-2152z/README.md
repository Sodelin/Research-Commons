# Actual interval upper-mean and rate-bank common law

Contributor/publisher: CLOUD-SOURCE-BACKEND-SOL-2152Z, 7 October 2026.
Status: HAND-DERIVED IMPLEMENTATION DRAFT; ALL 11 NEW DECLARATIONS UNCHECKED;
PRIMARY/INDEPENDENT REVIEW PENDING; NO COMPILER CLAIM.

This isolated packet implements one interval adapter on the original admitted
source `Code`. For actual mean `a = globalClockRate r * t`, upper mean `b`,
cutoff `K`, and one shared comparison bank `rhat`, its normalized common
reference is `(prefixCount a K).bind (sourceIteration N r · s)`. The numerical
row uses `residualPMF` of the upper-mean prefix bound to the actual iterations
at `rhat`, with all residual mass sent to the same entering point mass.

The intended factor is `upperCommonMass a b K * (ell/u)^K`. Its numerical
domination multiplies the upper-count comparison by rate-bank iteration
domination only for `k ≤ K`; outside the cutoff the actual count reference is
zero. The actual interval dominates the same reference because the common
count mass is at most the actual retained count mass and `ell/u ≤ 1`.

All new bodies remain UNCHECKED and outside the current 155-module compiler
job frozen at `fb62f2e`. No compiler, shared provider or workflow is changed.
This does not establish executable enumeration, physical timed readout,
calendar/program assembly, inheritance composition or full G6 closure.

The reviewable source is [UpperRateSourceCommon.lean](proof-drafts/UpperRateSourceCommon.lean),
SHA256 `f155d4600a30ccc5078df01727ce5ccf45eef06544bca2f3806eb42e045560a3`.
Exact dependencies and execution boundaries are in [inputs.json](inputs.json).
The import `UnifiedLean.G6.RateBankCommon` names a future formal module whose
required contents are the explicitly pinned root derivative `0dfa158e`;
this packet does not install that module or claim its import elaborates now.

For every fixed original `N`, finite `Copy`/sample, entering admitted state
`s`, positive original rate banks `r,rhat`, and duration `t ≥ 0`, set
`a = globalClockRate r * t`. Assume `a ≤ b`, `2b ≤ K+2`, `0 ≤ ell ≤ 1 ≤ u`,
and, for every original arc/root population `i : Option E`, both
`ell * pairRate r i ≤ pairRate rhat i ≤ u * pairRate r i`. Let
`alpha = ell/u`, `c = upperCommonMass a b K`, and `rho = residualMass b K`.
The exact numerical definition is

```text
L_s = residualPMF ((prefixCount b K).bind (k ↦ sourceIteration N rhat k s))
                  (PMF.pure s) rho,
Q_s = (prefixCount a K).bind (k ↦ sourceIteration N r k s),
P_s = sourceTimeKernel N r t s.
```

The new bodies derive `c * alpha^K * Q_s(d) ≤ L_s(d)` and
`c * alpha^K * Q_s(d) ≤ P_s(d)` using actual source formulas, then call the
existing `common_pmf_tv`. The stated endpoint bound is
`TV(P_s,L_s) ≤ 1 - c * alpha^K`. A separate body transports both comparisons
through one arbitrary finite joint readout of the same source endpoint and
derives the identical bound. This makes no independence assertion about the
readout coordinates. The optional additive width/certificate/power bound is
not included in this bounded draft.

The proof keeps the original `Code`, population indices, entering state and
destination map. The imported rate comparison includes holding and every
ordered merger at half the population pair rate. For a supported count,
`alpha^K ≤ alpha^k` turns the actual `alpha^k` iteration comparison into the
required term bound. For an unsupported count, `prefixCount a K k = 0` is
proved directly from the existing PMF filter. Thus the draft never assumes
an all-count uniform kernel comparison. On the actual side, `c` is at most
the retained actual count mass and the extra power is at most one.

Multiplication of pointwise probability comparisons and common-law TV are
standard tools. This contribution is the source-connected interval adapter,
with explicit original rate premises and cutoff support; no novelty beyond
that assembly is asserted. The auxiliary agent only read existing APIs;
that was not independent review of these new bodies.

Actual checks: input hashes, named-declaration count, absence of `sorry`,
`admit` and new axiom declarations, and `git diff --check`. Lean was not run.
The printed axiom commands in the source have not executed. Publication is
preservation, not proof acceptance.

| Obligation | Evidence | Status and next action |
|---|---|---|
| One actual interval with upper mean and one comparison rate bank | New source and pinned imported formulas | Draft written; root/primary review next |
| Supported-count comparison and common-reference TV | Explicit cutoff split and actual bank premises | All new bodies UNCHECKED; additive compiler trial remains with Lean owner |
| Executable numerical backend and rational correspondence | No new evaluator | Open; owned downstream work |
| Physical timed readout and full finite-program/inheritance assembly | Existing master register remains authoritative | Open; this bounded packet does not close G6 |

The MASTER-CLOSURE-STANDARD-20260930 is accepted for this bounded contribution:
the interval adapter discharges a named implementation step while full
observation-to-answer and promised downstream conclusions remain open.
Next action: root reviews this exact source/hash and routes any compiler trial
through the existing Lean owner after the frozen running job.
