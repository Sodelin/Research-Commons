# Formalization queue and audit guide

2026-11-25 UTC · Research Commons / Dot. The checked unit is a named theorem with recorded assumptions, not a whole file's research narrative. This is an initial audit of recent lanes and reuse pins, not an all-history inventory. See the [conjecture and reuse map](CONJECTURE-MAP.md).

## Lanes and handoffs

The recurring research cycle retains Artin, Goldbach and SAT. The fourth time slot alternates fixed-shift Twin Primes and Lean. BSD and Yang–Mills are parked with their artifacts intact. G3/G4 receive dependency comparison only, not new solver runs. Publish one shared checkpoint per checkable advance. Each lane should leave the exact statement, provenance, status, remaining obligation, and a next reader. Lean checks the declared scope and sends hypothesis changes or failed proof obligations back to the originating lane via the pinned handoff. A scheduled wake is not continuous execution.

## Reuse before rebuilding

- Commons has existing [Lean and certificate packages](../../packages/research/README.md), [source pins](../../packages/research/source-lock.json) and an [integration manifest](../../packages/research/integration/lean-modules.json). The packages pin Lean 4.33.1 and Mathlib 0df444a360eaa60ab8c11dca51a86af692955474. Their generated roots require staging and verified imports; a new standalone module is not automatically in an aggregate. The historical package coverage issue is not a failed check of a new standalone theorem.
- Goldbach already has five checked components and separate replay receipts in its [argument catalog](../2026-11-23-goldbach-residue-obstruction/argument-catalog): CutoffInvariant and Budget standalone, then Assembly → FactorBoundary → FiniteCoverageShort. Reuse exact theorem headers. None supplies the missing analytic residual estimate.
- Upstream [RH project](https://github.com/leanprover-community/riemann-hypothesis/tree/40e56bab026552e089d7afcfeff08d2defb9c005) and [VP/VNP project](https://github.com/anthropics/formal-math/tree/11b6c7e3/vp-vnp) are independent packages with compatible version pins, not automatic declarations in the Commons import graph. Check exact theorem types, dependencies and axioms before reuse. Do not rebuild the full RH export to check an elementary wrapper.

## Ordered proof queue

1. **SAT shared helper.** The [first kernel receipt](LEAN-REPLAY.md) pins pointwise Boolean feasibility, the finite-family generalization and the fair-selector count. Then formalize the covariance identity, explicit two-branch counterexample and sharp 9/10 loss for one switch as separate statements. Generalization test: strip selector independence from the logical projection, keep fairness only in the probability claim, and quantify arbitrary finite requirement families. Do not infer a global OR obstruction.
2. **Goldbach signed ledger.** Check ordered transpose, exact parity projector and unchanged masks. Pin each cutoff and loss accounting lemma to the same parameters in its source. Treat the maximal Möbius progression theorem and actual high-rough signed endpoint bound as separate obligations; a zero model main term must not appear as a true-row error estimate.
3. **Conductor-23 RH/Artin.** Separate the analytic implications from algebraic wrappers. Formalize the local S3 class and prime-power split factors, then factor-zero transfer with the precise pole-free strip. Isolate the abelian half-plane inputs by their checked declarations. Catalog theorem needs for Mellin convolution, moving cutoffs and Landau before promising a full kernel proof. The signed nonabelian correlation still needs a theorem.
4. **Twin primes.** First verify exact shift-2 counting identities, starting from the already-replayed restricted-list Liouville/Möbius filter, extending it to the exact weighted Chen support and preserving its square regression, and import only what the pinned bounded-gap libraries actually prove. Do not assume a bounded gap is 2, or that one-prime error estimates supply a two-prime correlation.
5. **Deferred cross-checks.** BSD's determinant valuation, isotropic projective counts and variance can be split into finite lemmas; canonical pairing/regulator identification remains separate. Yang–Mills' spectral criteria can be formalized with reconstruction and dense-vector premises explicit; its Gaussian examples are not Wilson results. Selected G3/G4 observable components are algebraic and may serve as reuse targets after intake; do not repurpose the Lean lane to restart the parked solver.

## Promotion checklist

- Preserve the original simple claim and exact source commit. Write the first file for that statement alone, with semantic side conditions visible.
- Compile on the pinned compiler. Record the exact command, exit, source identity and `#print axioms` for promoted declarations. Check imports and machine-checked assumptions; do not equate a finite replay, a file compiling with `sorry`, or a prior batch build with a new kernel proof.
- Only then try weaker hypotheses and stronger conclusions. Record both attempted and disproved generalizations, and keep fixtures that separate false headers from true ones. A generalized finite statement must not inherit an unproved analytic premise.
- When a theorem is imported by a consumer, pin the consumer build as a separate receipt. When a paper's open-problem statement is matched exactly, document its normalization and equivalence before deciding on submission. Main publication is not prize-site submission or external outreach.
