# Theorem growth: propose scope changes, check proofs and adapters

Keep the informal discovery pass, but make its output an exact contract and a small dependency graph rather than prose alone. Pin the original theorem, its assumptions and definitions; reuse exact declarations where possible; route only the missing obligations into proof writing. A candidate is accepted only when its own proof checks and an independently checked adapter recovers the original interface. Treat failed search, counterexample, and verified strengthening as distinct outputs.

## First executable pilot

`grow_linear.py` checks the pinned original integer certificate, then runs bounded, greedy assumption deletion. For each deletion it asks Z3 to synthesize a new bounded witness including a scale, and accepts only after Lean checks the same variables, exact premises, and original target. This is not just stripping zeros from a previous witness. The supplied [fixture](growth-fixture.json) uses the premise x≤1 directly at first. The worker removes that originally used premise, derives 2x≤3 from 2x+y≤3 and −y≤0, and checks x≤1 by integer rounding. A separate importing Lean consumer recovered the full old interface using the new theorem. Neither retained premise suffices alone, with exact controls (x,y)=(2,−1) and (2,0). The [machine receipt](growth-fixture.receipt.json) records the search, verified scope and artifacts. This is a restricted greedy search, not global minimality or a general Lean proof transformer.

```sh
python3 grow_linear.py growth-fixture.json "$(sha256sum growth-fixture.json | cut -d' ' -f1)" /path/to/libz3.so /path/to/pinned/lean fresh-output
```

## Unifying layer

1. Inventory a reviewed large module read-only: exact declaration types, proof dependencies, axioms, stable IDs and source/toolchain pins. Candidate generation is separate from proof checking.
2. Generate bounded candidate changes such as dropping a hypothesis, replacing a concrete structure with a small interface, lifting a parameter, or splitting a reusable lemma off the proof. Use counterexample checks first where meaningful. Measure coverage and avoid vacuous assumptions.
3. Verify the changed theorem and old-from-new adapter. Feed only verified, distinct results into subsequent rounds, capped by budget and with dependency-aware identities; do not run recursion over arbitrary imported code.
4. Scale on the existing checked package inventory before selecting a few declarations from a named GRH or Navier–Stokes formalization. Whole-module processing is not the same as removing RH or a PDE's core analytic input. No such large module was compiled or generalized by this pilot. Python scheduling and Lean checking suffice now; Rust is only justified if profiling points to the indexing or queue path and would not replace isolation or proof checking.
