# Kernel receipt: SAT helper feasibility and selector counts

2026-11-25 UTC. Scoped standalone kernel verification, not an aggregate package build, a formal proof of the 9/10 pooling inequality, or a result on P vs NP.

Source hand result: [helper switch and pooling](https://github.com/Sodelin/Research-Commons/blob/c275cc5724d5895ea4d0f67bdd22d25c9240b29f/research/2026-11-24-vp-vnp-boolean-boundary/COMPACT-CUT-RANK-HELPER-SWITCH-POOLING.md). Module: [HelperSwitch.lean](HelperSwitch.lean). Compiler: Lean 4.33.1, Windows GNU official release, compiler commit 819816b2e0a3bf405af45ae5c7af2491d8f5bee6. No Mathlib dependency. Run from the containing directory:

```sh
elan run leanprover/lean4:v4.33.1 lean HelperSwitch.lean
```

Final clean run: exit 0, no warnings or errors. Local compiled input SHA-256 as reported by the runner: `9b5142ad15a2f02db97392b562a9eb437725a7ffa87692574ce6410d5a3663a8`. A first Windows attempt invoked an absolute path inside the sandbox, which Lean rejected as a nonportable module name because it contained an exclamation mark. The clean run used a relative module path.

`#print axioms` output:
```text
'ResearchCommons.HelperSwitch.eliminateRequirements' depends on axioms: [propext, Quot.sound]
'ResearchCommons.HelperSwitch.eliminateFamilies' depends on axioms: [propext, Quot.sound]
'ResearchCommons.HelperSwitch.helperExists' depends on axioms: [propext, Quot.sound]
'ResearchCommons.HelperSwitch.helperProjection' depends on axioms: [propext, Quot.sound]
'ResearchCommons.HelperSwitch.fairOutcomeCounts' does not depend on any axioms
```

The projection is pointwise for every assignment and all selector bits; no fairness or independence premise is needed. The broader statement covers any finite families of already-evaluated positive and negative requirements for one helper, not arbitrary quantified SAT counting. Fairness enters only when the eight selector triples are assigned equal weight. The 9/10 bound and exact pooled cross-ratio witness remain hand proof and finite replay until separately formalized.
