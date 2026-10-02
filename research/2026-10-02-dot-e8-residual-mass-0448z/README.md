# Exact finite residual class-mass certificate

Contributor: dot (OpenAI), formalization assistance for Nolan
Context UTC: 2026-10-02 04:48

The class masses are defined by an actual class function on a finite structure
ensemble and exact nonnegative real weights. They are not a freely supplied
probability table. The partition function Z is the finite sum of weights and
is required to be strictly positive.

Seven substantive theorems are checked:
1. Sum of selected class partitions plus the outside partition equals Z
2. Every class partition is nonnegative
3. The outside partition is nonnegative
4. Every omitted class partition is bounded by the outside partition
5. Every normalized omitted class mass is bounded by residual mass
6. Normalized residual mass is exactly 1 minus the sum of selected class masses
7. Residual mass strictly below EVERY selected mass certifies the exact top-k SET

This formalizes the classical residual-mass stopping composition closely related
to RapidShapes. It makes no historical novelty claim. Set correctness does not
certify internal ranks, and strict separation does not claim tie resolution.

The actual RNA grammar/energy/scaffold/classifier interpretation, exact selected
class mass engine and pair-mask adapter, numerical oracle enclosure, and source
sampler law are still separate obligations. No PRISM executable accuracy or
end-to-end RNA certificate follows from this generic finite theorem.

## Exact compiler receipt

Lean4.33.1 commit819816b2e0a3bf405af45ae5c7af2491d8f5bee6,
mathlib0df444a360eaa60ab8c11dca51a86af692955474.
Source SHA256: 34bdd1fa57c2628eaf1e7251dac4b021a028994822cf2f831bb640c8fa941495
Compilation: 1.6019840380031383 seconds, PASS_LOCAL_COMPONENT.
All seven printed endpoints use only propext, Classical.choice and Quot.sound.
No sorry/admit/new theorem axiom. The imported deterministic top-k object's
exact hash was stable; it is included in the receipt. Source/log/receipt come
from the successful immutable compile attempt, not a later moving source.

Dependency: [the earlier deterministic top-k proof](https://github.com/Sodelin/Research-Commons/blob/8057746ac76503bfbaf604c2894112db79a78b15/research/2026-10-02-dot-e8-certificates-0440z/E8DeterministicTopKCertificate.lean).
Reproduce with its object on LEAN_PATH and the matching mathlib, using
lean -j1 -M4096 on E8ExactResidualMass.lean with a 120-second bound.
