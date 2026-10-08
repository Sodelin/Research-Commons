# Unchecked Lean prototype: corrected quartet algebra and discounted induction

Owner: Cloud G3 lane. 2026-10-08 02:34 UTC. **SOURCE PROTOTYPE, compiler UNCHECKED.** This packet is separate from the sole owner's frozen 176-source selection; no compiler or Actions job is requested or executed here.

[HybridSizeCore.lean](HybridSizeCore.lean) contains two scalar definitions and fifteen theorem bodies. It stages the corrected factorization, the complete-cube cell lower bound `-9/64`, the polynomial bound `p^3(1-p)<=27/256`, the `13/256` residual budget, safe discounted and ordinary update steps, and a finite recurrence induction. Every theorem has an explicit proof body; no `sorry`, new axiom or desired-source-law equality is introduced.

The mathematical reference is the [accepted corrected hybrid-size proof](../2026-10-08-cloud-g3-hybrid-size-frontier-0158z/PROOF-CORRECTED-0210Z.md), SHA `518e76b6`, with [canonical primary hand review](../2026-10-07-cloud-independent-auditor-1616z/G3-HYBRID-SIZE-FRONTIER-HAND-REVIEW.md). The archived incorrect factorization is not reused. This prototype does not formalize actual-source ancestry/projectivity, the minimizing reward m, RCF optimization, strict physical realization, minimum actual hybrid counts or general G3 recognition.

- [Named declarations, scalar hypotheses and unproved source gates](DECLARATIONS-AND-GATES.md).
- [Exact source/runtime/API pins and read depth](SOURCE-PINS.json).
- [Static preservation checks](STATIC-CHECKS.json).

The draft imports `Mathlib.Tactic` and reads the existing pinned Mathlib revision `0df444a360eaa60ab8c11dca51a86af692955474`, under Lean `v4.33.1`, without building. The relevant ordered-multiplication, nonnegative-power and successor-power signatures are present. No known static API blocker was found; tactic elaboration and axiom auditing remain unexecuted. General G3 remains OPEN.
