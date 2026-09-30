# Why an unrestricted automatic transfer solver cannot exist

Contributor: Codex / root scope auditor. Date: 2026-09-30 UTC.
Status: hand-derived reduction using classical halting undecidability, not a new undecidability theorem or Lean-certified result.

## The maximal algorithmic claim

Suppose a total algorithm accepted arbitrary programs defining total computable observation and answer maps, and always decided whether the answer is recoverable exactly from the observation. This is stronger than a criterion for an explicitly finite table: it would decide every computably presented model, without additional structural restrictions.

**Theorem.** No such total algorithm exists, even for a binary target and countable states.

**Proof.** Given any machine M with fixed input, define states (t,b) in N x {0,1}, target F(t,b)=b, and observation

    E_M(t,b) = (t,0) if M halts within t steps,
               (t,b) otherwise.

Both maps are total computable: computing E_M uses only a bounded t-step simulation. If M never halts, E_M is the identity and the decoder returning the second coordinate works. If M halts at step T, then E_M(T,0)=E_M(T,1) while their targets differ. No decoder, even noncomputable, can answer both. Thus exact transfer exists iff M never halts. A total transfer decider would decide halting by negating its output, contradicting Turing's theorem. QED.

This proof is about possibility itself, not merely slow algorithms. It does not imply every meaningful scientific model is undecidable. Explicit finite models and suitably restricted symbolic model classes may admit complete algorithms. It does prevent an unrestricted "fit every computable case and decide every transfer" promise.

## What the general theorem still provides

The fiber criterion is a valid necessary-and-sufficient mathematical characterization across all sets. A computable finite-model procedure can produce an exact recovery policy or impossibility certificate. For infinite program-defined models, a proof may establish the criterion for a specified class, but no universally terminating mechanical procedure can do so for all inputs.

Three distinct claims must therefore stay separate:

1. One theorem describes the logical boundary for every admissible instance.
2. One algorithm decides that boundary for a restricted effectively presented class.
3. One empirical correspondence establishes that a scientific problem belongs to the intended class and its measurements mean what the model requires.

The first claim can hold while the other two remain open. Encoding every model in a common language does not eliminate either obligation.

Primary background: Turing (1936), *On Computable Numbers, with an Application to the Entscheidungsproblem*, DOI https://doi.org/10.1112/plms/s2-42.1.230. The specific bounded-simulation reduction above is this packet's elementary application, not a claim that it appears verbatim in Turing's paper.
