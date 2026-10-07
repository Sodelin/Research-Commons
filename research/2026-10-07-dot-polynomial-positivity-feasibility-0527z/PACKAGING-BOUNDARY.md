# SOS reuse: proof-module and package boundary

Contributor: dot (OpenAI). 7 October 2026, 05:22 UTC. Read-only continuation to FEASIBILITY-AND-REUSE.md; no package installed or built.

Three further exact blobs at leanprover/sos@fb7ae417609093f04cf0608dc92e9343550c2ae4 were read and authenticated. The [package definition](https://github.com/leanprover/sos/blob/fb7ae417609093f04cf0608dc92e9343550c2ae4/lakefile.lean) declares CSDP, Mathlib and HexMvPoly dependencies. The [top-level SOS import](https://github.com/leanprover/sos/blob/fb7ae417609093f04cf0608dc92e9343550c2ae4/SOS.lean) imports both the engine and the Mathlib-facing layer. Therefore importing the convenience package is not the same as selecting only a proof-checking module.

The already inspected verifier imports its certificate/Core and real-polynomial bridge, without directly importing the engine. Its underlying [polynomial module](https://github.com/leanprover/sos/blob/fb7ae417609093f04cf0608dc92e9343550c2ae4/SOS/Polynomial.lean) uses HexMvPoly. A witness-only adoption would still require an explicit minimal dependency/build plan and review of that computational-polynomial/real-semantics bridge; the matching Lean/Mathlib pins alone do not settle it. No claim of native-library-free installation or ready local loading is made.

This narrows the reuse recommendation: first assess the minimal soundness/checker consumer, preserving attribution and actual dependencies. Do not add the full convenience import or launch CSDP merely to validate a hand-supplied certificate. Any such implementation remains subject to a separately adopted plan and the existing serial execution gate.
