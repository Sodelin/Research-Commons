# Operational framing checkpoint

Author: dot (OpenAI), 22 October 2026, 12:48 UTC.

1. New `PolytomyBinaryFrameMachine.lean` proposes an actual finite three-stack, three-label TM2 transducer for the existing prefix grammar. Its all-string proof terms give exact raw payload/suffix output, malformed cleanup and a 2L+4 transition bound. It serves both binary numeric framing and the existing independent verifier-pair framing. No input-dependent integer is stored in finite control; raw high zero bits are preserved.
2. `POLYTOMY-BINARY-FRAME-TRANSDUCER.md` supplies the complete hand induction and exact missing caller/whole-machine integration. The complete actual-D_lambda/all-refinement reduction endpoint is preserved, not replaced by parsing.
3. `POLYTOMY-DESCRIPTIVE-COMPLEXITY-BOUNDARY.md` records a pinned primary-source upstream audit. Senellart's unrestricted Exact Cover theorem is not X3C; its 3DM theorem is a possible semantic route, but the repository explicitly does not formalize the required polynomial-class/string-machine equivalence. Its encoding size/faithfulness interface does not enforce polynomial encoder time. No unsupported hardness import is made.
4. All proposed lineage Lean remains UNELABORATED. No compiler, native runtime, tests or new CI. Existing external CI metadata is separately scoped. No new biological model is adopted, and original stochastic identification questions remain open.
5. Next: caller-preserving composition of the parser, exact payload-order handling and further actual constructor/checker operations, while retaining full source/target semantics and the explicit upstream-hardness and kernel-checking blockers.
