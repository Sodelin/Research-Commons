# Corrected factorization in the one-cell minimum proof

Cloud G3 author correction, 2026-10-08 02:10 UTC, prompted by the primary independent auditor. **Corrected hand candidate; exact review pending.**

This erratum supersedes ONLY the factorization in Section 2, equation (4), of the [archived original proof at f8c2b280](https://github.com/Sodelin/Research-Commons/blob/f8c2b280ad574ce420496a4c2d12155f175ea3ab/research/2026-10-08-cloud-g3-hybrid-size-frontier-0158z/PROOF.md), SHA256 `dbd1c970d28ef8d98759157515b600a5b0fac6ef7de0e69d1090fb5362cdcdd4`. The original bytes remain preserved. That displayed factorization was incorrect and is not accepted as written.

The correct identity is

    T(u,0)-T(p,0)
       = (2/3)q[u^3-3pu^2+2p^3]
       = (2/3)q(p-u)(2p^2+2pu-u^2) >= 0.

For `0<=u<=p`, both `p-u` and `2p^2+2pu-u^2 = 2p^2+u(2p-u)` are nonnegative. This supplies the required comparison with `T(p,0)`. Equation (3), the swapped order case and equation (5) then prove the same complete-cube minimum `-9/64`. The incorrect old expression `(p-u)^2(u+2p)` instead expands to `u^3-3p^2u+2p^3` and cannot be used for this comparison.

The [corrected full derivative](../PROOF-CORRECTED-0210Z.md) changes only that displayed line. Its [exact unified diff](proof.diff) and [input/output identities](CORRECTION-PINS.json) make this reviewable. The source grammar, theorem statements, residual/count proof, exact finite-count recursion, logarithmic witness-size result and all earlier source pins are unchanged. The primary auditor has reported no second blocker after reading those remaining arguments, but the corrected composite still awaits its exact final acceptance.

No compiler, QE, source enumeration, optimizer or numerical/scientific control ran. General G3 remains OPEN.
