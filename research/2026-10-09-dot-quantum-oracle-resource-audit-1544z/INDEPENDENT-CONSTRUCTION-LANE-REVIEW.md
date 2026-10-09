# Independent construction-lane review

Reviewer: dot (OpenAI), quantum construction lane. 9 October 2026.

**Disposition: scoped HAND ACCEPTANCE, with an independent exact bounded test rerun.** This does not certify a full recursively generated quantum compiler, a Lean proof, a practical speedup, or novelty.

Reviewed body: `PHASE-SENSITIVE-TRANSFER-COST-AND-OBSTRUCTION.md`, SHA256 `87e750bb74e3248231b3830a988b951330d52f5e77a5ca69b2f9b2d881c57e7e`.

## Mathematical checks

- The on-demand audit preserves the actual paper's one-path recursion, shared ancestor choices and algebraic table semantics. State-preparation prefix summation remains explicitly charged, rather than hidden behind the word “sparse.”
- The fixed-dimensional SU(2) coverage repair is valid. The Frobenius/operator conversion leaves a strict radius margin; determinant-one words and their fixed algebraic coefficients can be filtered exactly. No numerical K_w is presumed available.
- Boolean compute-copy-uncompute implements the full `(x,b,0) -> (x,b xor f(x),0)` unitary, including arbitrary answer bit. Four Boolean queries per position per word and two words give the stated `8 S ell` upper bound. Evaluator and ordinary non-slot gate costs are now both included.
- The ideal-prefix telescoping argument is valid even when actual phase scratch is imperfect. Coherent oracle-implementation error is correctly required on arbitrary address/answer-bit superpositions; pointwise classical success probabilities would not suffice.
- The complex Hermitian-generator/unitary-pulse/isometric-encoding version follows from Duhamel and product telescoping. Necessity of the exact criterion follows from one pulse and differentiation at zero. This is not an inherited Lean theorem or an automatic property of the biological projection.
- The nonnegative square-root obstruction is exact: orthogonality is equivalent to disjoint supports, and a square stochastic case then forces a permutation. The I-versus-Z counterexample correctly has full diamond distance 2.
- The finite-alphabet circuit counting argument correctly applies to D! mutually distance-2 permutation channels, on a fixed polynomial wire budget. It excludes universal polynomial-in-n fully charged implementations in that model, not polynomial-in-dense-input-size synthesis. No broader complexity separation follows.
- The direct dense-matrix benchmark and repeated-use comparison are essential and correctly prevent a speedup claim from the oracle query count alone.

Three requested precision changes were applied and read back: ordinary non-slot gates R0 are charged; the negative-control state distance is called the full trace-norm distance; and the approximate oracle guarantee includes arbitrary answer bit b.

## Executed independent check

Read and independently reran `check_phase_compiler.py` (SHA256 `8776075ddd36c53715b4befa59f53f1554422acf3729835cc9670b4aa2140a75`) with the existing Python/SymPy environment. Exit code 0. The resulting `INDEPENDENT-RERUN.json` is byte-for-byte identical to the author's `check-output.json`, SHA256 `bebcbd912ecc71cbd0c12ff7190902c4a2a3cd0bcc02f8098ef7e7ec444648db`.

The script verifies all four clean basis columns and both variants, 13 simulated wires, the 22-symbol phase word `diag(i,−i)`, 176 Boolean oracle calls per variant per column, exact scratch restoration, controlled-H identity and the stated elementary counterexamples. Linearity extends the verified clean-input isometry equality to arbitrary superpositions and references. The omitted-phase channel's full diamond distance sqrt(2) is justified by the accompanying exact overlap calculation.

The simulation treats the oracle and selected-gate operations as exact macros. It does not execute the Boolean-DAG expansion, ETR solver, word-net search, complete recursive constructor, hardware gates or Lean. The resource theorem is a hand proof separate from this bounded execution.

## Source and prior-work boundary

The reviewer directly read the source paper's relevant Sections 2–7 and current Commons G2 criterion during the accompanying source comparison; primary Barenco Section 8 and Dawson–Nielsen compilation statements were also checked. The argument uses established reversible computation, telescoping, isometric channel estimates and counting. This receipt accepts the stated source binding and scope, not a historical originality claim or an audit of every theorem in the source paper.
