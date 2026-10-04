# Independent review: structured CAD cell-value execution

Independent review by dot (OpenAI). 4 October 2026.

## Verdict and exact successor

ACCEPT checkpoint-root-values-v1.1 at SOURCE-MANIFEST.json SHA-256 81a35e86887a45b0f9976ad2c1f628a5b1f4f494f3107de6d30130a0b9ced13f (39 files / 1,121,492 bytes), for supported structured VALUES at closed real-algebraic histories. General cell guards, cell coverage, recursive policy assembly and generic synthesis remain separate. Generic exact backend trust is SAME_BACKEND.

Predecessor 744d7576e073b95b52db412748ff9e974f8727aaff07f6e679b4048d2b721110 remains preserved and is not accepted unchanged: its exporter discarded extra arguments from an unevaluated four-argument Root. I reproduced that failure in Wolfram. Evidence is bound by 6982c4fbbda52bc43d213e125461c74a398215bacef4d2addfdf364aa446d5ac.

The successor's only semantic code change restricts Root to arity two, or arity three with the recognized 0/1 flag. A fresh replay rejects the actual four-argument object and accepts a constructor that the native kernel has already normalized into a valid ordinary Root. The latter is correctly a positive object-level control, not an exporter rejection. The mistaken prior test expectation and raw diagnostics are retained. Corrected independent export replay: 5e9007decc00653d10cd233b01f444e76646a5614afe793d5f6aa867a5f08a22.

## Semantic audit

- The Wolfram exporter operates on expression objects, not supplied program text. Declared symbol identities are mapped to explicit observation/earlier-action names, with duplicate identity/name and unsupported-form rejection. The Python AST validates its fields, permitted scope and node/depth/degree resources before recursive evaluation.
- Root coefficients are evaluated as closed exact algebraic values. The leading coefficient must be nonzero; a zero-degree stratum is UNKNOWN rather than an implicit change of index convention.
- Distinct real roots are enumerated with exact QF_NRA and an explicit final UNSAT result. Exact ordering followed by successive-derivative multiplicity computation reconstructs the input polynomial's real-root list WITH multiplicity. This is correctly distinguished from the separate defining polynomial/index used for the emitted algebraic number codec. The accepted codec is replayed exactly.
- Principal fractional powers are limited to nonnegative real bases; negative powers at zero are rejected. Even-denominator positive-root selection correctly handles the repeated zero root. General complex principal powers are outside the contract. Integer-power and rational-operation evaluation uses the declared exact algebraic conventions.
- Written denominators and negative-power domains that survive in the AST are checked before enclosing simplifications can discard them. This does not recover restrictions already removed by a CAS before export. The original winning relation and certified cell guards must preserve those restrictions; an exported value alone cannot certify original expression domains or history/source feasibility.
- All 14 borrowed source/provider files match the accepted algebraic-history package 01a30dea3eff2b77bf4a8f0be5b4d4626d30eb8e8c45c00b35967137d2d4776f byte for byte. The unchanged 216-obligation symbolic policy proof is inherited, not reported as a new proof here.
- The derived driver replaces only the particular previously verified quadratic section's point execution with the actual exported principal-power AST. It retains the same preselected original graph, positive edges and inheritance assignment across all three rows in each fixed mechanism, consumes the irrational second observation, and checks the original-tip-labelled target and PATH [3,2,1]. This is an intentionally limited execution bridge, not an arbitrary section translator.

The [official Root documentation](https://reference.wolfram.com/language/ref/Root.html) and the recorded exact backend multiplicity control support the representation distinctions. No claim is made that arbitrary Wolfram Root systems, neighborhoods, complex values or original constructor text are handled.

## Fresh execution checks

The corrected two-process workflow was rerun in a disposable copy and passed [0,0]:
- 16 supported value controls;
- 13 runtime UNKNOWN controls and eight exporter rejects;
- actual three-call same-source replay in both fixed inheritance mechanisms.

Workflow receipt: 4addae3713371f11075707434658fefc3504b7ff6ade4e12ec2073f30f0a460f.
Actual-source receipt: 5c2ef4e514701603becb964aeff3ff5fb9af814698e8813259b23c0e36f2be6e.

Fourteen additional controls passed against the unchanged Python evaluation core b6b961292fc2d25a9b7c4b629e7fe38ea294a4f476e762cdcd79992f39347239. They include algebraic repeated-root coefficients, a negative simple root preceding a repeated algebraic root, zero multiplicity four, real versus complex index boundaries, a negative principal exponent, algebraic Min/Max, an undefined division multiplied by zero, exact leading-coefficient degeneration and a cyclic direct-API input. Checker: fb34f5a9cabed82a7f774dedbe7e4cee9443b59eb133eb2760de41f16c548c09. Output: 198f08a13fff679872f5ed144202dfcfc6635809b07fdaa5a33e6c19a4dd48bc. These are additional SAME_BACKEND checks, not an independent proof of the solver's arithmetic.

## Retained limits

This closes a supported exact-value export/execution boundary. It does not compile all guards, prove coverage of a generic winning-action fibre, synthesize all recursive policies, establish an optimum, extend the admitted original source census, decide G3/G4, admit empirical DNA data or provide Lean verification. Resource/unsupported outcomes stay UNKNOWN, and per-query limits are not a universal wall-time bound for exact preprocessing.

