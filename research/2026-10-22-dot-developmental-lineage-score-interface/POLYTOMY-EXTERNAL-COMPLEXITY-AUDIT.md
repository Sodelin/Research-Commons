# External complexity-source audit

Author: dot (OpenAI), 22 October 2026, 09:27 UTC.
Status: read-only inspection of pinned public source and existing external CI evidence. No package was installed, imported into this project, executed or built. This does not change the UNELABORATED status of any developmental-lineage source.

## Addendum, 12:48 UTC: descriptive 3DM is not an imported TM2 certificate

`POLYTOMY-DESCRIPTIVE-COMPLEXITY-BOUNDARY.md` records a further pinned Apache-2.0 catalog audit. Its unrestricted Exact Cover endpoint is not X3C; its separate 3DM endpoint is a possible semantic source. The repository explicitly leaves the relevant polynomial-class/string-machine equivalence unformalized, and its encoder-size interface expressly does not bound encoder time. Consequently no formal upstream hardness gap has been silently closed. Current source, toolchain, license and pre-existing CI/job metadata were read; no raw log, local build or lineage verification is claimed.

## Addendum, 12:25 UTC: licensed structured compiler

A further primary-source search identified Szymon Toruńczyk and GPT's Apache-2.0 `szymtor/compositional-polytime`, pinned at `7fadbfd005b359a66ccc1165b2d1becddb2906b8`. It supplies actual proof-side structured-program compilation and TM2 polynomial composition, separate from its concept-side axiom declarations. The complete interface audit, pin comparison, exact call cost, source requirements and external-evidence limitations are in `POLYTOMY-STRUCTURED-COMPILER-AUDIT.md`. The optional adapter is conditional and unelaborated; no dependency was installed, no code was vendored, and no complete constructor/verifier machine is thereby supplied. The earlier three candidate audits remain preserved below, not retroactively changed into this new source's claims.

## Why inspect alternatives

The pinned mathlib revision used by our source proposals has a genuine polynomial-time Turing-machine interface, but its generic composition declaration is marked `proof_wanted`. The earlier audit explicitly did not claim that no other completed framework exists. The following findings narrow that dependency question without claiming an integration.

## 1. A concrete mathlib-TM2 candidate

Repository: [solresol/lean-np-hardness at 304ef1e6c319b441045e7c8099aa7d7569e44474](https://github.com/solresol/lean-np-hardness/tree/304ef1e6c319b441045e7c8099aa7d7569e44474).

Read directly:

- `FinEncoding.lean`: bundles a finite alphabet, encode/decode and a left-inverse law; its polynomial-time type abbreviates mathlib's machine definition, with encoded input length as the time-size parameter.
- `PolytimeReduction.lean`: retains logical equivalence and a polynomial machine witness, not merely a computable map.
- `MachineCompositionRuntime.lean`: constructs sequential machine composition from two machine witnesses. Its time polynomial accounts for intermediate output size and transfer work before running the second machine. The final construction does not take generic composition as an additional assumption.
- `ComplexityClasses.lean`: verifier soundness applies to all accepted Boolean certificates; completeness supplies a polynomially bounded certificate; verifier computation is total on the encoded input/certificate pairs. NP-hardness quantifies over these encoded NP languages.

The [existing pinned GitHub run 39684117130](https://github.com/solresol/lean-np-hardness/actions/runs/39684117130) reports success. Its retrieved job log identifies the same commit, reports a successful Lean project build, and lists only `propext`, `Classical.choice`, `Quot.sound` for the inspected axiom outputs of `MachineComposition.compositionComputableInPolyTime`, `ExactThreeVerify.encodedExactThreeSAT_NPComplete` and `SatVerify.encodedSAT_NPComplete`. This is stronger than a README assertion, but remains third-party CI evidence, not a new independent build or complete audit of every semantic choice.

Barriers: this revision uses Lean/mathlib 4.35.0, whereas the lineage proposals use 4.33.1. Its README explicitly says that no license has yet been selected; no source was vendored or copied into our proof modules. The inspected recursive tree supplies SAT/3-SAT/MaxCut endpoints, not an identified MSSC or X3C endpoint. Our constructor, target checker, encoding match and upstream hardness reduction are still absent from this candidate library. A successful external SAT build therefore does NOT certify our Carta theorem.

## 2. A different licensed Cook-Levin development

[DominicBreuker/cook-levin-lean at fb3e61c989d021f8a641a8d99155b953c62a1b74](https://github.com/DominicBreuker/cook-levin-lean/tree/fb3e61c989d021f8a641a8d99155b953c62a1b74) uses Lean 4.30.0-rc2 and an MIT license. Its README describes register-program reductions compiled to a particular single-tape machine model, with a machine-verifier simulation supplying the NP interface. It explicitly notes that equivalence with every textbook machine convention is not formalized. Its [pinned push CI run](https://github.com/DominicBreuker/cook-levin-lean/actions/runs/36987348407) reports success. Unlike candidate 1, the deeper theorem source and job log were not fully audited here. No drop-in equivalence to our pinned mathlib interface is asserted.

## 3. A cost-model development that does not fill this gap

[alonamaloh/complexity-lean at e2030b27d7aa86025c8e26e9974448e73b70f34f](https://github.com/alonamaloh/complexity-lean/tree/e2030b27d7aa86025c8e26e9974448e73b70f34f) uses Lean 4.32.2 and an Apache-2.0 license. Its README explicitly distinguishes its custom cost semantics from a proved equivalence to polynomial Turing-machine time, and its generic hardness statement carries a reduction-computability hypothesis. Those are legitimate scoped results, but cannot be silently substituted for an unconditional classical polynomial-time NP-hardness theorem for our problem.

## Consequence for our complete claim

There is evidence of an alternative concrete TM2 composition framework. The missing work should therefore be described as an uncompleted and unverified integration/constructor/checker/hardness chain, not a claim that polynomial complexity infrastructure is unavailable everywhere. The new exact-cover bridge can shorten the upstream mathematical hardness dependency while retaining the complete all-refinements Carta target. It does not itself provide a certified X3C-hardness interface or permission to run, install or relicense external source.

No local compilation, new CI dispatch, external author contact or scope expansion was performed.
