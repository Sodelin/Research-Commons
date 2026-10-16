# Lean 4.33.1 checker/export and independent challenge assessment

15 October 2026 (Pacific); source inspection began 16 October 2026, 00:24 UTC. **Documentation/source assessment only.** No compiler, checker, exporter, installer or package bootstrap was run. This is a separate follow-on note, not an additional gate on the active desktop build.

## Scoped disposition

The frozen nine-module [source selection](https://github.com/Sodelin/Research-Commons/tree/55eecf2a337a43c0a9b958592dde1e50a6bf405d/research/2026-10-15-astra-semi-foundations-2124z) and Lean 4.33.1 remain unchanged. All 18 local files still match that selection's manifest. This assessment produces no new elaboration, theorem, axiom-audit or source/object acceptance result.

**Concrete finding:** the exact pinned Lean source already contains `leanchecker`, but it replays declarations through Lean's own kernel. A standalone independent implementation/export chain compatible with this package has **not been authenticated by this bounded source assessment**. Existing candidates and the precise missing evidence are below; this is not a claim that no compatible build exists anywhere.

## Actual implementations and version boundaries

| Existing implementation/source pin | Input and what it checks | 4.33.1 disposition |
| --- | --- | --- |
| Bundled `leanchecker`, Lean `819816b2e0a3bf405af45ae5c7af2491d8f5bee6` | `.olean` environment replay through the reference kernel; `--fresh` replays the selected module and imports into an empty environment. | Exact 4.33.1 source path exists. This assessment does not authenticate a desktop executable or run it. It is same-kernel replay, not an independently implemented kernel. |
| `digama0/lean4lean`, inspected master `67f63b0c818920dfaed2ad07ccff187a6a8fe1e3` and `8223d223ed98661882e95d9d6a7126df7097cd76` | Lean implementation of a kernel with `.olean` replay CLI. Its README explicitly describes derivation from the C++ implementation and possible shared bugs. Building its executable is distinct from checking its separate metatheory/verification targets. | Both inspected toolchain files specify **4.33.0-rc2**, not 4.33.1. An index's statement that a commit builds under another version is not an authenticated same-version binary or closure. No retargeting is performed or selected. |
| `leanprover/lean4export`, `15f6055e299ad5b89345e533cc2192f4cc00f659` | Exports declarations and recursively used constants to NDJSON 3.1.0. A declaration list after `--` can select the intended cones; metadata records Lean version/githash and exporter/format versions. | Its toolchain file specifies **4.33.0**. Neither format agreement nor patch-version proximity proves `.olean` loading, source/API compatibility or binary identity under 4.33.1. No compatible exporter binary has been established here. |
| `ammkrn/nanoda_lib`, `f67473ba5f9397266f89c7852082c9c914b5d219`, Cargo version 0.4.24 | Rust external checker reading textual exports, with an axiom policy and optional declaration pretty-printing. Its parser's format-version interval is **3.1.0 inclusive to 3.2.0 exclusive**. | A concrete format-compatible candidate for a future authenticated 3.1 export. That parser interval is not a Lean-version or kernel-semantics compatibility certificate. No installed binary, locked executable build, complete run or package acceptance is established. |
| `leanprover/comparator`, `865edc14486c3388e9225daa971da8e157488c3e` | Separately trusted challenge/solution statement matching, dependency/axiom checks and kernel replay, with optional external kernels. | Its current toolchain is **4.35.0**. It is a source/design reference, not an admitted 4.33.1 executable or a reason to change the active package. |

Primary inspected sources: [4.33.1 checker](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/LeanChecker.lean), [replay](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Replay.lean), [Lean4Lean toolchain](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/lean-toolchain), [Lean4Lean scope](https://github.com/digama0/lean4lean/blob/67f63b0c818920dfaed2ad07ccff187a6a8fe1e3/README.md), [exporter version](https://github.com/leanprover/lean4export/blob/15f6055e299ad5b89345e533cc2192f4cc00f659/lean-toolchain), [export implementation](https://github.com/leanprover/lean4export/blob/15f6055e299ad5b89345e533cc2192f4cc00f659/Export.lean), [nanoda parser](https://github.com/ammkrn/nanoda_lib/blob/f67473ba5f9397266f89c7852082c9c914b5d219/src/parser.rs), [comparator toolchain](https://github.com/leanprover/comparator/blob/865edc14486c3388e9225daa971da8e157488c3e/lean-toolchain).

The exporter branch named `hbv/backport` was also inspected at `04757fe5e7afd386b3d7eb16b19a1333d6849a51`: it specifies 4.15.0. Its name alone supplies no 4.33.1 compatibility. The bounded branch/version reads are recorded in `PRIMARY-SOURCE-READS-01.json`; no exhaustive checker census is claimed.

## Why 4.35 documentation cannot select the active toolchain

The official [4.35 release notes](https://lean-lang.org/doc/reference/latest/releases/v4.35.0/) describe project-level `lake check`/`lake comparator`, bundled external checkers and direct export inputs. These are later facilities. The same notes describe stricter NDJSON reader handling. Their existence is useful documentation evidence, not proof that those commands, binaries or reader behavior exist in the selected 4.33.1 environment. No upgrade, installation, environment move or cross-version object reuse is proposed.

The pinned [4.33.1 object reader](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/library/module.cpp#L489) checks structural header fields and, when `LEAN_CHECK_OLEAN_VERSION` is enabled, the build githash. This assessment does not establish the compilation setting of any other binary. Object compatibility must not be inferred merely from the textual export version.

The [4.33.1 release account](https://lean-lang.org/doc/reference/latest/releases/v4.33.1/) records actual kernel/runtime corrections and examples where independent checkers agreed on an erroneous input. Agreement is additional evidence, not a theorem that a checker, its runtime or its implementation lineage is infallible. This observation does not introduce a new gate or alter the selected package.

## Challenge and axiom manifest supplied now

`CHALLENGE-STATEMENTS-01.json` selects the **15 declaration names already requested by the frozen audit's `#check` commands**, records each exact proof-free source header and its ambient assumptions, and adds a concise human-readable contract. The original audit has **14 `#print axioms` requests**: it does not separately print the `orbitDistance_eq_zero` row. This difference is recorded; neither the frozen audit nor the active job is modified. A later separately admitted follow-on can collect that extra row if selected.

The manifest was prepared without consuming a generated proof export, acceptance flag or current build result. Its finite/nonempty premises, observation-range boundary, declared symmetry group, N^-2 normalization and ALL-source-orbits action convention are explicit. It has no definition holes, placeholder proofs, new axiom declarations or claimed runtime result.

This is **a proposed review contract, not a ready comparator challenge module**. The existing modules mix definitions and proofs. Before a future comparator-style run, an independently trusted challenge environment must bind the exact definitions occurring in each type. Merely importing a solution's definitions into a nominal challenge, comparing theorem names or comparing printed strings would not discharge that obligation. No refactor of the frozen modules is authorized or performed here.

`AXIOM-POLICY-01.json` specifies a proposed ceiling of `propext`, `Classical.choice` and `Quot.sound`, with their types, universe parameters and pinned primitive-source locations. A ceiling permits a smaller actual set; it does not predict that every theorem uses all three. Standard names must resolve to the expected types and primitive interpretations. Reachable `sorryAx`, compiler-trust axioms, unsafe proof dependencies or any other unreviewed axiom are outside that ceiling.

Lean 4.33.1 also contains ambient metaprogramming/compiler declarations that may be absent from a theorem's dependency cone. A full environment export and a selected theorem-cone export can therefore have different axiom inventories. Do not silently broaden the ceiling to make a full export pass. The export selector, complete dependency cone, missing-declaration behavior and checker configuration require review together. Actual axiom lists and kernel-type digests remain null in these proposed manifests.

## Trust and scientific limits

There are separate obligations for: the intended mathematical statement; the definitions/imports used by that statement; source-to-object/export identity; a complete accepted checker run; and the experiment/source-model interpretation. A later kernel agreement can support well-typedness under explicit axioms. It cannot prove that an observation model describes a material, that observational equivalence is causal equivalence, or that an exact-law oracle counts physical samples.

No Poisson/Gibbs measurement model, optimal-copy bound, G3 attained-membership/source-size theorem, G4 uniform all-rivals margin, physical receiver, Rust refinement or canonical adoption is obtained here. Existing accepted CM and G components retain their actual scopes and attribution.

**Next bounded action for this follow-on:** independent review of the statement/axiom contract and selection of an actually held compatible checker/export artifact, if later requested. No checker/export runtime is selected now; no additional owner query, acquisition, retargeting, kernel project or resource prerequisite is added to the current build. The active authentication/driver review remains with its existing operator and reviewer.
