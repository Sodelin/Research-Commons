# E8 concrete SCFG2 runtime child-normalization adapter

Attribution: dot (OpenAI), research assistance for Nolan.
Checkpoint: 2026-10-02 06:01 UTC.
Master obligation advanced: actual production/runtime child-carrier correspondence for E8 source gates 3/4.

## Result

`E8SCFG2RuntimeChildAdapter.lean` passed Lean 4.33.1 in 1.945 s with a 3072 MB compiler cap. Exact source SHA256: `61151fc34a1ca4c9cc09711e59d3ca60b78690005e2f8687867ca4d5915648c3`. Eight selected theorem axiom audits use only standard axioms; two are axiom-free. The full receipt, compiler log, source provenance and scope receipt are included.

For every valid active child on the selected SCFG2 deduction factory/executor path, the formal transcription proves:

- the forward runtime child lookup and the traceback-normalized child refer to the identical key
- the resulting chart lookup values agree
- the entire ordered active-child lookup stream agrees, before multiplication
- any ordered fold over that stream agrees without an associativity assumption
- the exact mathematical contribution product agrees
- parent, rule, split and child count remain unchanged

This is a **specific public-source normalization check**, not a new stochastic-kernel framework. It does not prove C++ extraction/refinement, IEEE arithmetic correctness, physical energy fidelity, complete/unambiguous RNA support, classifier agreement or sampler independence.

## Why the raw deduction record was insufficient

The public scaffolded runtime does not use the generic `engine/execute.hh` carrier unchanged. Its actual schedule executor calls `runtime_child_total_for_deduction`.

For the `WMBP_DIRECT_VP` rule, that forward lookup redirects a `VP_DIRECT` child to `VP` and explicitly sets secondary endpoints `ip` and `jp` to `-1`. The matching traceback transformation changes the nonterminal to `VP` but retains the child's endpoint fields.

The two transformations therefore agree only after applying the real key-validity invariant: every non-`BE` key has `ip=jp=-1`. A `VP_DIRECT` key is a primary, non-`BE` key. Thus the seeming reset-versus-retain difference disappears on valid executed children. The proof retains that premise explicitly; it does not declare the transformations equal for arbitrary invalid keys.

This establishes the correct normalized child-carrier interface for a future supported-state PMF binding. Binding PMFs directly to the unnormalized exported `Deduction.children` would model the wrong lookup for this rule.

## Selected executed-path validity audit

A separate complete public-source inspection verified:

1. The exact deduction generator's three child-bearing `Deduction` vector push sites are guarded by `is_valid`.
2. Its fallback basic generator also filters `is_valid`.
3. The per-item factory appends or returns those generated vectors.
4. The one direct `W(i,i)` base return has zero active children, so the active-child premise is vacuous there.
5. The selected scaffolded schedule executor consumes that factory output without mutating its children before lookup.

This is a source/hand audit supporting application of the Lean theorem to the pinned factory path. It is not a verified C++ compiler/memory model or proof about arbitrary externally constructed deductions. See the independently published [targeted prior/source report](https://github.com/Sodelin/Research-Commons/blob/7bb162985e1f7ea74bad92c4b2ed617ab5132301/research/2026-10-02-dot-e8-targeted-prior-0601z/TARGETED-E8-NEIGHBORHOOD-AND-REUSE.md).

## Exact source pins and transcription audit

All source facts use PKProbDesign commit `27afdd054272dbda8a74c8aad156970a44c23cd8`, containing the public vendored CParty SCFG2 runtime.

- [Actual scaffolded executor and normalization](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/replay/w_final_exact_inside.hh), Git blob `f4b6ab09e1d16f20f7d9851b6bb3c83fdaf9ec05`
- [Item key validity](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/deductions/item_key.hh), blob `d3e01e287baba10007daae11b873c203b4c59277`
- [Deduction active-child validity](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/deductions/deduction.hh), blob `b32bd883258b53bf1ce88129e7ac4fc82ddd4bf7`
- [Exact generator](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/deductions/generate_exact_basic.hh), blob `b138807cdd7bdc63f8cc75a9effb9e1f2bb482e6`
- [Fallback basic generator](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/deductions/generate_basic.hh), blob `ba427a53c1c6c1309e615b3de57d0902b13342f6`

`SOURCE-PROVENANCE.json` records all inspected file pins. The formalization's 17 nonterminal names and 57 rule names were mechanically compared against the exact pinned header enum lists, preserving order and spelling. Field/key-validity and normalization semantics are explicit manual formal transcriptions. They must not be described as extracted executable C++.

## Prior result and non-duplication contract

The existing CParty/SCFG2 architecture already supplies the deduction, chart, local-weight, schedule and normalization operations being checked. Existing mathlib `PMF.bindOnSupport`, support/zero-support/associativity and `PMF.ofFintype`/`map_ofFintype` supply general probabilistic assembly. This module does not rebuild or reprove those libraries.

Its narrow addition is the concrete normalization correspondence needed before those existing PMF contracts can model this runtime's actual child lookups. The proof uses ordinary equality, key validity and finite traversal. No historical novelty claim is made.

The earlier [finite-model sampler bridge](https://github.com/Sodelin/Research-Commons/tree/bf1c5f46c46185aa2d44b47d5f767b4d1502dbca/research/2026-10-02-dot-e8-grid-traceback-0517z) and [source/support addendum](https://github.com/Sodelin/Research-Commons/tree/51561e98b15e6469de41c2b7d2925374faf96f96/research/2026-10-02-dot-e8-source-support-0538z) remain unchanged. The new adapter is a source interface obligation, not a silent upgrade of their assumptions.

## Remaining source gates

- Full generated-deduction/schedule dependency order and total continuation-step fuel
- Supported-state probability binding using these normalized runtime children
- Pure local factor semantics and consistency across dynamic support/storage observations
- Exact represented/physical Boltzmann weight comparison, including documented provisional support and scaling boundaries
- Actual derivation multiplicity, emitted pairs, scaffold support and agreement with the specified PRISM ensemble
- Current L5/L6 classifier correspondence and selected-class SUM rather than maximum-target evaluation
- Conditional random input law and an applicable existing verified/exact/approximate-bit sampler
- Floating arithmetic and confidence-numerical certification

The documented residual scaling differences and the potential ensemble differences are not repaired by fitted factors in this proof. No private product code is included.

## Replay

Compiler: Lean 4.33.1 commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

Compile the source with the pinned dependencies using `lean -j1 -M3072`. It has no imports of the earlier project modules. The receipt identifies the precise successful source/log/object hashes and standard-axiom reports. Earlier local attempted sources survive in immutable history and are not substituted for this published successful snapshot.
