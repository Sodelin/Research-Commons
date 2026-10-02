# E8 source-loop bounds and supported-root traceback addendum

Attribution: dot (OpenAI), research assistance for Nolan.
Checkpoint: 2026-10-02 05:38 UTC.
Status: three exact-source Lean components PASS; 16 selected endpoint axiom audits, standard axioms only. This is not PRISM executable closure or an exhaustive source-call termination theorem.

Prerequisite public batch: [finite-grid traceback-to-observable bridge, bf1c5f46](https://github.com/Sodelin/Research-Commons/tree/bf1c5f46c46185aa2d44b47d5f767b4d1502dbca/research/2026-10-02-dot-e8-grid-traceback-0517z).

## New checked results

### E8TracebackCallRanks

The source-inspired measure is `8 × max(j-i,0) + phase(routine)`, over mathematical integer endpoints. Thirteen named same-interval wrapper calls decrease phase. The literal `Sample_V` inner-loop lower limit implies strict narrowing for its internal `Sample_V(k,l)` calls. `Sample_VM`'s left `WM` and right `WMV`/`WMP` subcalls also decrease this rank. Endpoint stripping cannot increase it.

This only covers the stated call-site arithmetic. It deliberately does not assert a complete call relation. Band/scaffold-border calls involving `B`, `Bp`, `b`, `bp`, `get_BE`, and their returned endpoints need actual helper/reachable-state invariants. Machine overflow and C++ index refinement are separate.

### E8SourceVBranchBound

The exact `min_l = max(k+TURN+1+MAXLOOP+2, k+j-i)-MAXLOOP-2` expression gives:

- `u1 = k-i-1 >= 0`
- `u2 = j-l-1 >= 0`
- `u1+u2 <= MAXLOOP`

Encoding a distinct internal candidate `(k,l)` by `(u1,u2)` is injective. At the pinned public `MAXLOOP=30`, there are at most 496 possible internal candidate pairs. Including one optional hairpin and one multiloop slot gives at most 498 slots. Guard filtering can only reduce the number.

Once the executed vector/list cardinality is refined to this checked loop-domain bound, the previous exact-real midpoint kernel theorem yields local TV at most `497/(2N)`. At `N=2^52`, this is `497/2^53`. It is a bound for this particular `Sample_V` branch list, not every `Sample_*` routine, and not a bound on floating-point/PRNG errors.

### E8SupportedTracebackLaw

The first batch's finite cancellation/assembly theorem explicitly required positive partitions at every state/depth. That premise is too strong to casually impose on an unrestricted RNA DP table containing dead subproblems.

The strengthening assumes nonnegative production and terminal weights and only a positive starting partition. A zero child partition forces every derivation weight under that child to be zero. Such a production contribution receives zero branch probability. Therefore normalized traceback cancellation, total mass one, and arbitrary fixed-observable aggregation hold at the supported starting state without global positivity.

The earlier finite-grid assembly remains published with its original stronger assumptions. This supported-root cancellation component does **not** silently change its theorem statement or establish the grid/continuation model for the actual engine. Further supported-state kernel assembly or an explicitly restricted carrier is still needed.

## Prior-work and integration contract

| Module | Closest checked principle | Concrete integration gain | Still needed |
|---|---|---|---|
| E8TracebackCallRanks | Standard well-founded ranking/loop-bound arithmetic applied to PRISM's actual call syntax | Checks V/VM narrowing and the named equal-span wrapper phase order | All border-helper containment, overflow/refinement and continuation fuel |
| E8SourceVBranchBound | Elementary injective finite counting, natural antidiagonal cardinality, and previously checked midpoint TV | Replaces a free local branch-bound parameter with a concrete 498-slot guard bound for Sample_V | Executed loop/vector length agreement and all other routines' bounds |
| E8SupportedTracebackLaw | Established nonnegative partition-weight traceback cancellation, including zero support | Removes positivity of every child/state from the starting-state theorem | Actual carrier/weights/classifier/RNG/numerical and supported-kernel bridges |

None of these is claimed as a new general mathematical sampling or grammar theorem. No generic runtime is rebuilt and no efficient arbitrary-semiring/class-language claim is made.

## Primary source pins

- [PRISM part_func.cc at 87a88715](https://github.com/TheCOBRALab/PRISM/blob/87a88715282d279fc361eb56de27153a321359be/src/part_func.cc): `compute_internal_restricted`, `Sample_V`, `Sample_VM`, the listed wrapper calls, and band call sites.
- [PRISM constants.hh at the same pin](https://github.com/TheCOBRALab/PRISM/blob/87a88715282d279fc361eb56de27153a321359be/src/ViennaRNA/constants.hh): `MAXLOOP=30`; verified Git blob `96ccc63d99a5d9db2477dc499342ea5b3f7e010e`.
- [PRISM, WABI 2026 article 30](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.WABI.2026.30), §2.1: existing ideal stochastic traceback cancellation.
- [CParty](https://pmc.ncbi.nlm.nih.gov/articles/PMC11709253/): existing unambiguous density-2 weighted source decomposition. This addendum does not replace its source-specific grammar with an asserted abstract bijection.
- [PKProbDesign SCFG2 runtime integration, pinned 27afdd05](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/SCFG2_API_INTEGRATION.md): existing CParty-backed exact API architecture, process-isolated session handling, fixed captured parameters, and explicit unreachable outputs. This is relevant existing engine architecture to inspect before bespoke implementation. The name “exact” is not treated as a formal real-arithmetic/numerical certificate here.

## Important depth distinction

The `d` in the previous conditional-kernel trace error bound counts total sequential stochastic production steps in a continuation-state path. A bound on maximum recursive call-stack height is not that bound. A full integration must either prove total continuation fuel directly or combine a genuine call-rank decrease with bounded arity to derive a conservative total-node bound. The partial call-rank facts in this addendum do neither globally yet.

## Exact compiler receipts

`SOURCE-AND-COMPILE-MANIFEST.json` contains the exact successful receipts. Sources and logs are copied from successful immutable attempts. Compiler: Lean 4.33.1 commit `819816b2e0a3bf405af45ae5c7af2491d8f5bee6`; mathlib `0df444a360eaa60ab8c11dca51a86af692955474`.

- E8TracebackCallRanks: 1.915 s, source `ccc76e7da6b8a176aa8d11af25afb541ba6efb2ddd188d3eb331fa4dede8b67a`
- E8SourceVBranchBound: 2.940 s, source `2be46488a85e40a7174510f9598178d525ed4712c43e0c23523d47bae0c7fdb8`
- E8SupportedTracebackLaw: 1.655 s, source `d139964d628b77b6d3920f613251a64b8d36a6d7ba62edd6ae6b12122ac63446`

Compile prerequisites from the first pinned batch before these sources, with their objects and pinned mathlib dependencies in `LEAN_PATH`. No costly certificate replay or broad Mathlib import is needed. No private product/source-adapter code is included.
