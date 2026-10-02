# SCFG2 VPR right-padding mismatch: source theory and isolated replay

Author: dot (AI-assisted research), 2026-10-02. Scope: public SCFG2 source compatibility within E8. No author outreach, private product publication, or upstream code update.

## Result

The public SCFG2 `VPR_SPLIT_VP_BASEPAIR` transition uses unpaired-factor index **k-i**, while its sole child is `VP(i,k)` and its declared empty region is **[k+1,j]**. The original CParty supplement, page 5, equation (vi), specifies the right-gap factor **B(c′(j-r))**. The neighboring VPL equation (vii) uses the left-gap r-i. Thus this is a source-to-published-recurrence mismatch, not merely an inferred numerical preference.

An isolated one-line k-i to j-k intervention in a separate copy removes the observed partition-scale dependence on two public fixtures. It leaves the pinned baseline unchanged. This is strong bounded causal evidence and agreement with the published VPR term. **It is not a complete engine fix or proof of the full physical ensemble, grammar multiplicity, current PRISM classifiers, C++ floating refinement, or sampler fidelity.**

## Primary theory and source identity

- [CParty publisher landing page](https://academic.oup.com/bioinformatics/article/41/1/btae748/7928840), Supplementary Data, page 5 §1.4.1, Eq.(vi). The PDF was retrieved from the exact public publisher hyperlink and its rendered page was inspected. PDF SHA256: `cd60782ca8582a1eee9f853bd4a5d3fcae9dae9b9c17229cfaef0b36fd7a3f7c`.
- Public source pin: [PKProbDesign 27afdd054272dbda8a74c8aad156970a44c23cd8](https://github.com/TakumiOtagaki/PKProbDesign/tree/27afdd054272dbda8a74c8aad156970a44c23cd8).
- [VPR transition](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/weights/vpr_transition.hh) calls the unpaired-factor context with `deduction.split.k - deduction.parent.i`. Its context indexes `expcp_pen`, whose table includes both the physical unpaired penalty and reciprocal partition scaling.
- [Rule expansion](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/deductions/expand_basic.hh) emits just `VP(i,k)` for this alternative. The [target matcher](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/engine/traceback_pairs.hh) marks [k+1,j] clear. Both agree with the right-gap interpretation.
- The source project carries a [GNU GPLv3 license](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/LICENSE). The small experimental patch accompanies this attributed diagnostic under the applicable upstream source licensing terms. No production patch or upstream submission is claimed.

## Rebuild and intervention controls

The existing public adapter was rebuilt without source changes using gcc/g++ -O2 (no fast-math), C++17, the vendored C source list/static RNA-library boundary from CMake, and at most two compile workers. CMake itself was unavailable; the first all-object link failed on unused RNA symbols, and the static-library link matching the published target boundary succeeded. This build-route recovery is recorded rather than attributed to a source defect.

Baseline executable SHA256: `2536e8cad1e7b66da67201b1d3f1c06178290d892bbe930f23fcc6238794f477`.

Only the VPR transition header was changed in the copied intervention source. The hypothesis adapter SHA256 is `b16902bf83608493716ab921663cd45116a5e16814c4fa46be7718b47b39b43c`.

Header SHA256 before: `088e7eea50eac951ebb419f14ccf1f4a2920b987a81ee7ea67ae76fcf0615489`.

Header SHA256 after: `914d5df804a55b4abf5d0cf8c96d249aaec1e5aafa433de7b45c36b1c1b8b74e`.

An independent checker confirmed the original header remains unchanged. The intervention recompiled the existing API translation unit against the copied header and reused unchanged runtime/RNA objects; it did not substitute an engine.

## Numerical evidence

Five fixtures were exercised at default, 1, 1.05, 1.2, 1.5 and 2 for the public `CPARTY_PF_OVERRIDE_SCALE`. Each variant ran probability and target-energy operations: **60 baseline calls and 60 intervention calls, all successful**. DP09 parameters, sequence, scaffold and requested target stayed fixed. Full public fixture strings and raw outputs are in the accompanying receipts.

| Fixture | n | Baseline log-probability range | Intervention range |
|---|---:|---:|---:|
| public22 target | 22 | 2.6645e-15 | 2.6645e-15 |
| public22 empty generated target | 22 | 0 | 0 |
| PKB00048 | 61 | 2.3063124e-6 | 1.7764e-15 |
| PKB436 | 70 | 0.07870062018 | 3.5527e-15 |
| nested9 empty target | 9 | 6.6613e-16 | 6.6613e-16 |

For PKB436, baseline scale-1 log probability is -3.6884031435387143; scale-2 is -3.7671037631732744, a roughly **7.57% relative probability decrease**. All baseline and intervention target-energy ranges are at most 3.56e-15 kcal/mol.

The direct API partition probe isolates the baseline difference to the denominator:

| PKB436 quantity | scale 1 | scale 2 |
|---|---:|---:|
| log(Z_scaled × scale^70) | 22.834764046960835 | 22.913464666595388 |
| log(target_weight × scale^70) | 19.14636090342212 | 19.146360903422114 |
| ensemble energy, kcal/mol | -14.073539485782419 | -14.122044312707917 |
| target energy, kcal/mol | -11.800300000000002 | -11.800299999999998 |

The target remains invariant while the normalized denominator grows by approximately 8.19%. These finite moderate values do not indicate overflow/underflow in the reported root quantities. The causal intervention, rather than this observation alone, supports the source-index diagnosis.

The index correction also changes scale-1 log probabilities by approximately -2.24e-7 (61nt) and -1.11e-7 (70nt), because it corrects the physical unpaired-penalty count as well as its scaling exponent. It is therefore not a fitted normalization factor chosen to preserve every old result.

## Root-live instrumentation and regression

A read-only candidate observer was wrapped around the unchanged scaffolded executor and its original storage-carrier observer. Positive contributions were retained, and normalized runtime child edges were followed from the root. This records live derivation-graph alternatives; it does not assume a derivation-to-structure bijection. The diagnostic root weights match the direct API baseline at 17-digit precision.

- PKB436: 1,632 root-live VPR basepair alternatives; 1,597 have unequal k-i and j-k.
- PKB00048: 332 root-live alternatives; 320 unequal lengths.
- public22: zero root-live VPR alternatives, despite positive VPR cells elsewhere. Its scale-invariant control is consistent with this distinction.

Example live transition for PKB436 at scale 1: i=13, j=21, k=20. Old padding=7; right padding=1; local factor=0.25591072290631289, child weight=0.90723669115953587, contribution=0.23217159748176816.

Both variants additionally pass **all seven methods of the unmodified public adapter unittest suite**, including empty targets, Viterbi output, invalid input, parameter switching/missing-file behavior, and two VP-border energy regressions. This modest suite does not cover all inputs or establish a formal arithmetic bound.

A separate BE gauge concern was screened: each of the three structured fixtures has one root-live same-anchor BE base and zero root-live same-anchor BE stack alternatives. A generated-state local obstruction has therefore not yet been turned into a root-live BE counterexample. It remains a separate source/support question, not evidence erased by the VPR result.

## Full-engine target and remaining obligations

The desired proof should quantify once over admitted inputs and providers, not test or prove each numeric parameter separately:

1. Finite scheduled engine correctness: actual normalized children precede each parent; pure local factors/observer frame behavior; chart equals the complete weighted-derivation sum. Existing verified memoization/order infrastructure and supported PMFs are reusable.
2. RNA binding correctness for all admitted sequences/scaffolds/options: complete/disjoint production semantics, one-to-one derivation/structure correspondence or justified multiplicities, physical local-energy ownership and homogeneous scaling. The diagnosed VPR recurrence is one concrete correction obligation within this larger contract.
3. Actual C++/numerical/random-source refinement: operation order, floating/transcendental bounds, extraction/compiler/memory semantics and conditional randomness. An abstract exact arithmetic theorem is not this executable bridge.
4. Frozen current PRISM classifier restriction and class SumProduct masses; selection-safe adaptive confidence. These E8 endpoints remain open.

No all-input source closure, novel generic framework, or completed PRISM adapter is claimed. The evidence justifies the isolated VPR recurrence correction candidate and motivates a broader source-theory regression/gauge audit before adopting it.

## Reproducibility packet

Accompanying files contain raw public-fixture baseline/intervention calls, direct partition fields, seven-method regression results, intervention/source/build hashes, a minimal one-line patch, and the diagnostic observer/replay driver. They contain no private product code. The supplement is linked to its publisher rather than redistributed wholesale. The earlier [prior/reuse report](https://github.com/Sodelin/Research-Commons/blob/7bb162985e1f7ea74bad92c4b2ed617ab5132301/research/2026-10-02-dot-e8-targeted-prior-0601z/TARGETED-E8-NEIGHBORHOOD-AND-REUSE.md) records the established mathematical and software lineage.
