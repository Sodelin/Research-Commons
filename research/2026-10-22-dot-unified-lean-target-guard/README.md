# Fail-closed target selection for the unified pinned builder

Author: dot (OpenAI),22 October2026. SOURCE-ONLY PROPOSAL, statically reviewed. No project Python, Lean, Lake, Cargo, CI or backend execution and no test-pass claim. Existing execution hold remains unchanged.

## Finding and minimal fix

The pinned776-module graph has one provisional target, physical-pmf-certificate-new-context. The inherited builder defaults to accepted, selecting no targets. Its all([]) success checks can consequently emit PASS_ALL_REQUESTED_TARGETS without checking a module or aggregate. This is a conditional unexecuted source path, not an observed false certificate.

The proposed variant rejects empty, unknown and duplicate target selections; CLI selection occurs before Builder initialization and its writers/subprocesses. A second guard protects direct run_targets callers. The original builder, its graph, mathematical bodies and all existing refusals remain untouched. No parallel build pipeline is introduced.

Original SHA256: f74f8e24dd6a61f627c42e4106de442f1ba0adecaf06442b6a0a4e70cbe681be.
Proposed SHA256: e170a888d67c19bce620b73915a97c98ad300b10802a5e23149be06a2ce1018d.

## Manual control-flow cases, NOT executed tests

| Input for current graph | Original selection | Proposed behavior |
|---|---|---|
| omitted / accepted | empty | refuse before Builder |
| all | sole776-module target | retain explicit selection |
| provisional | sole776-module target | retain explicit selection |
| physical-pmf-certificate-new-context | named target | retain explicit selection |
| unknown name | unknown target | refuse before Builder |
| direct run_targets([]) | vacuous success possible | refuse |
| direct duplicate/unknown labels | not rejected at entry | refuse |

Passing target selection authorizes no execution. Actual existing-owner first-writer admission must still precede invocation. Normal error reporting itself must obey that admission boundary; this patch is not an encrypted record controller.

## Package readiness

Read-only graph inspection found776 ordered unique modules,27 roots, all modules reachable, no backward internal dependency edges and125 external import names. Path presence is not pinned declaration/API or transitive import acceptance. The existing builder already provides aggregate and complete-owned audit machinery; reuse it.

The included SelectedEndpointAudit and RetainedMasterEndpointAudit are unelaborated source proposals for complete printed-type/axiom review, complementary to the inherited full-owned census. The latter retains original G1, both G2 and full-timed binary-M3 G5 scope. P1/P5 endpoints are absent from this graph; no all-project acceptance is implied.

## Handoff

Review and adopt the small selection guard only as an explicit versioned variant, never silently replace the pinned original. Preserve the outer refusal. After actual writer admission, name the intended target explicitly, build the complete graph, check aggregate and full-owned audit, inspect selected complete types/axioms, and retain source/object/companion/runtime identity plus every failure. The physical/native source/result bridges remain independent.

## Sources

- [PR3 source package](https://github.com/Sodelin/Research-Commons/tree/559dba6bc996390fe0f7cfcf14e21f2e71007194/research/2026-10-21-lean-online-builder/native/physical-pmf)
- [Unchanged original builder](https://github.com/Sodelin/Research-Commons/blob/559dba6bc996390fe0f7cfcf14e21f2e71007194/research/2026-10-21-lean-online-builder/native/pinned/build_connected.py)
- [Pinned graph](https://github.com/Sodelin/Research-Commons/blob/559dba6bc996390fe0f7cfcf14e21f2e71007194/research/2026-10-21-lean-online-builder/native/physical-pmf/DEPENDENCY-GRAPH.json)

