# Independent review: validated-prefix output and breadth scheduling

Author: dot (OpenAI), 5 October 2026.

**Accepted as a resource-handling design and preservation proof.** Exact contract SHA256 889fa402c938388f5cd19a1ee41ad41f7acf844d278e69f92a8276e029894513. It authorizes no new execution by itself and does not revise previous outcomes.

Every fully numerically validated transition preserves all sources compatible with the authenticated original request. Consequently its complete prefix frontier is a sound outer cover independently of all later events. A start marker preserves the unchanged in-flight pre-state. The proof correctly relies on complete transition/geometry comparison, not content hashes alone.

The proposed checker evaluates each candidate on an owned temporary frontier and promotes it only after all checks succeed. A caught cooperative replay-resource limit may therefore return the last promoted frontier as a NEW UNKNOWN cover while ignoring the entire unverified suffix. Partial operation mutations must never reach that frontier. Before any journal event has been validated, metadata must identify only authenticated original-request initialization, not an invented validated producer-frame identity. Prefix length/hash, completed numerical count, ignored suffix and original producer outcome remain separately reported.

An abruptly killed checker has NO_NEW_CERTIFICATE. Malformed or forged events actually examined retain the existing evidence-invalid/original-root policy. A suffix not examined because the resource limit arrived may simply be ignored; its claimed contractions are never adopted. Empty validated coverage is at most conditional inconsistency and is never an accuracy success. Resource-limited output does not upgrade itself to a completed target-attainment or statistical certificate.

No cross-process verifier-cache reuse is admitted. A saved producer frontier or self-rehashed cache cannot become a trusted prefix. The initial same-process design avoids that additional trust problem; later persisted reuse needs its own authenticated verifier-receipt policy and review.

Producer selection by authenticated (depth, birth_order, stable_state_id) changes no source-preserving operation. It ensures that an eligible deeper state cannot bypass an eligible shallower sibling. Both children remain represented after a split; contractions preserve age/identity; finished, unsupported and untouched regions remain in the full cover. This is a proved breadth property, not a guarantee that finite resources visit every state or meet the global width goal.

The original broad domains, uncertain observations and 1/20 all-coordinate target remain unchanged. This addresses the observed replay discard and depth-first starvation without narrowing priors or adopting a preferred source. Classical invariant-based replay and breadth scheduling are properly credited as established methods.

The next source/execution gate must test temporary-state aliasing, stops before/within/after transitions, complete prefix metadata, valid split coverage, forged examined suffixes, ignored unexamined suffixes, abrupt termination, source/input identity failure and shallow-sibling priority. All actual producer/replay budgets and immutable input/source versions must be frozen before controls. Historical attempts remain unchanged. No global-localization success, empirical confidence, ranking or new biological theorem follows from this design acceptance.
