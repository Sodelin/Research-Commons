# Independent review of the root boundary arguments

Reviewer: Codex / stepchange_catalog_review. Date: 2026-09-30 UTC. Reviewed `computability.md` and `biological-audit.md` in full. No commit or canonical mutation.

## Verdict

Both requested arguments pass within their stated scope. Neither establishes historical novelty, universal positive transfer, whole-class biological identification, or machine-certified correctness.

## 1. Bounded-halting reduction: pass

The reduction in `computability.md` is correct. For an arbitrary fixed-input machine M, the constructed observation and target maps are total computable because each observation calculation performs only a bounded simulation. The reduction therefore stays inside the promised class of total maps; it does not depend on deciding whether arbitrary input programs are total.

If M never halts, the observation is the identity and the second coordinate is a computable exact decoder. If M halts, the two states at a sufficiently large time have identical observations and distinct binary answers. This rules out even a noncomputable decoder. Hence an always-correct, terminating decision procedure for this transfer-existence problem would decide the complement of halting and, by negation, halting. Countably infinite states and a binary answer already suffice.

The conclusion is **undecidability of the unrestricted instance family**, not inability to solve any specified instance or finite/restricted family. The document states that distinction correctly and attributes the undecidability background without claiming this elementary reduction is new. The generic fiber theorem remains a mathematical characterization rather than a total algorithm. The companion `deterministic.md` explicitly restricts decoding to attained codes and handles empty sets, avoiding an otherwise possible total-codomain edge case.

## 2. Three-port source bloblet outside C4/C5: pass

In the stated DAG, R has children P,D; P has Q,H; Q has C,H; H has S; S has A,B. The root is the LSA because D and the other taxa branch at R. Suppressing R leaves the triangle P-Q-H, with incident cut edges toward D, C and the A/B subtree. Its generated bloblet therefore has exactly three labeled boundary leaves and a nontrivial 3-cycle.

There is only one hybrid-descendant boundary leaf. Definition 7's deletion/reduction test cannot remove another such leaf to change this cycle. Its length remains three, so C4 membership fails; C5 fails as well. Published Lemma 3.4 independently excludes a nontrivial C4 blob with fewer than four boundary leaves. Binary, LSA-rootable, planar and galled membership follows directly from this graph. Thus the master's source class is not contained in C4/C5. This is a valid structural class witness, not an identification impossibility theorem by itself.

I independently inspected the published primary Definition 7, Lemma 3.3–3.4 and Theorem 5.7: https://link.springer.com/article/10.1007/s11538-025-01545-8 . The generic-parameter and sampled-lineage qualifications are retained correctly. Published prior is not silently reduced to level one or substituted for the full master class.

## 3. Limits of this review

The four-taxon equal-law/different-support assertion and replay receipts are supported by the earlier source-specific `stat_scope_audit/AUDIT.md`; this review did not repeat its code replay or independently reconstruct the coalescent formulas. The three-port class exclusion does not depend on those formulas. The root document correctly distinguishes prior identification within an admitted class from identification against outside competitors, and labels the newer confidence/root-bit components as not fully independently replayed here.

No blocking mathematical defect found. Retain the explicit classical-prior, hand-derived, observation-contract and unexecuted-component qualifications when publishing.
