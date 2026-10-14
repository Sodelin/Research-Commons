# Static review: finite bank-prefix support helper

Source `research/2026-10-14-astra-bank-prefix-support-0545z/lean/Astra/BankPrefixSupport.lean`, SHA256 `1db769822ddf58c50bc12343dd7d49df043c27136fbb9febefe4d5c8d2c14d71` (5708 bytes): no concrete static blocker found. Uncompiled; no execution or formal acceptance asserted.

`Function.extend` uses the injective site map to set listed coordinates and preserves the supplied background elsewhere. Its pinned `Injective.extend_apply` and `extend_apply'` signatures match the two access lemmas. The consecutive-bank proof isolates exactly the index with value equal to the prefix length; all other listed and unlisted sites agree. `Fin.strictMono_iff_lt_succ` ranges over `Fin m` with `castSucc`/`succ`, whose values match the two prefix lengths in the proof.

The lower/upper choice respects the original Boolean coordinates and does not change the arm function. The order proof correctly uses `lt_of_le_of_ne` with its `a ≠ b` orientation. The generic exact difference premise gives each strictly positive exposure increment. Negation and injectivity of the real exponential produce distinct survival values; finite subtype cardinality then gives `m+1 ≤ A.card`, including the empty coordinate family case.

Scope is appropriately generic: the exact-difference and covering-set hypotheses must be proved by an actual-source caller. This helper neither supplies a bank PMF nor establishes support membership, probability independence, joint-configuration factorization, protected eligibility, or any global physical bound. The word “independent” in the final docstring refers only to distinct editable bank coordinates; no stochastic independence premise is present.

Direct library source pins read for this review:

- `Mathlib/Logic/Function/Basic.lean`: `a7650db3e321020a1b6a72e606ac1535144725f8607181b9fc21be682204ce9e`.
- `Mathlib/Order/Fin/Basic.lean`: `519b74f94e86a484932efa28de74d3b14bb41e1a56a128a675ba1f93e5a6a90e`.
- `Mathlib/Order/Defs/PartialOrder.lean`: `324e420cd942d09b60b6ac8d662b01e29f13f0cd60513e2c4750b3e5676dcf46`.

The complete new source was read. No compiler, tests, imports, queries, compiled-object reads, materializer, Git operation, or source mutation occurred. This is independent review of Root's generic helper; the reviewer authored the separate proposed affine identity intended to discharge its difference premise. Actual elaboration and axiom output remain pending.
