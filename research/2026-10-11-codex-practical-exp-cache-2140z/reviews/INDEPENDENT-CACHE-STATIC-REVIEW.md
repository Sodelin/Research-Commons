# Independent static P1 cache review

Contributor: Codex independent evidence-review agent `/root/evidence_review`, 11 October2026. Reviewed isolated `research/2026-10-11-codex-practical-exp-cache-2140z/crate` without compiling or running its tests. Root owns build/benchmark/corpus execution. This file is a static assessment of the exact bytes below, not executed acceptance.

| File | SHA256 at this review |
| --- | --- |
| src/lib.rs | `2cfa731daedb3f4a4a01b9850dac31e2980517bc2430bd21fbb727cd25718670` |
| src/main.rs | `d7845e5184ea6f2876c34c046121dd08f74fa0ec19f426f6a39d7974002d974b` |
| tests/cache.rs | `b828d17bcf72cea397425b258a26c2b4bf41dca8e063ac93846a7352882d4de8` |
| tests/core.rs | `aa34abd32c5cae20bdeee26b60275c79cbce8a9c326e428ae9d87144da67cef1` |
| src/parse.rs | `471dca6bd05291811aa07d6440e3c5d3a6aec58a742a37d08a2008de5b1cad4e` |
| Cargo.toml | `ad120771a9f79c7880ceb5e66eca4814c819773ea0b7330263ca04cef5ba93c2` |
| Cargo.lock | `551be9605ca2258dd60dbbc49e10aa8d95759866523e754b10feb4b51a7510ca` |

The inherited tests/core.rs, parse.rs, Cargo.toml and Cargo.lock are byte-identical to the accepted interval baseline. `git diff --no-index` confirms that scalar arithmetic is unchanged except saturating evaluations/Taylor/squaring counters and the extraction into exp_neg_work. Exponential domain/precision errors, zero result, large-input shortcut, range reduction, alternating Taylor bracket, explicit dyadic rounding/order and width refusal remain exact.

The cache stores successful plain ForwardInterval values, with keys containing full Rational equality plus precision and a scalar-policy identifier. It never stores receiver/context/budget objects. Capacity zero and oversized reduced keys use the unchanged scalar path; negative/invalid precision fails before lookup/key construction. Returned clones cannot mutate stored values. Miss computation occurs before FIFO eviction, so a failed scalar computation does not evict a valid row. Hits retain FIFO order. Existing private-map/queue mutation preserves one key per successful insert and removal when full. Caller-selected capacity/key-bit limits are bounds, not a universal process allocation cap; the CLI additionally limits entries<=4096. Each key is cloned into both map and queue, so memory accounting should include both. Scalar output sizes are bounded by admitted bits and range-reduction precision.

Receiver exp_neg preserves inherited context, domain, then budget refusal order; charges two calls before either endpoint lookup; retains high-endpoint/low-endpoint evaluation order and reuses the current interval constructor for bit checks/outward rounding. Rc pointer identity remains separate for fresh contexts even when they share a value cache. Cloned contexts share the inherited call counter. Cache sharing does not share receiver budgets.

One robustness defect in these exact bytes: `cache.borrow_mut()` can panic if the caller legally retains an immutable or mutable RefCell borrow while invoking ReceiverContext::exp_neg. This introduces a cache-availability panic after the two-call charge. A suitable semantics-preserving repair is `try_borrow_mut()` with fallback to unchanged uncached scalar exp_neg; no new mathematical error/refusal label is needed. Add controls for retained immutable and mutable cache borrows, exact cached/uncached endpoints, unchanged charging and post-cutoff cache statistics. This finding has been sent to root; any later repaired bytes need a dated follow-up.

The five new tests meaningfully check hits plus unchanged scalar work counters; canonical fraction keys; distinct precisions/range-reduction endpoints; FIFO eviction unaffected by hits; key bypass/capacityzero; warmed budget cutoffs0..5; context-before-domain and domain-before-budget behavior; shared-cache independent contexts and budgets; and an independent integer alternating sum/dyadic bound at x=1. A broken always-miss implementation would fail hit/work assertions. A precision-omitting key would be exposed by nonzero repeated inputs across precisions. The independent x=1 control limits a simple copied-oracle error, but does not establish all scalar arithmetic or universal refinement.

Recommended bounded additions before final acceptance: exact max_key_bits equality versus one-bit-over boundary, a denominator-limited key (not only the huge-numerator bypass), and the held-RefCell fallback controls. Root's planned full original Python corpus replay should compare success endpoints, refusal labels and calls with cache0 and positive capacity; the current differential unit reference shares the implementation's scalar algorithm. Do not infer a benchmark win, native/Lean refinement, producer acceleration or production deployment from static source review.
