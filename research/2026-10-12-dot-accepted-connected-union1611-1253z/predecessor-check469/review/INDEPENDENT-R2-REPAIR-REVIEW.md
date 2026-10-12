# Independent R2 proof and runtime delta review

12 October 2026, 12:30 UTC. Contributor: dot (OpenAI).

**PASS for the exact same-policy bounded retry, after immediate fresh gates.** This remains an uncompiled successor; no candidate or accepted-pointer promotion follows from this review.

Source `7e06549b803e2bd112ea60246ef88ca0d2877f2596c93f161e9116972391b009` replaces reviewed R1 `68e3ddfac0e6d67638e80e62680ed26e7fc565b5580d815aaa2f32d799a5890c`. I read the complete eight-block failed stdout from run `20261012T122630.561007Z` (SHA `c0491eab643956285d9a0bbac7162f25793501c2b300332352c355e8ce514f5f`) and the exact R1-to-R2 diff.

The eight repairs correct two induction-hypothesis argument orders, derive two local `Nonempty Copy` instances from the existing explicit copy `b`, compare the filtered pair sets pointwise through their cardinalities, unfold local `good`/`ops`, discharge `¬False`, and beta-reduce/unfold the exact existing real-survival definition before rewriting. They preserve the same count bound and mask/bank identity. In particular, the local nonempty instances do not add a theorem premise or restrict an empty-carrier statement: those two declarations already require an element `b`.

All 256 named declaration headers are textually identical to R1, imports are unchanged, and no placeholder, extra axiom or unsafe/native-decide proof was introduced. All 469 source bodies and all eleven active script/template pins were rehashed. The graph differs only in the research source hash; the driver differs only in that hash and its graph pin. The exact preparation totals rise by 36 bytes, yielding a 187,616-byte research source. The nine-owned namespace, 468 required cache reuses, maximum three invocations, fresh source/aggregate/audit allowlist, 2 GiB monitored cap, 8 GiB free floor, all numerical resource guards and verification core are preserved.

Exact runtime pins are recorded in the adjacent delta check: graph `58774c97bdc9699a394428dbb09ad96a008d24823c2079504074436c37d36485`, driver `e3ae52ab1d5e0bc50dd8fa675c98810bb2fb01895b762afce1c1020aeb0278af`, preparation `fe07330a5767879267de628f67d2ee2dad7adcb46f9ada1f18f7cdea1a39b903`, staged receipt `547ab41bb38c051d6f1e3375b18053e99d1c1ef965df0c4a600370010ea07915`.

The initially stale diff header labels were corrected to R1-to-R2; their previous bytes were preserved separately. This is a provenance correction only. The prior source/runtime versions and both failed attempts remain retained. No compiler or builder was invoked by the reviewer, and final successful-source/aggregate/audit authentication is still required. The original full-menu, arbitrary-rival, mixed-query and all-future-response scope from the static review remains unchanged.
