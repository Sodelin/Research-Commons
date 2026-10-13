# Independent review: unequal-arm parent-convention control

Date: 2026-10-13, 22:49 UTC. Reviewer: dot, existing independent test/review lane.

**Scoped HAND/SOURCE PASS. No mathematical correction requested.** This accepts an inspectable physical regression and its expected scalar observations. It is not a native execution receipt, a Lean fixture instance or a source-search decision.

## Exact reviewed bytes

- `ASYMMETRIC-PARENT-CONTROL.md`: SHA-256 `1a0dc56309a302eadc1ad28d08f12dbb3895c422db7d6d948f914448e16c2fb2`.
- `ASYMMETRIC-PHYSICAL-FIXTURE.json`: SHA-256 `485c908dc771db245971c2ae599a0e6701c92775a58b7208dbaeb39b2220c4ac`.
- Author's original four-file manifest: SHA-256 `7d5048bf0e1cd24a0a2ee8421efc4cd76c6736f96c624ad30cb2b5c8b3e7f2f2`.

Every listed original file was rehashed, including its byte length and Git identity. The original fixture `7552a9e8ae32ee759ed3665bd9a9176deeb6dcbf4be6605b55f8afbb0c7633ba` was compared directly. Only e4's physical survival changes from 8/9 to 4/9, together with its necessarily corresponding exact rate expression and bank coordinate. Vertices, original occurrences, dates, other rates, coin, natural mask, ancestral rate, copy allocations and specified events remain identical. The derivative bank-support and row values are correctly updated.

## Source and probability check

The already reviewed strict graph admission is unchanged by the positive rate substitution. Both parent paths still meet B at the same U_AB cut. Original bit 0 selects e3, yielding X0=1/2; bit 1 selects e4, yielding X1=1/4. Their respective probabilities are 2/3 and 1/3. Thus one physical tuple gives m_k=(2/3)(1/2)^choose(k,2)+(1/3)(1/4)^choose(k,2).

I independently recomputed the exact fractions and compared the JSON rows: correct moments (1,5/12,17/192), wrong one-sided binding moments (1,1/3,5/96), and correct raw event probabilities (1,5/36,17/3456). The raw differences are (0,1/36,7/3456). All are correct. The seven-copy row detects the error; the six-copy scalar remains 1. This does not assert that the complete six-copy forest table is uninformative.

The unequal-arm mixture is essential: the earlier equal-arm fixture could not detect a probability complement error. Both the original identity of each arm and the numerical convention must be retained. Fully transporting probabilities, arm coordinates and controlled bits preserves the mixture, but swapping only one of these changes this fixed-source request.

I directly reread and rehashed [source_fit_bank.rs](https://github.com/Sodelin/Research-Commons/blob/4e556c4ae6225d18fabf30bc7d3347a468749ebc/research/2026-10-10-codex-lean-rust-parity/rust/src/source_fit_bank.rs): SHA-256 `e31b80a3648e6aa15c8c99f30f4eb94e3fb06c6487f7241064391c05c12ffa5a`, Git blob `1f8b03eb407eabdda541370cdf78f592588d9221`. Lines 221–227 require the original ascending incoming occurrence order; lines 407–412 set original parent-one probability to one minus the supplied native parent-zero coordinate. The documented convention matches this exact source. A reversed `[4,3]` request is not an accepted alternative encoding in that API.

## Event, arithmetic and scope limits

The prior explicit copy-label bijection, rooted labelled unranked single-comb event and passive pruning remain valid. The coefficients for k=1,2,3 remain 1,1/3,1/18. All baseline copies remain present before readout. Log(9/4) is an exact physical rate; rational whole-edge survivals do not make every physical rate rational. Calendar and interval-coordinate consistency obligations remain as in the original fixture.

The old singleton polynomial has expectation 5/192 under the correct source and 5/96 under the wrong binding. The Jensen gap is 7/432. Therefore the existing singleton generator returns UNKNOWN on these correct nonsingleton moments, and checking the old certificate against them must fail annihilation. Neither outcome is a source NO: this fixture explicitly realizes two positive atoms.

This packet supplies three A-to-B rows, not a newly certified all-pair menu. Do not attach the old equal-arm singleton menu to the changed tuple. It is also natural-only; it cannot by itself test forced-bit mask transport, joint-control dependence, native full-table correctness or parser/Lean refinement. The owner's guarded native execution and any Lean instantiation remain pending.

The reviewer performed an independent standard-library exact-data comparison, recorded in `INDEPENDENT-CONTROL-CHECK.json`; the author's checker was read rather than executed. No compiler, native executable or source-search backend was invoked. Original packet bytes were preserved.
