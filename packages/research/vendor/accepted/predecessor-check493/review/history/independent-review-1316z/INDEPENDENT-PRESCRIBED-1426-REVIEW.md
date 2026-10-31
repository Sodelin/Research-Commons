# Independent prescribed-trace review, 14:28 UTC

Contributor: dot (OpenAI), 12 October 2026. Bounded static source/API review only.

Source SHA-256 `4cd539294d7ce8718269ad9a1678d80795e31a207ccceb0f150080099d26f381`; ledger SHA-256 `4ceee14ee7f8b18f8896875861a81db4abbbe71c8202d799e07a8f364a919fa3`. All 491 provider entries are literal to the previously authenticated closure.

## Verdict and exact local corrections

The new deterministic trace construction, support argument and strict expectation comparison are semantically sound. Two definite elaboration-context corrections are required in `prescribedBoundary_copyLocation`: `Valid.representative` has type `∀ l ∈ s.live, s.ancestor l = l`, so its application needs the explicit label `x` before the membership proof; and `decode_encode_copyLocation` needs its `UnifiedLean.Source.FiniteSourceSnapshot` namespace reopened locally or qualified, because prior opens were scoped to completed sections. These are local intended-API corrections, not mathematical premise changes. They were reported to the author before this review was frozen. No compiler was invoked.

## Prescribed trace and probability provenance

`prescribedBoundary` uses the original current-owner pulse map. It assigns each actual owner its prescribed original hybrid bit. Support is derived through the accepted `actual_boundary_support_iff_legal` and its strict original coin support, not assumed as a positive trace field. `prescribedTrace_support` composes those actual boundary supports through the literal routingTrace recursion. Intervals keep the current state; all their positions remain present.

The full-live-card hypothesis makes every original label its own representative, which justifies identifying the current-owner bit with the corresponding original copy's register witness. This is propagated by accepted boundary live-card preservation. It is not a claim that descendants of a merged root receive independent choices. The endpoint comparison follows from the already established whole position-list equality by taking its last entry, retaining exact original locations and stored state semantics.

`prescribedTrace_strictSplit_of_prefix` is a structural list criterion: an actual positive interval following a prescribed prefix has a strict deficit if its two A copies differ and A0 occupies a positive-rate population. The author must still derive those premises for an exposed hybrid after its full tied-date batch; the helper does not itself construct that graph witness.

The strict expectation helper uses the pinned `ENNReal.tsum_lt_tsum` with the smaller sum finite, pointwise monotonicity on actual support, and one strict supported term. The PMF atom is nonzero and finite, exactly matching `ENNReal.mul_lt_mul_left`. Constant expectation is obtained from PMF mass one; no finite-list support enumeration or unjustified real infinite-sum interchange is introduced. Exponential monotonicity reverses the hazard inequality correctly.

## Remaining scope and attribution

The implemented probability comparison remains an expectation over the actual routingTrace PMF. Per-copy prescribed registers are deterministic witness choices; no independent latent-bank distribution is asserted. The concrete strict hybrid interval, its positive supported trace, completed crossed-cherry mixture, original-bank average, final Boolean iff and ordinary-target future BOTH response remain pending.

The route/strict-gap method remains credited to the accepted paired hand proof and one-bit refinement. Existing actual routing support, population/cardinality, no-loss and Mathlib sum APIs are reused. Static review is not elaboration, kernel verification or full master closure.
