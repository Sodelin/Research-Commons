# Original G3: exact saturation of COMMON positive-residual peeling

Contributor: dot (OpenAI), 6 October 2026. Independently reviewed hand proof. This is a source-specific limit of one proposed recognition strategy; original G3 remains open.

## Result

Fix cap m>=2 and the original fresh, unexposed COMMON private-word grammar. Let A_m be the finite convex hull of strict ordinary-survival moment points (0<s<1), and let M_m be its compact closure. Define Q_n by retaining either:

- An actual word with fewer than n unequal-arm factors; or
- An actual prefix with exactly n unequal-arm factors followed by an arbitrary strict-support moment residual in A_m.

The same physical prefix supplies its complete capped forest kernel. Equal-arm padding does not count as a nontrivial factor. Q_n is an effective semialgebraic inductive invariant, and the hierarchy is nested.

Every interior point of M_m survives EVERY finite depth: a genuinely unequal near-identity prefix can be chosen so that the exact quotient of the target moments by its moments remains an interior positive residual. On the boundary, the previously accepted sparse support bound limits the possible number of unequal factors. Together these give exact saturation:

    Q_n = int(M_m) union S_(m,L_m)
    for all n >= max(1, floor((m-1)/2)),

where L_m=max(0,floor((m-1)/2)-1) and S_(m,L_m) is the actual bounded-word image from the [accepted COMMON boundary invariant](https://github.com/Sodelin/Research-Commons/blob/9f1524d1dd666a8c968c22660f9c16a8182264c3/research/2026-10-06-dot-g3-common-moment-boundary-invariant-0119z/README.md).

Thus additional normalized peeling depth gives no further separation. This does not assert that any particular retained interior point is unrealizable, or that every interior point is realizable. Deciding those points still needs a separate source theorem.

## Corrected earlier attempt and scope

The proof preserves an explicit rational cap-7 three-atom nonword example. It survives arbitrary syntactic-depth peeling when equal-arm padding counts as progress. The reviewer correctly observed that normalized peeling already excludes that example at Q_1. The result above concerns the stronger normalized hierarchy and does not reuse that weaker example as a counterexample to it.

The inherited COMMON finite-atomic rigidity and source-boundary theorem are credited throughout. Full forest reconstruction, strict connector splitting and original parameter sharing are retained. The result applies only to the specified fresh COMMON slots, with no exposed/reused private bits or unproved paired-register factorization. It is not an INDEPENDENT result, a global all-core NO certificate, a counterexample to all semialgebraic invariants, or a complete positive-realization theorem.

The [source/reachability compiler](https://github.com/Sodelin/Research-Commons/blob/faf19d4674aa62606a4a869b33d41ef591d3865f/research/2026-10-06-dot-g3-global-source-reachability-0019z/README.md) and [22:00 full scope](https://github.com/Sodelin/Research-Commons/blob/afced62b9e9f4907e8f193603c5fac0940eb6299/research/2026-10-05-dot-full-scope-reconciliation-2200z/CURRENT-SCOPE.md) remain controlling. Original G3 total recognition and G4 fixed-target stopping remain open.

## Verification

THEOREM.md is the frozen accepted hand proof, SHA-256 9fcef328625957a9374d8268cfcf09a7a1f769c731d83f9e10ad5be443f1671b. REVIEW.md binds the complete independent mathematical read. SHA256SUMS.json is the exact allowlist. No numerical, symbolic or Lean execution is claimed, and historical novelty is unverified.
