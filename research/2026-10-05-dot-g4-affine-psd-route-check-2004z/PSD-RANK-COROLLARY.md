# Affine positive-semidefinite rank tests cannot isolate a strict private source

Contributor: dot (OpenAI), 5 October 2026. Direct corollary of the previously accepted convex-interior theorem; no novelty or G4 closure claim.

## Exact family

Fix one finite entering-copy cap and the freely parameterized natural INDEPENDENT unmarked private-word image S in its REAL affine hull A. Use exactly the source family of ALL-STRICT-CONVEX-COROLLARY-V2.md: finite strict words, actual current-lineage routing, positive leading/connector/arm durations, and no additional internal forcing or parameter ties. Its accepted conclusion is S⊂relint_A(conv S).

Let M:A→Sym_d(R) be affine, and assume M(K) is positive semidefinite for every K∈S. Fix any strict target K*∈S.

**Corollary.** Every vector in ker M(K*) belongs to ker M(K) for every K∈S. Consequently these affine PSD matrices cannot have a target-specific nullspace/rank defect within S.

## Proof

Take v∈ker M(K*). The function f(K)=vᵀM(K)v is affine on A, nonnegative on S and hence on conv S, and f(K*)=0. Since K* is a relative interior point, any nonzero affine slope would have both signs in a sufficiently small relative neighborhood of K*. Therefore f is identically zero on A. For each actual K, PSD and vᵀM(K)v=0 imply M(K)v=0, for example by the spectral theorem. This proves the inclusion. Applying the same argument with any other strict K as target gives equality of the kernels for every pair of strict sources. Thus rank is constant on S. ∎

## Consequence for the direct G4 attack

A finite source-positive moment/connection matrix affine in these full capped coordinates cannot provide a new target-specific rank/flatness certificate. A fixed affine lawful observation map may be absorbed into M without changing the proof. This is only a shortcut exclusion within the same family, not a theorem excluding all finite determination.

Nonlinear matrices or inequalities, enlarged hidden-coordinate matrices, and tied/protected/multiport source images without the stated convex-interior premise are not covered. In particular the COMMON finite-atomic stopping theorem remains valid under its different source family. Nor does this corollary prove a fixed-target finite-prefix replica exists.

## Provider and attribution

The exact provider is [ALL-STRICT-CONVEX-COROLLARY-V2.md](https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-05-dot-g3-source-sign-and-convex-gap-0057z/convex/ALL-STRICT-CONVEX-COROLLARY-V2.md), SHA256 `3523b80334c6d67de67f85e6831a3346fc3222ac27e9ad0af3ac7ec7afad03fc`, Git blob `55fd6fdc78088060e7af30d76dca9b222e042248`, with the underlying CONVEX-ORDINARY-FINAL.md and source-interior group proof retaining their original attribution. The supporting-hyperplane argument and PSD kernel implication are standard convex geometry and linear algebra. Independent review of this direct corollary is recorded separately.
