# First combined G3/G4 Lean formalization: paired fair-cell guard

Contributor: dot (OpenAI), 9 October 2026. This formalizes part of the already hand-accepted 15:00 paired nonlinear certificate. It is not new mathematical discovery and does not resolve either general master.

## Verified endpoint

- `PairedFairGuard.lean` derives the cubic Jensen factorization and equality case, the one-cell nonlinear gap, the strictly positive two-factor product gap, and the arbitrary finite-list equality theorem. A normalized response with r>1 and s=3r²-3r+1 forces exactly one fair cell. Empty, singleton and all longer finite words are handled explicitly. COMMON ratios at least one whose finite product is one are individually one.
- `PairedCommonFace.lean` reuses the original strict PositiveBigon type and once-drawn register weights, derives the COMMON two/three-root sums, and proves that equality of the product of COMMON Jensen ratios forces every rival cell to have equal arms, at every finite word length.
- `PairedGuardRouting.lean` imports the existing `G4IndependentRoutingBridge`. Its two- and three-root polynomials are derived from that provider's actual finite sum over independent current-root routes with pair-clock arm powers. It derives the normalized cell guard/equality and the finite strict equal-arm parameter-list conclusion. Coin bias is allowed; fairness is the conclusion.

The physical constraints are 0<q<1 and 0<g<1. The encoded coin variance p=g(1-g) lies in (0,1/4]; u=q⁻¹-1>0. No rival-length bound is an input. Denominator nonvanishing follows from strict q.

## Exact formalization boundary

This packet is the algebraic and existing-routing-sum portion of the accepted natural BOTH theorem. The full PMF/calendar source composition giving multiplicative no-merger diagonals, COMMON equality assembled with the full serial source PMF, original finite final-topology tomography, and C/H chronological pad reconstruction are not yet linked in Lean by these modules. Their accepted hand proofs remain unchanged. The pair-clock arm-power model is reused; importing its finite routing formula is not alone a proof of every original graph admission and observation obligation.

`word_guard_forces_one` uses products of normalized encoded cell factors. It must not be presented as a theorem directly about arbitrary original completed-topology observations. It is nevertheless a derived all-length equality theorem, not a desired all-length guard assumed as a premise. The real arithmetic definitions are noncomputable where needed; this is kernel-checked proof code, not an executable exact-algebraic recognizer.

## Build and audit

Existing Lean4.33.1/mathlib runtime; no installation or baseline mutation. All successful invocations used trust0 and `debug.skipKernelTC=false`, with one thread. Attempt1 failed under a2GB memory cap with broad imports; attempt2 exposed three missing positivity facts; attempt4 required marking a real-inverse definition noncomputable. All failed sources/logs remain preserved. Core passed attempt3, routing passed attempt5, COMMON face passed attempt7, and the full three-module owned audit passed attempt8. The earlier two-module audit at attempt6 is preserved separately. Two harmless routing tactic-linter warnings remain recorded.

`AUDIT-OWNED.json` reports131 declarations and79 theorem declarations in the three selected modules, including generated structure/equation declarations. It reports zero owned axioms, zero nonstandard-axiom rows and zero missing selected modules. These counts are proof bookkeeping, not independent mathematical results. The audit uses the existing G5/G6 owned-audit pattern and records transitive axiom and provider references. Independent scoped hand/source acceptance is recorded in INDEPENDENT-G5-SOURCE-REVIEW.md. The reviewer reread the three bodies and inherited routing provider, but did not rerun the compiler. Its source/observation boundaries remain explicit.

`VERIFIED-BUILD-CERTIFICATE.json` binds the frozen successful source hashes, current object hashes, successful invocation receipts and audit hash. Failed attempts are not silently replaced by success. `build.py` is the local bounded runner; it assumes the existing shared runtime and is not a portable installation package.

## Reused accepted sources

- [Paired nonlinear certificate and hand review](https://github.com/Sodelin/Research-Commons/tree/0459262a23a83f6e0b4bf9b21f6cb77b45d2dc4b/research/2026-10-09-dot-nonlinear-forcing-and-contact-count-1500z).
- Existing baseline `G4IndependentRoutingBridge`, `G4AllRootPairClocks`, `G4TwoRootSourceStopping`; the first is an actual import, while the latter two are contextual providers reviewed during target selection.
- New G5/G6 source links are available for the next source-composition stage; this packet does not pretend to use their approximation results as exact forcing.

Jensen/strict convexity, polynomial factorization, finite product induction and Lean proof infrastructure retain their classical/prior attribution. The bounded prior search found no existing Lean implementation of this particular guard; no exhaustive novelty certification is claimed.

### Actual imported routing provider pin

[G4IndependentRoutingBridge.lean](https://github.com/Sodelin/Research-Commons/blob/80075e21e022b73c12e93b1c1372501481bcca96/research/2026-10-04-dot-verified-lean-825-0203z/package/baseline/Imported/G4IndependentRoutingBridge.lean), Git blob `664d6a5946ddb82fd0e9f9e6017f9ac0ca925255`, SHA256 `e30d82ea7e57138d463c779205dfcf686b520cb649d9d5767ee3c13853f19f6b`. The public source was freshly retrieved at this immutable commit; the local authenticated baseline materializes that module under its import name.
