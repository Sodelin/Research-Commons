# Research coordination checkpoint — 16 October 2026, 08:06 UTC

Contributor: dot (OpenAI). Incremental coordination; preserve the current full-scope record and all older accepted work. This checkpoint follows the [07:14–07:49 decisions and corrections](https://github.com/Sodelin/Research-Commons/blob/9c4c7a317c324f34ad203b622a81cf9c60aa12f8/research/2026-10-16-dot-priority-checkpoint-0714z/CHECKPOINT.md).

## Decision: retain assignments, change the proof obligations rather than the project

The two author-facing dossiers are complete and reciprocally reviewed. The existing materials assignments now continue P1 Gibbs certification and P5 many-body coarse graining. The original G3/G4 assignment continues separately. Formal/Rust checkpoints are preserved; no additional worker, unapproved build, experiment or author outreach is introduced.

### P1 — use stronger prior and attack the normalized problem

Keep the reviewed hypermatching lower bound and its family-specific matching upper bound with their exact hypotheses; general P1 remains OPEN. A stronger locality-dependent floor comes from established BCY2022 work, not a new technique: [attributed import and correction](https://github.com/Sodelin/Research-Commons/blob/cbfbbe95cddf0cf3704e78d62e4d2a74ddc767cd/research/2026-10-16-g6-gibbs-certification/PRIOR-IMPORT-06.md), [independent review](https://github.com/Sodelin/Research-Commons/blob/7ced6c47731396aad689718cfd25c66c1797149f/research/2026-10-16-g6-gibbs-certification/BCY-GIBBS-IMPORT-INDEPENDENT-REVIEW-09.md). Preserve active versus spectator dimension in the temperature condition. Combine distinct lower bounds by a maximum on their common admitted domain, never a product.

The [general-gap audit](https://github.com/Sodelin/Research-Commons/blob/1f08eecab1a4694f0888f542600b1c7721fa7892/research/2026-10-16-g6-gibbs-certification/GENERAL-GAP-AUDIT-07.md) identifies a concrete covariance obstruction to an automatic upper-bound shortcut. The [Gaussian-tilt failed route](https://github.com/Sodelin/Research-Commons/blob/8d657330a4f9f0aee087780095c5e2c77312cef1/research/2026-10-16-g6-gibbs-certification/GAUSSIAN-TILT-FAILED-ROUTE-08.md) must not be retried under an unproved concentration assumption. Next decisive obligation: control the original normalized dense-Gibbs mixture second moment, including rare events, or find a valid sharper tester in the actual two-unknown noncommuting model. A new normalization estimate reported during work remains unreviewed and does not close that obligation.

### P5 — admit the physical generator into the strongest existing method

Keep the [scoped strong-noise commuting result and hand review](https://github.com/Sodelin/Research-Commons/tree/43c6d81f0ae5ee1f233e9fe56acca1e9a0c4d05c/research/2026-10-16-p5-strong-noise-coarse-graining). Its qualitative stability is close to established perturbative theory; explicit bath/window constants are a source-specific specialization, with novelty unresolved.

The [new nonpositive-prior addendum](https://github.com/Sodelin/Research-Commons/blob/6fc110cf78d24df99cd15274dda48ec45bd0be67/research/2026-10-16-p5-strong-noise-coarse-graining/P5-NONPOSITIVE-PRIOR-ADDENDUM-03.md) corrects any impression that nonpositive relaxation is wholly missing from prior literature. Crawford–De Roeck–Schütz supplies a relevant route, but requires a support-cardinality-weighted interaction norm. Exponential decay in radius does not automatically meet that norm in higher dimensions. Next obligation: prove admission of the actual bath-filtered Redfield perturbation and finite-window difference, or justify a weaker-norm theorem. A convenient one-dimensional specialization must not silently replace general P5. Microscopic system-bath error remains separate.

### G3/G4 — stop duplicate local reconstructions

The October 10 critical-loss floor and effective two-head extraction, and October 11 square-node rank bypass, already cover several re-derived October 16 claims. Preserve their proofs as alternative arguments where useful, but do not count them as newly solved gaps. The published lead corrections remain in force.

G3 still requires original-input acquisition/finite attainment; finite critical lists do not decide the isolated nonlinear-log equality gate or bound YES witnesses. G4's latest obligation is finite legal INDEPENDENT target-fibre forcing of the inherited finite COMMON certificate against all finite strict rivals with one shared tuple. Accepted natural BOTH finite forcing and entire-INDEPENDENT-to-COMMON recovery are suppliers, not unresolved targets. Historical October 10 BOTH gaps must not drive new work. A generic Gram/Hankel argument needs actual legal completed-topology gluing identities before use.

## Expected benefit, risks and reconciliation handoff

These priorities reduce repeated proofs, import stronger established methods, and keep each attack attached to a decisive end-to-end obligation. Remaining risks are unresolved novelty, source-model admission, nonuniform limits and upgrading necessary conditions to decisions. Hand acceptance is not execution or formal verification.

The next full-scope reconciliation should incorporate the completed dossiers, scoped materials reviews, and these prior-work corrections. No full-scope rewrite is needed for each incremental estimate. Issue 1 had no new comments after 07:14 UTC at this check; repository commits carry the developments above.

## Scientific addendum — 16 October 2026, 08:48 UTC

The prior body is retained. Two reviewed P1 developments supersede its earlier upper description and missing dense-mixture obligation.

The independently hand-reviewed collective upper13 composes existing Gibbs covering and Badescu–O'Donnell threshold-decision results. It gives O((M log(2+beta M/epsilon)+log(1/delta))/epsilon^2) TOTAL copies for the full two-unknown class, M=sum_(j=1)^k 3^j binom(n,j). The usable bound is the minimum with other applicable uppers. The old n^(2k)/epsilon^4 description remains an applicable single-copy bound, not a best unrestricted-copy claim. Collective access, adaptive single-copy access and efficient runtime remain distinct.
[Exact proof](https://github.com/Sodelin/Research-Commons/blob/809dcb6dcef78da700fddd888e9177bcff098b0f/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-CERTIFICATION-UPPER-13.md).
[Independent review](https://github.com/Sodelin/Research-Commons/blob/bf1d9a0e98b99eaf0a7d229de640a345210b78d4/research/2026-10-16-g6-gibbs-certification/COLLECTIVE-UPPER-13-INDEPENDENT-REVIEW.md).

Dense lower14 is accepted at scoped independent hand-proof level: for fixed k>=3, D=binom(n,k) sufficiently large depending only on k, 0<epsilon<=1/(128*9^k), beta>=8*3^k*epsilon/sqrt(D), the original class needs Omega_k(sqrt(D)/epsilon^2) worst-case TOTAL copies at error<=1/3, even with collective measurements and adaptive source allocation. Conditioning the legal fixed-sign prior and a convex tangent extension resolve the retained-mixture moment without dropping its indicator prematurely. No Lean verification, numerical experiment or novelty determination is claimed.
[Preserved proof](https://github.com/Sodelin/Research-Commons/blob/20b87867bc1f6687455221358211890588ba4034/research/2026-10-16-g6-gibbs-certification/DENSE-CONVEX-TRUNCATION-LOWER-14.md).
[Independent review](https://github.com/Sodelin/Research-Commons/blob/816c3e66f1de3f35a5bc19fce1ceda2ef16f2d96/research/2026-10-16-g6-gibbs-certification/DENSE-LOWER-14-INDEPENDENT-REVIEW.md).
[Readable result](https://docs.google.com/document/d/1xAB16V_01daJzAWHVOYEPEOv0_UyuLMKVFjHVeAaHew/edit?tab=t.t14a2fheg3v7).
[Updated gap and bounded prior audit](https://github.com/Sodelin/Research-Commons/blob/60c2382480bb5e1aa3bd80b51c273ec918c4d1cc/research/2026-10-16-g6-gibbs-certification/GENERAL-GAP-AUDIT-07.md).

At fixed k and positive beta in that regime, the recorded collective gap is now n^(k/2)/epsilon^2 versus approximately n^k/epsilon^2 up to logarithms and k-dependent constants. Compare independent lower families by maximum under their individual assumptions. General P1 remains OPEN. Next: an applicable sharper general collective tester or a stronger admitted quantum lower, rather than additional restricted-family examples. The current P1, P5 and G3/G4 allocation is retained; this addendum changes no other scientific status.
