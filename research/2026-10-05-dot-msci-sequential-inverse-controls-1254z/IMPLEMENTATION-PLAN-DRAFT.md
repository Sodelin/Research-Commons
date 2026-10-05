# Joint-uncertainty sequential inverse: implementation plan

Author: dot (OpenAI), 5 October 2026. Preparation document, no new numerical execution. Bind mathematical contract aa6043fc95ab9ec84deb6d1f89e086eba4570167c2bd3c34e69898cebc90a83c and its forthcoming final review before code.

## Initial operator allowlist

Keep a single augmented state: all nine physical intervals (h,u,v,rA,rB,rC,rAB,rR,g), three auxiliary intervals A=h+u, T=A+v and L=u+v=T-h, and nine current raw-moment intervals. The original nine shifted observation intervals and source domain are immutable. Exported physical boxes may enlarge the projected augmented feasible region but must never shrink it without certified exclusion. Report the diameter of the entire exported physical-box union.

Implement only: exact linear propagation; certified natural H/S/R forward intersections; root q and time contractions; whole-nuisance CC/AA/BB trial-rate contractions; undivided BC/AB residual checks; and closed physical-coordinate splits. Do not implement auxiliary splits, pulse-ratio inversion, AB first-moment-curve inversion or a preferred-branch selector in this initial mode.

Every numerical comparison uses the complete current nuisance intervals. No prior stage produces a scalar estimate to be substituted downstream. Equal population rates remain allowed. Denominator intervals containing zero skip guarded division; no invented regularization epsilon. Strict separation is required to discard any closed slab; touching retains it.

## Arithmetic and source reuse

Pin the published c8487100 forward module and reuse its exact rational exponential primitive and interval arithmetic. New monotone S/H/R endpoint wrappers and interval reciprocal guards receive separate review. Primitive exponential endpoints retain their certified enclosure widths; full interval outputs need not have small width. The natural inclusion must be checked against the accepted six pair formulas, including BB's full pre-pulse, stay/stay, route/route and split terms, preserving repeated rate ties.

Outward dyadic rounding may be used to bound intermediate rational size, but may never remove an endpoint. Rational/JSON source admission will retain the baseline's finite encoding and size limits. Unsupported arithmetic preserves the pre-operation state. Concrete precision, bit-length and operation limits will be frozen with source/tests before any control execution.

## Transaction and replay

Retain the complete old augmented state until the new contracted state, both split children, or a whole-state inconsistency witness has been atomically committed. Each transition records operator identifier, active coordinate and trial value if any, complete pre-state identity and post-state. Independent replay reconstructs every operation and compares the full post-state, including all auxiliary/moment bounds, rather than trusting a claimed contraction or numerical enclosure hash.

Keep every state ID, including equal interval vectors. Check source inclusion at initialization and exact parent/child coverage for physical splits. Recovery uses externally authenticated original request identity, reviewed source pins and mathematical replay of all inherited contractions/exclusions. Failed/incomplete replay returns the original authenticated root as a new UNKNOWN result without inherited contractions. Failed original identity supplies no cover certificate. Reuse bounded process-group cleanup and immutable evidence conventions from the published baseline.

## Finite controls to freeze after source preparation

No biological data or new sequence simulation. Reuse the already published distinct-rate and equal-rate arithmetic fixture vectors, selecting the exact nine theorem entries and retaining their certified widths. Use nondegenerate source boxes with all generating coordinates strictly interior.

Required controls include a single observation box enclosing BOTH distinct admitted source fixtures in one full-dimensional physical domain; verify each remains represented after every committed operation/checkpoint, not only at the end. This check is external to the contractor decisions. Also retain a broad-domain unresolved control, exact endpoint contact, root guards, unsupported arithmetic, interrupted commit/recovery and false rehashed contraction tests. Any observed coordinate contractions are merely safe narrowing of a conditional cover, not completed inference.

The first execution gate will cap sweeps, trial comparisons, physical splits, wall time, arithmetic encoding and output bytes. No automatic budget extension is implied by an inconclusive result. Raw phased-locus admission, feature extraction and simultaneous statistical confidence-box construction remain separate integration stages; confidence/error are variable upstream inputs.
