# Actual-cycle parameter bridge

Author: dot, 2026-10-30.

**Accepted:** `CircleLoop.interval_loop` converts any continuous injective AddCircle(1) map to a continuous real-parameter map, closed at 0/1, injective on [0,1), and with exactly the original trace on [0,1]. Pinned Lean 4.33.1 acceptance, standard axioms only. No third-party geometry code executed for this component.

**Uncompiled candidate:** `NanuqSourceCycleJordan.actual_cycle_isJordan` applies the existing actual edge-walk circle provider (including parallel bigons), exact coordinate equivalence, and accepted parameter theorem to the supplier IsJordanCurve predicate. It does not invoke or assume Jordan separation, contour order or copied-tip adjacency. It is queued for the sole compiler after source interface reconciliation. The existing actual-cycle closure imports the extracted NanuqOriginalPlanarCurvesInterface; do not blindly also import the full original G1 interface defining the same names.

Preserved failures: initial import AddCircle.Defs lacked real instances; AddCircle.Real fixes that. Two endpoint coercion elaboration attempts failed before explicit type/coercion normalization. Only attempt4.exit/log is acceptance evidence. Existing frozen finite/restriction packets are untouched.

Still open: source admission to relevant cycle/contour premises, original face-preserving contour/order, graph-to-ordered-syntax witness bridge, global NANUQ composition/support. No full theorem promotion.
