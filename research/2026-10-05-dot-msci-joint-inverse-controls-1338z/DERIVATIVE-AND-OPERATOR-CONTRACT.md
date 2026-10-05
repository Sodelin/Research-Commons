# Coherent nine-residual interval-target contractor: implementation contract

Author: dot (OpenAI), 5 October 2026. Design for independent review before source changes or numerical controls.

## Accepted mathematical target

Bind the accepted Jacobian/interval-target proof0cc4ca6c62066e59be9709bcc10c9188dc9d712f3aae28409d37941b1280249a and its independent review. Retain the physical coordinates x=(h,u,v,rA,rB,rC,rAB,rR,g), positive duration/rate margins, interior g, exact time sums t1=h+u and t0=h+u+v, current-block pulse semantics, tied B/C rates and complete phased homogeneous clock-JC channel. The nine raw features remain AC1,AC2,CC1,BC1,BC2,AB1,AB2,AA1,BB1. Original supplied observations are shifted means and are converted to raw intervals exactly, without replacing them by their centers.

This is one coherent joint operator on all nine equations. It does not introduce isolated CC regroupings, extra pulse-ratio shortcuts or an altered observation model. The existing sequential result and its exact sources are already with the sole publisher and remain frozen.

## Certified derivative source

Reuse the pinned published forward source c8487100113c15804775d4c569a5a71c13b6916736f99242a2e9ed6e621abace, particularly its UN-CLIPPED pair_expressions function and certified rational exponential. Evaluate that same smooth expression graph on interval automatic-differentiation values: one interval value plus nine interval first derivatives. Seed physical coordinate i with its full source interval and the exact i-th unit derivative vector. Form all time sums inside that graph. Every repeated rate, inheritance and time variable remains tied to the same source coordinate.

Use interval sum/product/reciprocal and exponential chain rules with exact rational endpoints and certified outward rounding. Reciprocal requires a denominator interval separated from zero. For E(a)=exp(-a), the derivative enclosure is -E(a) times each derivative of a. No numerical finite difference is a derivative certificate. No derivative is taken through clipping, interval endpoint selection, min/max, point estimates or the old natural-inclusion implementation.

For all x in the entire closed physical box C, the AD value and each gradient component must enclose the true smooth value and derivative. This follows by expression-level inclusion induction and the reviewed scalar primitive. Auxiliary restrictions are NOT used to narrow derivative intermediates: they could exclude parts of a mean-value line segment. The initial contract deliberately bounds the full convex physical box. Existing valid auxiliary/moment constraints may remain in state, but do not silently restrict the Jacobian's domain.

Independent controls will check analytic root derivatives, elementary H/S/R derivative formulas, equal-rate behavior and generic AD algebra. Where practical, symbolic identities or a separately evaluated analytic primitive gradient provide an independent check. Sampled derivatives or finite differences may be additional diagnostics only; they do not prove the whole-box bound.

## Rational preconditioning and joint update

Choose q as the exact rational midpoint of C. Obtain certified Fq containing the nine raw means at q, and J containing every entry of the raw Jacobian over C. A separately evaluated point Jacobian enclosure may be used to form a rational midpoint matrix M. Exact rational Gaussian elimination may propose Y=M inverse, with a verified exact matrix product when it succeeds. This is an ordinary preconditioner, not a proof that the interval Jacobian is regular.

Any fixed rational Y makes the accepted inclusion sound. If inversion is singular, exceeds its rational budget or cannot be validated, use the declared zero-matrix/no-op fallback or retain C as unresolved. Do not diagnose a mathematical singularity from a failed finite computation; strict-source nonsingularity does not ensure a coarse midpoint matrix can be inverted at the chosen precision. No float matrix inverse or uncertified error estimate may be used as a certificate.

With O equal to the complete original or already certified-tightened raw-moment interval box, compute by outward interval arithmetic

    K=q-Y(Fq-O)+(I-YJ)(C-q).

Intersect every physical coordinate of C with its corresponding K interval. The accepted mean-value proof preserves EVERY x in C whose raw feature vector lies in O. An empty coordinate intersection certifies whole-cell inconsistency. Keep interval RHS uncertainty throughout; never evaluate only the center of O. Point-target existence/uniqueness tests are outside this contract. Successful local narrowing is not a global accuracy claim.

The replacement keeps all inherited valid auxiliary/moment constraints and every other state in the global cover. The complete pre-state remains committed until the full replacement and its replayable receipt are ready. On arithmetic refusal, timeout or conditioning failure, do not commit any partially narrowed coordinate vector.

## Mathematical receipt and independent replay

Bind the complete pre-state, original request identity, selected raw-feature order, point q, full physical Jacobian domain, source/precision constants, preconditioner procedure and outcome. Retain enough exact numerical evidence to reconstruct the interval matrix/vector expression and all coordinate intersections. A content hash may identify a large matrix receipt, but is not itself its mathematical validation.

A separate checker recomputes the AD enclosures, rational preconditioner and interval-target expression from the authenticated pre-state and pinned source. It compares the complete post-state or exact exclusion/refusal outcome. It independently reconstructs closed physical splits and preserves all in-flight/untouched states. Reuse the accepted complete-cover recovery semantics: failed replay gives a new UNKNOWN cover containing the authenticated original domain, without inherited contractions; failed original-request identity gives no cover certificate. The old checkpoint history is never rewritten or treated as a new successful execution.

## Finite first source and execution gates

Prepare the source and tiny unit/mock tests first. Before actual controls, freeze all code, arithmetic limits, maximum joint calls/splits, wall/resource caps and exact input fixtures. Reuse the three already admitted arithmetic sources, including the changed-time/root-rate source; no new DNA, simulation, model or population channel is needed.

The bounded controls must include the same broad distinct/equal/two-source domains used by the accepted sequential result, a genuinely uninformative target box, and a resource-refusal/conditioning case. Require BOTH distinct compatible sources to remain in the global augmented-state union at every committed stage and recovery output. Check their physical coordinates, linked times and entire high-precision certified moment enclosures; insufficient enclosure verification remains unresolved.

Separately labelled interior local-box controls may test whether this joint operator can actually contract all nine physical coordinates near a declared source. Local supplied-domain contraction is not evidence that the broad original domain has been localized. Report every individual coordinate width and the diameter of the WHOLE exported physical union. Do not substitute auxiliary time widths, one selected box, a nominal Newton point or the nonsingularity theorem for that global metric.

Tests must cover exact interval target retention, sign-aware matrix products, Y=0, verified rational inversion and failure, endpoint touching, equal rates, complete-source coordinate ties, forged rehashed matrix/contraction witnesses, interrupted commit recovery and untouched global branches. Unsupported arithmetic must retain the pre-state. No unbounded refinement or automatic budget escalation is implied by an unresolved result.

## Prior and unfinished application stages

Krawczyk operators, interval Newton, interval AD, rational linear algebra and set inversion are established methods. The accepted proof credits the classical uncertain-parameter/interval-target literature; this implementation adds an auditable source-specific adapter, not a new generic inversion algorithm. No uniqueness, novelty or external peer-review claim is made.

A reliable application still needs biological/channel/domain admission, complete phased-locus feature extraction, a justified simultaneous confidence box and a sufficiently small whole-source cover for variable requested accuracy/confidence. This numerical component does not verify empirical MCMC convergence or admit separate unphased frog/Raubeson datasets. All rankings remain withheld until the actual application gates are met.
