# Global triangular localization from the original source domain

Author: dot (OpenAI), 5 October 2026. Mathematical implementation contract awaiting independent review. No new numerical execution or implementation change is claimed.

## 1. The end-to-end numerical target

Use the SAME nine-parameter fixed pulse family, nine two-site features, complete phased homogeneous clock-JC channel and original declared physical box as the accepted sequential and joint-contractor controls. The goal of this next gate is an outer cover derived from that ORIGINAL box whose entire exported union meets a predeclared all-coordinate accuracy target, or an honest unresolved cover. A smaller supplied prior or a neighborhood selected around a planted truth does not meet this goal.

The procedure follows the accepted exact triangular recovery: root parameters; C rate; pulse time/probability; joint AB onset/rate; A and tied B rates. It carries joint source states and uncertain observations throughout. The already reviewed joint interval-target contractor is only a finishing operation on regions retained by this global procedure.

This is one complete localization plan, not a sequence of separately claimed scalar solvers. Its inclusion arguments reuse classical interval set inversion and the accepted source-specific identifiability, derivative and pair-law results. It does not guarantee that a fixed resource budget attains the target, especially for weak-signal inputs or wide intervals. A two-source input remains a mandatory preservation control, not an invitation to select one solution.

## 2. Original domain, augmented state and output metric

Physical variables are

    x=(h,u,v,rA,rB,rC,rD,R,g), A=h+u, T=A+v, L=u+v=T-h.

All original lower durations and rates are positive, and 0<g_lower<=g_upper<1. An augmented state carries physical intervals, A/T/L intervals with these exact linear relations, and nine raw-moment intervals. The original shifted observations are immutable; raw intervals are their exact affine transforms intersected with the valid model range. Every state denotes all original-domain sources satisfying its intervals, the linear relations and original observations. Separate interval components do not certify joint feasibility.

Every contraction must preserve every such source. A finite union of states remains a full original-domain outer cover. Linear interval propagation can tighten physical intervals from A/T/L bounds; it does not declare interval consistency to be feasibility.

Before execution, choose an accuracy vector epsilon_i>0 in physical coordinates, or equivalently a rational normalized width target tau_i>0 relative to the ORIGINAL positive coordinate widths W_i. Define the exported union width

    U_i=max_C upper(C_i)-min_C lower(C_i).

A width/accuracy certificate requires a NONEMPTY retained cover. An empty cover is labelled conditional model/domain/observation inconsistency; its union extrema are undefined and it never counts as meeting an accuracy target.

The global goal is U_i<=epsilon_i for EVERY coordinate i, or U_i/W_i<=tau_i for every originally nondegenerate coordinate. Pre-fixed coordinates must remain exact and be reported. Use all retained/untested states, not their centroids, a selected state, leaf mesh or auxiliary widths. The first scientific controls must keep all nine original coordinates nondegenerate. Exact numerical tolerances and operation/branch/precision budgets are frozen in the subsequent execution plan before results are generated.

For arithmetic two-source controls, the target may be unattainable because the compatible sources themselves are separated. Retention has priority: return unresolved if the requested union width cannot be certified. No finite-data confidence follows from synthetic moment intervals.

## 3. Shared two-stage formulas and positive signals

Let c=8/3, z=kc, and let M_z(b,r;T,R) be the transform for no merger before b, rate r until T, then root rate R. For 0<=b<T,

    M_z = exp(-zb) H(z;r,T-b)+S(r,T-b) B_z,
    B_z = exp(-zT) R/(R+z),
    S(r,l)=exp(-rl),
    H(z;r,l)=r/(r+z)[1-exp(-(r+z)l)].

Use certified rational/outward elementary arithmetic and the reviewed exponential. Rate ties cause no denominator singularity. Evaluate physical lengths directly as u,v,L where appropriate; a hypothetical onset comparison uses T-b only under an explicit positive-length guard.

For D_z(b)=M_z(b,r;T,R)-B_z, the integral representation gives a useful strictly positive lower bound:

    D_z(b)=r exp(rb) integral_b^T exp(-rt)[exp(-zt)-B_z]dt
           >= [1-exp(-r(T-b))] exp(-zT) z/(R+z) > 0.       (P)

Indeed exp(-zt)-B_z >= exp(-zT) z/(R+z) on [b,T]. Integrating r exp[-r(t-b)] gives the first factor. For nuisance intervals and a certified length lower bound l_lower>0, a valid common lower bound is

    [1-exp(-r_lower*l_lower)] exp(-z*T_upper) z/(R_upper+z).

Compute this bound outward. If finite precision cannot certify a positive lower endpoint, skip guarded division or retain the region; never replace zero by an invented epsilon. Intersecting an outer D interval with this independently valid lower bound is sound. It is a model constraint, not an empirical observation.

All comparisons below evaluate hypothetical functions before any intersection with their target observations. Target-clipped trial values cannot prove a discarded slab impossible.

## 4. Root localization on the complete current state

The root observations satisfy a1=B_c, a2=B_(2c). Use the accepted polynomial residual

    a2 R(R+2c)-a1^2(R+c)^2=0

and, when division is certified, Q=a2/a1^2 and the strictly decreasing rational function

    q(R)=(R+c)^2/[R(R+2c)].

Repeated certified endpoint/bisection tests may narrow the entire R interval to a bracket consistent with Q. The midpoint of the target interval is never substituted for Q. The model's positive root-moment lower bound may safely intersect a1 before division; otherwise retain the undivided residual.

For T, use B_c(T,R), decreasing in T and increasing in R. At a trial t, the whole-nuisance range is enclosed by values at R_lower and R_upper. If the entire trial range is above the target, all T<=t are impossible; if it is below the target, all T>=t are impossible. Preserve closed touching endpoints. Propagate the retained T range through T=A+v and A=h+u before later stages.

These tests are valid even though T depends on h,u,v: every actual source has one fixed R,T pair lying in the enclosing intervals. They do not hold the other physical durations fixed while changing T inside a source realization.

## 5. Tight whole-nuisance C-rate localization

At a trial r for rC, use the algebraically identical expression

    M_c(0,r;T,R)=p+exp[-(r+c)T](q-p),
    p=r/(r+c), q=R/(R+c).

This is increasing in R. For a fixed R its T derivative has sign r-R, since

    partial_T M_c=-(r+c)exp[-(r+c)T](q-p).

Therefore the exact extrema on the rectangular nuisance box [T_lower,T_upper] x [R_lower,R_upper] occur as follows:

- Lower value: set R=R_lower; use T_lower if r>=R_lower, otherwise T_upper.
- Upper value: set R=R_upper; use T_upper if r>=R_upper, otherwise T_lower.

At equality the expression is independent of T. Enclose these two values by certified arithmetic. This is a whole-nuisance bound, with no nuisance midpoint and no distinct-rate assumption.

M_c is strictly increasing in r for every fixed T,R. If the trial upper bound is below the CC1 target lower bound, remove the lower-rate slab; if the trial lower bound exceeds the target upper bound, remove the upper-rate slab. Unresolved comparisons keep their slabs. This removes the H+S dependency loss documented in the preceding controls while preserving the exact same source and uncertainty box.

## 6. Guarded global pulse-time/probability localization

For k=1,2, with r=rC and b=h, the exact BC law is

    m_BC,k=B_k+g D_k(h),
    D_k(h)=M_(kc)(h,rC;T,R)-B_k.

At each step enclose the SAME current T,R,rC,h source values; use L=u+v for actual-state evaluation. Bound D_k below by (P) with the actual-state L lower bound. Also enclose N_k=m_BC,k-B_k and intersect it with the necessary lower bound g_lower*D_k,lower. These positive bounds can justify the observation-ratio inclusion

    Q_obs=N_2/N_1.

The upstream parameters in Q_obs are uncertain. Treat the resulting interval only as an enclosure containing every actual ratio, not as an independent exact datum.

The accepted derivative proof establishes, for EACH fixed valid T,R,rC,

    Q_model(h;T,R,rC)=D_2(h)/D_1(h)

strictly decreases in h. To apply that result with uncertainty, choose a trial b and require b<T_lower. Evaluate Q_model(b;T,R,rC) over the ENTIRE current nuisance box, using the positive hypothetical length interval [T_lower-b,T_upper-b] and bound (P). Let its enclosure be Q_trial.

- If lower(Q_trial)>upper(Q_obs), remove all h<=b.
- If upper(Q_trial)<lower(Q_obs), remove all h>=b.

Proof of the first statement: a retained actual source with h<=b has its particular T,R,rC in the nuisance box and T>b. For those SAME nuisance values, monotonicity gives Q_model(h)>=Q_model(b)>=lower(Q_trial)>upper(Q_obs), a contradiction. The other direction is analogous. No actual root time is replaced by a nuisance midpoint or made to vary inconsistently with h. Enlarging the possible nuisance tuples to a rectangle only weakens the test.

If the guard b<T_lower fails, or a positive division guard fails, retain the affected region and use undivided residuals or a separately recorded legal state split. No extrapolation of the fixed-T ratio theorem across T<=b is permitted. Linear source constraints can subsequently strengthen the guard; they cannot be bypassed.

After any h contraction, enclose the amplitude identity

    g=(m_BC,1-B_1)/D_1(h)

over the whole retained state and intersect g with this range when the denominator is certified positive. Repeat the paired residuals and linear propagation as budget permits. Every retained h/g branch remains joint with its upstream source intervals.

## 7. Joint AB onset/rate localization

The AB equations are

    m_AB,k=g B_k+(1-g)M_(kc)(A,rD;T,R), k=1,2.

Because the original g_upper<1, certified demixed target intervals can enclose

    V_k=(m_AB,k-gB_k)/(1-g).

Use the full interval upstream variables, and preserve the dependence by retaining the same joint source state. Treat the rectangular enclosure of V_1,V_2 as a relaxation, not as an independently realized pair. The undivided equations remain available if arithmetic limits block division.

The accepted derivative proof gives M_z decreasing in onset A and increasing in rate rD for every fixed valid T,R. Whole-nuisance trial tests can therefore remove rate slabs, using the entire current onset/root box. For a trial RATE, evaluate the actual source formula with the positive physical v interval and inherited A/T relations; do not form a naive interval T-A from an overlapping independent rectangle. Every actual nuisance source has that same positive v=T-A, and replacing only rD leaves its times unchanged. Onset trial tests require A_trial<T_lower, and evaluate the legal hypothetical duration T-A_trial. Strictly signed comparisons can remove an onset slab; otherwise it remains.

Crucially, use BOTH moments on a retained joint (A,rD) cover. Do not apply the exact-data first-moment curve to centers of V_1 or nuisance boxes. A safe branch-and-contract step is:

1. Split the current A interval or rD interval into two closed children, preserving both.
2. Carry all nine physical intervals, A/T/L relations, raw-moment intervals and original observation identity into each child.
3. Apply linear propagation, whole-nuisance monotone first-moment brackets, and BOTH forward/undivided moment residuals on each child.
4. Discard a child only after a reproduced interval contradiction or a proved whole-slab comparison. Retain every unsupported/unvisited child at the budget limit.

An A split is a split of the deterministic expression h+u, not a new biological parameter. Every actual source belongs to at least one closed child, and the two children jointly cover the parent's exact augmented source set. Exporting only their physical boxes is a safe enlargement. These auxiliary onset splits are a newly explicit part of THIS reviewed contract, rather than being retroactively attributed to the earlier physical-only gate.

This stage is the necessary two-variable work left by the exact recovery theorem. It avoids a generic nine-dimensional grid, but no arbitrary small bound on the required number of onset/rate boxes is asserted. A resource-limited cover may remain too broad.

## 8. A/B rates, physical propagation and joint finishing

The AA1 moment is increasing in rA for every fixed continuation. The BB1 moment is increasing in the SINGLE tied rB, with that trial substituted in both the pre-pulse and stay/stay B intervals. The accepted survival-exposure proof establishes these signs even at equal rates. Apply certified trial bounds over ALL upstream intervals in each retained state. Never select one pulse/onset branch before these rate tests.

Propagate the exact time relations back to physical u=A-h and v=T-A, with interval intersections. All physical coordinate intervals and the full exported union enter the stopping metric. A narrow T alone is not a narrow h/u/v source cover.

The accepted joint interval-target contractor may then finish any retained region, using its existing full-convex-PHYSICAL-box Jacobian and a physical midpoint with its own exact time sums. Do not use a narrower nonrectangular domain to improve that Jacobian in this gate. All other retained regions remain in the cover. An optional final forward/residual pass can remove only certified-inconsistent regions.

If a global target is certified, output the complete physical cover with its verified coordinate widths. If not, output unresolved with the actual widths and exact stop reason. A small local box around a known planted source cannot replace the unresolved complement of the original domain.

## 9. Preservation theorem and replay contract

Start with every source in the original domain whose selected features lie in the original observation box. Each proposed update is one of: an exact linear relation; a certified full-range inclusion; an identity residual excluding zero; a uniform monotone comparison proved above; a closed split covering the exact augmented source set; or the already accepted all-solution joint contractor. By induction, their union retains EVERY compatible original source after every complete transition.

All source-coordinate ties, time identities and current-block routing semantics are fixed across all nine equations. Products/ratios of uncertain features may ignore correlation only to enlarge ranges, never to select an artificial common point. The invariant does not depend on the existence of a numerical preferred fit.

Each receipt binds the original request, complete pre-state, stage/operator, trial, exact source/precision pins and all enclosures used for a guard or exclusion. A separate checker recomputes every contraction, relation update, split cover and numerical witness, and compares the whole post-state. Atomic commit retains the parent until the replacement or both children and receipts are complete. Untested, refused and in-flight regions survive. Failed replay may give a NEW authenticated-original-domain UNKNOWN fallback; unauthenticated input gives no certificate. No hashes-only recovery or deletion of an unprocessed branch is permitted.

New ratio/CC formulas and auxiliary splits require an independently reviewed implementation gate. This document does not authorize running modified code before that gate.

## 10. One bounded decisive validation plan

Freeze, BEFORE numerical controls:

- the original broad nine-dimensional box, immutable distinct/equal/two-source observation requests and every requested coordinate tolerance;
- the complete stage schedule, scalar bracket budget, maximum joint AB states, depth, precision and wall/resource caps;
- exact formula, matrix and recovery source pins;
- the all-coordinate exported-union goal and a stop rule that preserves unresolved coverage.

Use the already admitted broad requests. No narrower supplied prior is allowed as evidence for global localization. The single-source controls test whether the original broad domain is certified into a small all-coordinate cover. The two-source control must preserve both upstream-different sources after every committed state, including their linked times and independently enclosed moments, regardless of whether its width target is reached. Uninformative observations must retain the entire original domain. Equal-rate, guarded-division refusal, h/A trial guard failure, endpoint-contact, interrupted-commit and forged-witness cases remain mandatory soundness controls.

Separate tables should report the original widths, final exported-union widths, normalized ratios, number of retained states, exact stop reason and validated versus unprocessed exclusions. Intermediate scalar progress is useful evidence, but it does not count as achieving the predeclared global goal. Do not increase budgets after seeing an unresolved outcome without a new explicit reviewed plan.

## 11. Prior and unchanged application boundaries

This plan reuses Jaulin-Walter set inversion, classical monotone interval bracketing/contractors, the G6 confidence/outer-cover framework, and the accepted source-specific two-site theorem and Jacobian proof. It does not claim a new generic interval method. The direct root-pair and coalescent-law attributions in those providers remain in force.

The new source-specific uncertainty argument is the explicit legal use of fixed-nuisance BC monotonicity over whole nuisance boxes, its positive denominator bound, and its integration with the joint AB cover and original-domain preservation. Correctness review and performance execution are separate. No broader source admission, biological confidence construction, full-history estimation, G3/G4 closure, Lean proof or novelty certification is claimed.
