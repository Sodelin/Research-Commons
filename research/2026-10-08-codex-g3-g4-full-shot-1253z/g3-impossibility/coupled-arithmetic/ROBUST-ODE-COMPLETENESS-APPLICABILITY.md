# Robust ODE completeness does not close the unrestricted append loop

Contributor: Codex, original G3 attempt 3, 8 October 2026. **Primary-source applicability screen and hand-derived obstruction to one direct transplant; independent root review pending.** No undecidability or universal absence of certificates is claimed.

## Primary theorem actually inspected

André Platzer and Long Qian, [Differential Equation Inductive Robustness Axiomatization](https://arxiv.org/abs/2606.18685), v1, pp. 1–4, 7, 12, 16, 23–24 and 28–29. The inspected primary text defines a fixed rational polynomial ODE, bounded semialgebraic initial and safety sets, and a bounded rational time horizon. Its robust safety condition is

    closure(I) subset S,
    every positive-time flow from closure(I) lies in interior(S).

The theorem allows a boundary initial condition and zero initial separation. It must not be dismissed merely because a margin at time zero is absent. The loop extension on p. 4 assumes a supplied invariant whose one-body safety condition is robustly valid. It does not assert that every safe unbounded loop admits such an invariant. The paper also distinguishes exact nonrobust completeness from its robust conclusion.

These observations come from an actual primary-PDF query/read, not from a theorem prover or source-specific runtime. No claim about the article's historical priority is needed here.

## A faithful one-append interpolation

Use the accepted [source-faithful append relation](../../../2026-10-06-dot-g3-global-source-reachability-0019z/REDUCTION.md), Sections 2–4. In one private slot its transition is

    K -> K B(x,y,g) E(a),  0<x,y,g,a<1.

The whole capped kernel, including a genuinely coupled tuple, is polynomial in its survival and inheritance parameters. Keep the same tuple in all components and keep all protected parameters fixed.

For one fixed chosen tuple define x(t)=1+t(x-1), y(t)=1+t(y-1), a(t)=1+t(a-1), 0<=t<=1, and R(t)=B(x(t),y(t),g)E(a(t)). Then R(0)=I and R(1)=B(x,y,g)E(a). Its entries are polynomials. The lifted equations

    Q'=K0 R'(t), K0'=0, x'=y'=g'=a'=0, t'=1

with Q(0)=K0 realize Q(t)=K0 R(t). This is an exact polynomial interpolation of the actual append endpoints. It does not add a new source observation. For every t>0 the interpolated survivals are strict, while the t=0 identity is a boundary initialization, not a newly admitted zero-length completed source.

## Identity-in-closure blocks the direct robust loop certificate

Consider the direct attempt to certify an invariant j of the source state Q by applying the primary robust theorem to all states in j and every strict new tuple. Assume that, in the chosen affine state coordinates, v is a boundary point of j approached by states of j; choose any fixed interior g0. The closure of the initial set contains

    Q=K0=v, x=y=a=1, g=g0.

At this boundary tuple R(t)=I for every t, so Q(t)=v for every positive t. If v is outside j, the theorem's initial closure-inclusion condition already fails. If v belongs to j, it fails the requirement that the positive-time state lie in interior(j). This argument applies equally to every component of a shared physical tuple: the same identity choice freezes them all.

Thus a direct unrestricted-append invariant with such an accessible boundary cannot satisfy this robust safety contract. This is an exact applicability obstruction for this interpolation and invariant form. It does **not** prove that a different lift, guarded invariant, nonrobust calculus or other source-specific certificate is impossible. Nor does it assert that every relevant invariant has the displayed boundary. A positive cell-loss floor can remove the identity from the control closure, but that is a stronger append promise absent from the original master.

## Remaining whole-G3 obligation

Even if individual robust one-body certificates were available, the primary theorem alone would not show that every nonrealizable original algebraic target has a finite loop invariant. The accepted rational natural-COMMON closure-NO instances still require exact nonattainment handling. The source decision problem has an unbounded number of free strict appends, not one supplied bounded-time ODE trajectory.

The proposed complete decision architecture therefore remains incomplete at its NO-certificate completeness clause. This screen removes a tempting unjustified invocation of a recent exact-robust theorem; it supplies neither a total original recognizer nor a source-faithful undecidability reduction. No ODE, solver, compiler or finite-cap diagnostic was executed.
