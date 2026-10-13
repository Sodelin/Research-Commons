# INDEPENDENT local gate: no second-order fair curvature, and an exact cap-three collision

Contributors: Codex general-algebra lane and Codex lead G4 researcher,
13 October 2026. **Hand-derived scoped obstruction; independent review
pending.** The root lane supplied the exact pair/triple collision and its
fixed-target padding construction. This lane supplied its explicit cap-four
separation and the full-kernel second-jet derivation below. The generator
identity, source grammar and observation adapters are inherited. No
historical novelty, Lean verification or G4 closure is claimed.

## Scope and inherited open gate

Write `E_a=exp(aQ)` for ordinary pair-rate-one forest evolution and
`B(t,p)` for one equal-arm INDEPENDENT cell of arm duration `t>0`, where
`p=g(1-g)` and `0<p<=1/4`. Every factor acts on current opaque roots and
retains their complete labelled genealogies. A word uses one physical
parameter tuple at every cap. All complete private forest rows below use
the inherited legal private interface or a proved faithful observer; this
note supplies no new original-source decoder.

The accepted [INDEPENDENT finite-persistence argument](../../chronology/continuation-1837z/INDEPENDENT-FINITE-PERSISTENCE.md)
reduces a hypothetical increasing-cap exact-rival sequence to a finite
target body plus arbitrarily many weak cells. Their effective ordinary
durations are `(1-2p)t`, but their total physical-clock surplus
`2 sum p t` need not vanish. The accepted BOTH local proof uses COMMON
to remove that reservoir. The present result identifies a precise failure
of replacing that clock input by second-order curvature. It neither
constructs exact rivals at every finite prefix nor excludes a higher-order
or full-chronology solution.

## 1. At fairness, the entire second jet is an ordinary clock change

For every finite cap, the inherited full-forest generator identity at
equal arms and fairness is

    Q B(t,1/4) = 2 B_t(t,1/4) - B_p(t,1/4)/4.       (1)

It is an identity in every complete labelled forest coordinate, not just
on no-merger diagonals. The finite source polynomial extends analytically
to `t=0`; boundary parameters are used only to calculate derivatives.
At the zero-duration boundary,

    B(0,p)=I,    B_t(0,p)=(1-2p)Q,    B_pt(0,p)=-2Q.

Indeed a specified entering pair can merge to first order exactly when
its members choose the same arm, of probability `1-2p`. Differentiating
(1) in `t` and setting `t=0` therefore gives

    Q^2/2 = 2 B_tt(0,1/4) + Q/2,
    B_tt(0,1/4) = (Q^2-Q)/4.                         (2)

The fair pair survival and its exact matched ordinary clock are

    d2(t,1/4)=(1+exp(-t))/2,
    tau(t)=-log d2=t/2-t^2/8+O(t^4).

Equation (2) yields, at every fixed complete cap `m`,

    B(t,1/4)
      = I+(t/2)Q+(t^2/8)(Q^2-Q)+O_m(t^3)
      = E_(tau(t))+O_m(t^3).                         (3)

Thus no second-order observable of the full finite forest kernel can
give a nonzero transverse coefficient along all admitted weak-cell
directions after the exact pair clock is removed: the fair direction is
identically zero through that order. Multiplication by any fixed admitted
prefix and suffix preserves (3), so adding chronological coordinates at
the same order does not remove this degeneracy. This assertion concerns
second-order coercivity only; it is not a no-go theorem for higher jets.

For clarity, the inherited effective duration `t/2` differs from the exact
pair clock by `-t^2/8+O(t^4)`. The second-order discrepancy relative to
`E_(t/2)` is therefore a clock retuning, not a new non-clock invariant.

One can realize the residual reservoir by approximation without any
boundary factor. Fix an ordinary target `E_H`, take `0<c<2H`, and set
`t_N=c/N`. Use `N` fair cells, with `N+1` strictly positive ordinary
gaps whose total is `H-N tau(t_N)>0` for all sufficiently large `N`.
These words have exactly the target pair row. Stochastic telescoping of
(3) gives convergence to `E_H` at every fixed full cap with error
`O_m(N t_N^3)=O_m(N^-2)`, while their physical exposure tends to
`H+c/2`. This is only an approximation sequence. In particular it does
not satisfy the exact-prefix rival obligation.

## 2. Exact complete cap-three collision at every fixed ordinary target

Let `x=exp(-t)`. A single equal-arm cell has no-merger probabilities

    d2=(1-2p)x+2p,
    d3=(1-3p)x^3+3p x,
    d4=(1-4p+2p^2)x^6+4p(1-2p)x^3+6p^2 x^2.

The exact pair/triple defect factors as

    d3-d2^3
      = p(1-x)^2 [3x(1-4p)-8p^2(1-x)].             (4)

It is negative at fairness and positive for sufficiently small positive
`p` at any fixed `0<x<1`. Its interior zero has the convenient
parametrization

    0<p<1/4,    A=3-12p+8p^2,
    x=8p^2/A,   d2=2p(3-8p)/A.                     (5)

Here `A>0`, `0<x<1` and `0<d2<1`; all actual parameters are strict.
For example `A-8p^2=3(1-4p)>0` and
`A-2p(3-8p)=3(1-2p)(1-4p)>0`. As `p` increases to `1/4`, both `x`
and `d2` tend to one. Let `u=-log d2`. For any fixed `H>0`, choose
an interior `p` sufficiently near `1/4` that `0<u<H`, then choose
strictly positive `a,b` with `a+b=H-u`. The one fixed rival

    W=E_a B(-log x,p) E_b

satisfies `D2(W)=exp(-H)` and, by (4), `D3(W)=exp(-3H)`.

These two equalities determine the entire complete forest response
through cap three. For any exchangeable, sampling-consistent such kernel,
if `P2` is the probability of exactly two output roots on three inputs,
restriction to a specified pair gives

    D2=D3+(2/3)P2,    P2=(3/2)(D2-D3).

The three labelled two-root forests each have probability `P2/3`; the
three rooted binary three-leaf trees each have probability
`(1-D3-P2)/3`. The one- and two-input rows are already fixed by `D2`.
Opaque entering subtrees are preserved by grafting, so the same statement
holds for the complete kernel interface, not only a root-count projection.

This rival is already separated by a legal cap-four no-merger row. Direct
substitution of (5) gives the exact identity

    d4-d2^6
      = -1728 p^6(4p-1)^4(32p^2-32p+9)/A^6 < 0.     (6)

The sign is strict because `32p^2-32p+9=32(p-1/2)^2+1>0`.
Multiplying by the positive padding factor `exp(-6(a+b))` therefore
gives `D4(W)<exp(-6H)`. No limiting or infinite source realizes this
collision; every selected `p,a,b,t` is strictly admitted and finite.

This proves only that complete cap three cannot force an ordinary target
in the private INDEPENDENT class. It is not a negative solution of G4:
the same constructed rival fails the explicit cap-four observation.

## 3. What remains, and what was reused

The master obligation remains a finite legal certificate for each fixed
target against every finite rival of unknown size, or exact inequivalent
rivals to one fixed target after every finite legal prefix. Neither is
proved here. The finite-persistent I-only gate now specifically requires
control beyond the fair second jet, including arbitrary-count weak
reservoirs, possible target-body retuning and full chronology. Failure of
quadratic coercivity and the cap-three collision do not decide whether
that stronger control exists.

The prior [all-fair higher-jet local theorem](../../../2026-10-10-dot-g4-all-fair-local-forcing-1220z/ALL-FAIR-HIGHER-JET-LOCAL-EXCLUSION.md)
was checked before writing this note. It uses an isolated-fibre power
bound and annihilation of finitely many target jets under a **fixed
COMMON clock**. Its positive weak-cone argument cannot simply be
applied after deleting that clock equality. Its theorem and the present
second-order diagnostic have different hypotheses; the theorem is
inherited, not reopened.

Provider for (1): dot's [full-forest source-generator identity](../../../2026-10-04-dot-g3-recovered-local-components-1812z/critical/source-generator/INDEPENDENT-BIGON-GENERATOR-IDENTITY.md),
whose Bernstein/coalescent duality prior attribution remains in that
packet. Its all-cap proof is the justification for (1), rather than a
diagonal extrapolation. The accepted mixed-body differential result is
[preserved separately](../MIXED-TARGET-DIFFERENTIAL-LOCAL-CANDIDATE.md).

**Verification separation.** Equations (1)--(6) above are hand arguments
or explicit polynomial identities. SymPy exact rational simplification
independently checked the substitution in (5)--(6), with a small retained
checker beside this note; this is a transcription control, not proof of
an arbitrary-cap claim. No Lean or Rust verification was performed.

**Next action:** seek a higher-order source-positive functional or an
exact full-chronology return construction for the I-only weak reservoir.
Any successful argument must control unbounded extra-cell count and
one shared tuple; neither a finite diagonal screen nor approximation
establishes that conclusion.
