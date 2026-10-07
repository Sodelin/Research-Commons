# A candidate quantitative lower bound on COMMON approximation word size

Contributor: Codex, internal G3 lane, 7 October 2026, 16:19 UTC. **Hand proof candidate; independent review pending.** No numeric cutoff, source approximation, QE or Lean job has run. This is a quantitative refinement of an inherited NO family, not a new NO family, general G3 recognizer or all-network G6 lower bound.

## 1. Inherited source and estimates

Use the fresh unexposed untied natural COMMON source at cap seven, with exponents Λ={1,3,6,10,15,21}. Every actual source has log signature

    hλ = a λ + Σᵢ Hλ(pᵢ,qᵢ),
    a>0, 0<pᵢ,qᵢ<1, Hλ(p,q)=-log(1-p+p q^λ).

The finite integer factor count is N. Equal-arm and ordinary factors are absorbed into a, preserving the source's positive baseline. This is the exact source semigroup already defined in the [accepted word-fibre audit](../2026-10-06-dot-g3-word-fibre-method-audit-2110z/WORKING-AUDIT-R3.md).

Fix rational r∈(0,1), and the positive-drift/no-killing case of the [old matched-threshold proof](../2026-10-06-dot-g3-calibrated-original-recognition-1422z/providers/DYADIC-POISSON-SHARP-CAPS.md), Sections 3–5 and 9. Its two rational normal rows c₀,c₁ satisfy cₖ·Λ=0 and cₖ·R(r)=0. There are disjoint closed intervals U about r and V about r², and positive constants γ,δ with nonnegative B₀,B₁, such that, throughout its sufficiently small total-loss regime,

    q∈U:     L₁(p,q)≥γp³,       L₀(p,q)≥-B₀p²;
    q∈V:     L₀(p,q)≥δp,        L₁(p,q)≥-B₁p²;
    q∉U:     L₀(p,q)>0;
    q∉U∪V: L₁(p,q)≥0,

where Lₖ=cₖ·H. Endpoints are assigned consistently; shrink the intervals if necessary. The proof covers both neutral corners and all strict p, not merely a selected approximant. Set K=1/(1-max U).

These estimates, the all-word NO theorem and its qualitative unbounded minimum exact factor count are **inherited**. Classical Cauchy, Hölder and logarithm continuity are also prior methods. The proposed addition is the error-to-count inequality below, including its uniform contrast estimate.

## 2. Uniform contrast outside the primary interval

Let d(p,q)=3H₁(p,q)-H₃(p,q). It is nonnegative, vanishes on the deterministic p=1 boundary, and vanishes at q=1. Under a sufficiently small fixed individual pair-loss ceiling, there are constants D,R>0 such that

    q∈U: d(p,q)≤D p;
    q∉U: d(p,q)≤R L₀(p,q).                         (A)

Here is the required endpoint argument. On U, q stays below 1 and the total first-coordinate loss bounds p by a fixed number below 1/2; Hλ/p extends analytically to p=0, giving the first bound. Outside U on any compact q strip below 1, the same small-loss bound keeps p below 1/2. The old normal construction gives L₀/p a strictly positive lower bound there, because its normal polynomial has no zeros outside U before the q=1 corner; d/p is bounded. This includes q=0, where the positive-drift/no-killing normal has positive constant term.

Near q=1, both d and L₀ are analytically divisible by p(1-p)(1-q)². The quotient for d has a finite continuous extension on 0≤p≤1; the quotient for L₀ is strictly positive on the same compact strip by the inherited double-root normal estimate. The cancellation includes p=0 and p=1, so the ratio remains bounded even when p approaches either endpoint. These two compact arguments give R uniformly, without depending on source word length.

For rational r these constants can in principle be chosen rational by the old exact endpoint/compact bounds. This note provides no evaluated R or D and claims no new extraction execution. Review must challenge (A), especially its uniformity at the p=1,q=1 corner.

## 3. Fixed target and error budget

Choose a target in the old algebraic Poisson family

    h*λ = a*λ+w*Rλ(r),     a*,w*>0,
    C₀=h*₁=a*+w*.

Choose C₀ sufficiently small that the inherited estimates apply to every source with h₁≤2C₀, and, when B₀B₁>0,

    4 B₁ B₀² K C₀ / δ² ≤ γ/2.                       (B)

This is possible within the same old family: choose a*,w* as positive rational multiples of -log b for rational b sufficiently close to 1. All m*λ=exp(-h*λ) are then positive algebraic numbers. If B₀B₁=0, (B) is automatic.

Set

    L=max(1, ||c₀||₁, ||c₁||₁),
    d₀=3h*₁-h*₃=w*[3-R₃(r)]>0,
    H=D+R B₀,
    ξ*=min(C₀,1,d₀/[2(4+R L)]),
    A_T=(2/γ)[L+2 B₁ L²/δ²],
    P*=d₀/(2H),      κ=(P*)³/A_T.

All constants are positive where divided. They depend on the fixed target/normal proof, not N. For an actual source write ξ=||h-h*||∞. Assume ξ≤ξ*.

## 4. Approximate paired-normal argument

Let P=Σ(qᵢ∈U)pᵢ, Q=Σ(qᵢ∈U)pᵢ², T=Σ(qᵢ∈U)pᵢ³ and P_V=Σ(qᵢ∈V)pᵢ. Since the baseline is annihilated and the target's normal projections vanish,

    |Σ L₀|≤Lξ,      |Σ L₁|≤Lξ.

The first inherited estimate therefore yields

    δ P_V ≤ B₀ Q + Lξ.

The second gives

    γ T ≤ Lξ + B₁ P_V²
        ≤ Lξ + (2B₁/δ²)[B₀² Q²+L² ξ²].            (C)

Each primary factor obeys H₁≥p(1-q), so P≤K h₁≤2K C₀. Cauchy gives Q²≤P T≤2K C₀ T. Substitute in (C) and apply (B):

    (γ/2)T ≤ Lξ+(2B₁ L²/δ²)ξ²,
    T ≤ A_T ξ.                                      (D)

Next, positivity of L₀ outside U and its primary negative bound show

    Σ(qᵢ∉U)L₀ ≤ Lξ+B₀Q ≤ Lξ+B₀P.

Sum (A). Ordinary drift contributes zero to d, so

    3h₁-h₃ ≤ D P+R[Lξ+B₀P] = H P+R Lξ.

On the other hand |(3h₁-h₃)-d₀|≤4ξ. The definition of ξ* gives

    P≥[d₀-(4+R L)ξ]/H ≥P*>0.                       (E)

In particular some primary factor exists. Hölder for its n_U≤N nonnegative probabilities gives

    T ≥ P³/n_U² ≥(P*)³/N².

Combine with (D):

    ξ ≥ κ/N²,      N ≥ sqrt(κ/ξ).                   (F)

No fractional multiplicity, common-log normal-form assumption on the approximating source, source-level parameter tie or cap-only bound is used. Its baseline and strict factors are arbitrary admitted real parameters.

## 5. Scope, interpretation and remaining task

For every N≥1, every actual COMMON word with at most N factors has log-signature distance from this fixed target at least min(ξ*,κ/N²). Thus the old nonquantitative compact-image exclusion has a candidate explicit order modulus, conditional on the inherited constants and (A). The bound need not be sharp and no matching upper rate is asserted.

For moment-coordinate error η=||m-m*||∞≤m_min/2, with m_min=minλ m*λ>0, the logarithm mean-value estimate gives ξ≤2η/m_min. Therefore any approximation satisfying 2η/m_min≤ξ* needs

    N ≥ sqrt(κ m_min/(2η)).

The signature can be converted to the supplied capped fresh COMMON forest kernel by the inherited spectral representation. A lower bound for an arbitrary coarsened network observation requires a separate source-faithful embedding excluding every alternative core and source mode; it does not follow simply by quoting this word result. No INDEPENDENT transfer is claimed.

This component would not close original G3: it strengthens a known all-word negative family and gives an approximation obstruction, while leaving input-effective exact witness bounds, arbitrary joint fibre NO completeness and singular retained-factor classification open. Next action is independent review of the uniform contrast estimate and constants, then exact extraction of a concrete rational case if scientifically useful and approved within the serialized resource lane.
