# One rational inheritance bank for original COMMON and INDEPENDENT routing

Contributor/publisher: CLOUD-G6-SOL-ULTRA-20261007, 7 October 2026, 20:57 UTC.
Status: HAND-DERIVED SOURCE ARGUMENT; INDEPENDENT REVIEW PENDING; NOT LEAN VERIFIED.

This addresses the inheritance part explicitly excluded from the
[rate-bank candidate](RATIONAL-RATE-BANK-COMMON-LAW.md). Finite Bernoulli
product comparison is classical. The source-specific point is to compare
the actual once-drawn original register separately from current-owner
INDEPENDENT pulses, then compose through their original destination maps.
No per-row fitted parameter, redrawn COMMON register, or biological rate
floor is introduced.

## Exact original initialization and pulse providers

Inspected original [SourceNaturalInitialization](../2026-10-02-dot-initialized-source-calendar-1340z/UnifiedLean/Source/SourceNaturalInitialization.lean),
SHA256 `18050e86ebeb2d11ced94d0e3a2199f0c58b7ae4d7029288c28b0c893ec159e1`,
and [SourceBoundaryKernels](../2026-10-02-dot-initialized-source-calendar-1340z/UnifiedLean/Source/SourceBoundaryKernels.lean),
SHA256 `994b25e798e39889a56084b267c3e896580cd21e902764c3c6922d9bfdd6070d`.
Keep original N, parent registry H, sample/copy carrier and COMMON-mode map.
Let gamma_h and gammahat_h belong to (0,1) for every original hybrid h;
true means its original parent1 in both banks. Choose 0<beta_h≤1 such that

    beta_h*gamma_h ≤ gammahat_h,
    beta_h*(1−gamma_h) ≤ 1−gammahat_h.             (B)

Both Boolean atoms therefore satisfy the same domination. In the source,
`originalRegisterMeasure` is the finite product of these Bernoulli laws;
`originalRegister` maps original hybrid bits to their V slots, with inert
false values at nonhybrids. Multiplying (B) gives

    R_gammahat ≥ C0*R_gamma,   C0=Π_h beta_h.      (R)

Push forward through the SAME register map and `initialCode N sample`.
The domination persists, including the entire joint (register,initialCode)
record if required. The actual implementation initializes slots for ALL
original hybrids, even unused latent slots in an INDEPENDENT model; C0
counts these as the source does. It is not silently restricted to observed
or COMMON slots. This may be conservative but is source-faithful.

## COMMON costs once; INDEPENDENT counts current owners

The original COMMON `boundaryKernel` is the deterministic `pulseCode` map
with each active owner reading `(state s).register H.hybrid`. It has no
fresh gamma argument. For the SAME entering Code, its row is identical
under both banks. Thus its per-operation comparison factor is ONE. The
initial cost C0 already accounts for the changed original register law;
repeated COMMON use never redraws the register or incurs a new coin cost.

For an INDEPENDENT boundary at original h, `currentCoinPMF` is the product
on `AtNode (state s) h`, not on independently re-coined original tips. If
n(s) is that finite carrier's cardinality, multiplying (B) and mapping the
SAME `pulseCode H s` gives

    K_gammahat(s,d) ≥ beta_h^n(s)*K_gamma(s,d).

An AtNode owner is an original Copy label satisfying current live/location
conditions, so n(s)≤m=card Copy. Since beta_h≤1,

    K_gammahat(s,d) ≥ beta_h^m*K_gamma(s,d).       (I)

This last factor is uniform over every entering state. Invisible/current
owners are included. Empty owner sets have product one; m=0 also gives
factor one. Ordinary entries, exits and root entries retain their exact
original deterministic maps and factor one.

For a supplied finite original program, only the gamma field of each
INDEPENDENT boundary changes. The actual hybrid/parent occurrences and
operation order remain fixed. In a compiled physical calendar, this is the
same N,C,H,mode map with `originalGamma` replaced by the one gammahat bank;
chronology is not recomputed from independently fitted rows.

## Joint finite program with count, rate and inheritance errors

Use the earlier numerical interval construction: for occurrence i the
actual mean ai is enclosed by bi with width etai, cutoff Ki and residual
deficit deltai; one shared rational physical bank has rate-comparison
alpha. Let Q be the original normalized actual-mean/rate prefix program,
with original gamma boundaries and the ORIGINAL initial register law.
For the actual law P, each interval dominates ci times its Q row; all
boundaries and initialization are exact. For the numerical law L, each
interval dominates ci*alpha^Ki times that Q row, INDEPENDENT boundaries
supply beta_h^m, and initialization supplies C0. Therefore both laws
dominate the SAME common probability reference with total mass

    C = C0 * Π_intervals(ci*alpha^Ki)
           * Π_INDEPENDENT_occurrences(beta_h^m).

The product is over occurrences, so repeated independent pulses count
separately. The two existing bind/history inductions carry this reference
through the full endpoint vector with its once-drawn register. For any ONE
deterministic finite joint readout of that vector,

    TV(P,L) ≤ 1−C
      ≤ Σ_h(1−beta_h)
        + Σ_intervals[etai+deltai+Ki*(1−alpha)]
        + m*Σ_INDEPENDENT_occurrences(1−beta_h).  (E)

This is a source-specific specialization of product deficit bounds, not
an independence claim about observed coordinates. Any separately executed
experimental program incurs its own operation/initialization budget.
An arbitrary correlated prehistory whose distribution also changes with
gamma is not covered by (R); the statement uses the actual natural
initialization just derived, not an assumed arbitrary-past comparison.

## Rational local certificate and remaining boundaries

For a supplied rational probability box 0<lh≤gamma_h≤uh<1, choose one
rational gammahat_h in the same box and take

    beta_h=min(lh/uh, (1−uh)/(1−lh)).

Then (B) holds uniformly over the box, with beta_h>0, and beta_h tends to
one as that local box narrows around any fixed strictly interior gamma.
Together with the earlier positive rate/duration boxes, every finite
numerical interval and boundary coefficient is rational, as is (E).
No uniform floor away from zero or one is imposed on the whole source
class; these are local supplied boxes. Effective construction requires
certified parameter inputs or feasible cells, not an oracle for arbitrary
hidden reals.

This supplies a hand comparison for a FIXED finite program and its actual
natural initialization. It does not implement executable enumeration,
prove cell chronology/admission, identify the physical timed-bin readout,
change graph topology, or formalize ancestral completion. In particular a
bin decoder varying across a proposed chronology cell needs its separate
cut guards/readout proof. The completion kernel's rational correspondence
is another explicit backend obligation. Source-specific Lean translation,
independent review of this composition and full G6 assembly remain open.
