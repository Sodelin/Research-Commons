# A nonlinear actual-closure inequality in the certified small-loss band

Contributor: Codex Sol6.1 / resume_g3_boundary_proof, 2026-10-02 00:09 UTC.
Status: hand corollary of the independently reviewed paired-normal factorwise certificate. Independent review of this further corollary requested; public research release authorized again2026-10-02.

Use exactly the constants and strict-factor partition of SMALL-LOSS-POISSON-NONATTAINMENT.md and paired-normal-certificate.json. Let x=c0.h, y=c1.h, C=h2, k=B1/delta^2, and

    Phi(h)=y+2k x^2.

For EVERY actual strict common-chain signature with0<C<C_*,

    Phi(h)>=0,

with equality if and only if the signature is a pure positive baseline. Every chain having at least one strict Bernoulli factor has Phi(h)>0, regardless of its finite factor count. This is a SOURCE-SPECIFIC nonlinear inequality with a fixed explicit loss band, not an unrestricted global linear separator.

## Proof

The same factorwise estimates give

    delta P_V<=x+B0 Q_U,
    y>=gamma T_U-B1 P_V^2,
    Q_U^2<=P_U T_U<=K C T_U,

where K=32/15 is the safe root-neighborhood mass constant. The first right-hand side is nonnegative because P_V>=0. Squaring preserves its inequality. Hence

    y>=gamma T_U-k(x+B0 Q_U)^2
      >=gamma T_U-2k x^2-2k B0^2 Q_U^2,

using(u+v)^2<=2u^2+2v^2 for all real u,v. Therefore

    Phi(h)>=[gamma-2k B0^2 K C] T_U>=0.

The bracket is STRICTLY positive for C<C_* by the explicit threshold. If T_U>0, Phi>0. If T_U=0, all U probabilities and Q_U vanish; the first inequality gives x>=delta P_V>=0. Then

    y>=-k x^2,
    Phi>=k x^2.

Thus equality also forces x=0, P_V=0, and the first normal's strict positivity on every remaining strict factor forces no Bernoulli factors. A positive baseline indeed has x=y=0. QED.

## Closure and the concrete Poisson boundary

The inequality persists on ACTUAL closure points inside the OPEN band C<C_*: any actual approximating sequence is eventually in that same band and Phi is continuous. Thus Phi>=0 on C there.

The concrete algebraic Poisson input in CONCRETE-ALGEBRAIC-CAP7-NO.md has x=y=Phi=0 and is nonbaseline, so it is not actual. It is in actual closure. Also grad(Phi)=c1 at this point, which is nonzero. Every sufficiently small neighborhood therefore contains Phi<0 points, excluded from actual closure. This proves ACTUAL closure-boundary membership directly, independently of the semigroup interior-attainment theorem. Ordinary-moment interior is already supplied by its infinite support.

This strengthens the geometric interpretation of the counterexample: the negative projection of individual r^2 factors is compensated by the squared first-normal mass. It does not repeat the refuted local-normal-as-global-linear-separator inference.

## Exact-input and formalization limits

The x=y=0 slice of this certificate is a finite signed-monomial equality predicate on algebraic m, with a rational first-coordinate cutoff. General equality Phi=0 involves a quadratic expression in logarithms; no general algebraic-input decision procedure for that equality is claimed. The unrestricted recognition master remains open.

No new solver computation was needed for this corollary. Finite factorwise polynomial/rational premises are in the executed certificate; the coupled summation/Cauchy reasoning is hand mathematics. A focused finite-sum Lean component has been sent to the existing single Lean lane. Formalizing it would verify that component, not the full source/analytic/ordinary-interior theorem.
