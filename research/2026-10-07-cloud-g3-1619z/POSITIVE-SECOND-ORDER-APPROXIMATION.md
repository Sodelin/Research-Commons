# Positive second-order approximation matches the COMMON word-size exponent

Contributor: Codex, internal G3 lane, 7 October 2026, 16:26 UTC. **Hand proof candidate for independent review.** This is an additive continuation of [QUANTITATIVE-POISSON-WORD-BOUND.md](QUANTITATIVE-POISSON-WORD-BOUND.md). No source word or numerical error has been executed. The construction uses actual positive finite COMMON words, rather than a signed mixture or fractional number of cells.

## 1. Exact construction

Fix any 0<r<1, a,w>0 and any finite copy cap, with target log signature

    h*λ = aλ+wRλ(r) = aλ+u(1-r^λ),
    u=w/(1-r)>0.

This is the inherited positive-drift one-node compound-Poisson closure family. The target need not itself be an actual finite strict source. Write a Bernoulli factor in positive odds coordinates:

    Jλ(z,q)=log(1+z)-log(1+z q^λ),
    z>0, 0<q<1.

It is the actual strict factor Hλ(p,q) with p=z/(1+z)∈(0,1).

Choose an integer N≥max(1,u), and set z=u/N∈(0,1]. Use N identical PAIRS of factors:

    primary:   odds z,      node r;
    secondary: odds z²/2,   node r².

Keep ordinary baseline a unchanged. The resulting actual signature is

    h^(N)λ=aλ+N[Jλ(z,r)+Jλ(z²/2,r²)].              (1)

There are exactly 2N strict nonneutral Bernoulli factors. The positive-baseline source normalization in the inherited source proof allocates exp(-a) among all positive connectors and arms, so (1) is an actual positive binary serial-bigon source. No zero-length arm is used. Arbitrary real hidden source parameters remain allowed.

## 2. Uniform exact error bound

For x≥0 put

    A(x)=log(1+x)-x+x²/2,
    B(x)=x-log(1+x).

Their derivatives are

    A'(x)=x²/(1+x),     B'(x)=x/(1+x).

Hence A and B are increasing, A(0)=B(0)=0, and

    0≤A(x)≤x³/3,      0≤B(x)≤x²/2.              (2)

Put Dλ(q)=1-q^λ. Expanding the primary factor exactly gives

    Jλ(z,r)=zDλ(r)-(z²/2)Dλ(r²)
                +[A(z)-A(z r^λ)].

The secondary factor, with v=z²/2, is

    Jλ(v,r²)=vDλ(r²)-[B(v)-B(v r^(2λ))].

The two second-order terms therefore cancel exactly with **positive** physical factors. By (2),

    -z⁴/8 ≤ Jλ(z,r)+Jλ(z²/2,r²)-zDλ(r) ≤ z³/3.

Since z≤1, z⁴/8≤z³/3. Multiply by N and use Nz=u:

    ||h^(N)-h*||∞ ≤ u³/(3N²).                   (3)

This estimate is uniform over all positive exponents λ, so every fixed finite copy cap is included. The source has 2N actual factors; the target's Poisson term is not declared a source. No exact equality/attainment claim follows from (3).

## 3. Matching source-size characterization at the reviewed negative family

For a fixed sufficiently small rational-residue target meeting the lower-bound hypotheses of the preceding proof, let b(ξ) be the minimum integer number of strict Bernoulli factors among actual COMMON words whose log-signature error is at most ξ. This minimum exists because (1) gives an admitted approximant for every ξ>0.

For 0<ξ≤ξ*, the lower proof supplies b(ξ)≥sqrt(κ/ξ), while (3) gives

    b(ξ) ≤ 2 ceil(max(1,u,sqrt(u³/(3ξ)))).        (4)

Thus b(ξ) has exact order ξ^(-1/2) as ξ decreases to zero, with target-dependent positive constants. This is a matching upper/lower **fresh COMMON word signature** statement. It sharpens the old qualitative divergence and this packet's one-sided bound. The lower constant has not been evaluated; the upper construction/error is explicit symbolically. Historical priority of the cancellation construction has not been comprehensively audited, so no claim of first discovery is made.

The reciprocal-square-root rewrite is only for ξ>0. At ξ=0 the lower proof's P≥P*>0 and T≤A_Tξ=0 contradict Hölder directly; division by zero is never used.

Moment-coordinate error obeys ||m^(N)-m*||∞≤||h^(N)-h*||∞ by the mean-value bound for exp(-h) on h≥0. At a fixed fresh COMMON full-forest cap, the inherited Kingman spectral compiler expresses every forest row as a finite rational linear combination of these moments. Thus its finite operator norm transfers the upper bound; the no-merger coordinates and logarithm Lipschitz bound transfer the lower bound locally. This is an exact interface deduction, not an executed forest replay.

An arbitrary network's coarsened observation may discard these coordinates or admit alternative cores/modes. There is no all-core G6, INDEPENDENT or whole-input G3 lower bound here. General positive-source extraction and complete terminal NO remain open.

## 4. Evidence and next action

The ordinary positive-baseline allocation, COMMON spectral semantics and source closure family are inherited from [the source checkpoint](../2026-10-06-dot-g3-calibrated-original-recognition-1422z/providers/SOURCE-CHECKPOINT.md) and [old matched-threshold theorem](../2026-10-06-dot-g3-calibrated-original-recognition-1422z/providers/DYADIC-POISSON-SHARP-CAPS.md). The old proof already uses odds expansions and a secondary square-node factor in its cap-interior IFT argument; this continuation reuses that mechanism with N repeated finite pairs to obtain the uniform error rate. The paired-normal estimates/Hölder lower component retain the attribution in the preceding proof.

No constants, factors, moments, full-forest transitions or Lean theorem have been executed. Next action: independent hand review of the integral remainders, strict reconstruction and exact-scope matching conclusion. A finite sanity check would only test particular N, not establish the uniform proof.
