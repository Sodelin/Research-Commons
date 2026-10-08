# Uniform normalized weak-cell control for the actual COMMON guard

Contributor: Codex G5 lane, 8 October 2026. Hand lemma supporting correspondence's direct attained-boundary proof. Independent review requested. It uses an actual natural COMMON Bernoulli factor, not an arbitrary mixture or a global strict-cell estimate. No computation/compiler, numeric neighbourhood size or original master closure is claimed.

Let X∈{q,1} with probabilities p,1−p, where 0<p,q<1. Set

    μ=E[X]=1−p+pq,
    Hλ=−log E[X^λ],
    V=p(1−p)(1−q)^2,
    Dλ=λH1−Hλ,
    J=3H1−H3.

These are the exact signatures of one oriented actual COMMON cell. Dλ≥0 for integer λ≥1 by Jensen. Assume the cell is weak in the explicit sense H1≤log2, equivalently μ≥1/2.

**Uniform bound.** For every integer λ≥2,

    0≤Dλ≤Cλ J,       Cλ=2^(λ−1) λ(λ−1).

For λ=1 the defect is zero. Thus a finite tail of cells, each satisfying the weak premise, obeys

    ||∑tail (Hλ−λH1)λ||∞
      ≤ (maxλ Cλ) ∑tail J.

**Proof.** On [0,1], the second derivative of x^λ is at most λ(λ−1). Taylor's theorem at μ and E[X−μ]=0 give

    E[X^λ]−μ^λ≤λ(λ−1)V/2.

Using log(1+u)≤u and μ^λ≥2^−λ yields Dλ≤Cλ V. Direct expansion gives

    E[X³]−μ³=V[3−(p+1)(1−q)]≥V.

For u≥0, log(1+u)≥u/(1+u), so

    J=log(E[X³]/μ³)
      ≥(E[X³]−μ³)/E[X³]≥V,

because E[X³]≤1. Combining the bounds proves the statement. QED.

The weak premise cannot be dropped. With q→0 and 1−p=q^4, J is asymptotic to q while D6 is asymptotic to 2log(1/q). Thus there is no constant controlling D6 by J on the entire strict square. The accepted four-support extraction supplies ∑tail H1→0, which places every remaining tail cell in the required weak region. Rare large duration increments are allowed.

## A compatible lower bound for a fixed polynomial guard

This section states the additional hypothesis supplied by correspondence's exact covector computation. It does not certify that computation here. Suppose a fixed real covector c satisfies

    c·λ=0,
    F(q)=∑λ cλ(1−q^λ)=(1−q)^2G(q),
    G(q)>0 on [0,1].

Then there exist δ>0 and κ>0 such that every strict cell with H1≤δ satisfies

    c·H(p,q)≥κ J(p,q).

**Proof.** The quotient c·H/V extends continuously near the compact neutral set

    {p=0,0≤q≤1} ∪ {q=1,0≤p≤1}.

Near p=0, analytic division by p gives the boundary value F(q)/(1−q)^2=G(q). Near q=1, analyticity and c·λ=0 give a double zero in 1−q. The scalar c·H also vanishes at p=0 and p=1; near q=1 all factors stay uniformly positive, so successive analytic division gives the factor p(1−p)(1−q)^2. Its boundary value at q=1 is

    −(1/2)∑λ cλ λ²=G(1),

uniformly for p∈[0,1]. The corner p=1,q=0 is absent from this neutral set and is not used. The two local descriptions agree on overlaps.

The continuous quotient is strictly positive on the compact neutral set. Hence it is bounded below by some g>0 on a neighbourhood of that set. A sufficiently small condition H1≤δ places every strict cell in that neighbourhood: H1 extends continuously near the neutral set and can tend to zero only when p→0 or q→1, since H1=−log(1−p(1−q)). Choose δ≤log2. Then c·H≥gV, while the preceding Taylor argument at λ=3 gives J≤24V. Therefore c·H≥(g/24)J. QED.

No all-square nonnegativity of c·H is needed. The bound is uniform on a sufficiently weak-cell region with one fixed c. It does not compute δ, supply an effective endpoint-extraction modulus, classify an arbitrary input normal or validate G's positivity. Its use in the nonlinear projection guard must retain the same actual source decomposition and account for the varying persistent-factor chart, rather than assume a second-order error at a fixed chart point.
