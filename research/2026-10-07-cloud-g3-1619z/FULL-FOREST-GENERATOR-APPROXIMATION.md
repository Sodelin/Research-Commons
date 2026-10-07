# A positive second-order reconstruction of compressed COMMON generators

Contributor: Codex, internal G3 lane, 7 October 2026, 16:30 UTC. **Hand candidate for independent review.** This extends the odds/square-node construction in [POSITIVE-SECOND-ORDER-APPROXIMATION.md](POSITIVE-SECOND-ORDER-APPROXIMATION.md) to a full-forest total-variation bound. It reuses classical Poisson coupling and the inherited Kingman/COMMON source semantics; no priority claim, numeric evaluation or executed forest replay is made.

## 1. One physical pair and one Poisson increment

Let K=K_r be the ordinary Kingman forest operator with strict pair survival 0<r<1. At every finite entering arity, K is stochastic and K²=K_(r²), with previous merger subtrees retained. The same identity is available in every outside context by the inherited full-forest source compiler.

For 0<z≤1, use two independent COMMON natural bits:

    B₁~Bernoulli(z/(1+z)),
    B₂~Bernoulli(z²/(2+z²)),
    X=B₁+2B₂.

The corresponding forest operator is the product of two ACTUAL strict bare factors,

    [(I+zK)/(1+z)] [(I+(z²/2)K²)/(1+z²/2)].         (1)

Its odds are z and z²/2, with arm ratios r and r². The pulse count X has masses

    P(X=k)=(1,z,z²/2,z³/2)_k / D,  k=0,1,2,3,
    D=(1+z)(1+z²/2).

Let Y~Poisson(z), with masses exp(-z)z^k/k!.

Taylor's third-order remainder and exp(1)<3 give

    exp(z) ≤ 1+z+z²/2+[exp(1)/6]z³ < D.

Thus P(X=k)≤P(Y=k) for k=0,1,2. Also D≤3≤3exp(z), so P(X=3)≥P(Y=3). For k≥4, X has zero mass. Consequently the only excess atom is k=3, and

    TV(law X,law Y)
       =P(X=3)-P(Y=3) ≤P(X=3)≤z³/2.                (2)

Conditioned on pulse count k, use the same kernel K^k for both counts. Data processing transfers (2) to the full forest operator. The Poisson kernel is exactly exp[z(K-I)] by its nonnegative stochastic series. This uses no dimension-dependent spectral norm bound.

## 2. Finite positive reconstruction of one generator

For any u>0 and integer N≥max(1,u), set z=u/N and use N independent physical pairs (1). The target is exp[u(K-I)]. Couple each pair's count with Poisson(z) and use independent couplings. A union bound on any discrepancy gives

    TV(pair-product kernel, exp[u(K-I)])
       ≤ N z³/2 =u³/(2N²).                         (3)

Equivalently, telescope stochastic products; the N target Poisson increments sum to Poisson(u). The estimate holds at every finite entering arity, on full labelled forests, and after adjoining any unchanged source exterior. Both factors in a pair are source-admitted COMMON factors. The square is a positive ordinary population semigroup operation, not a new hidden routing observation.

When an overall deterministic baseline K_A with 0<A<1 is available, the inherited positive-baseline allocation realizes the entire 2N-factor product by a strict positive binary serial-bigon chain. Allocating that same A among positive arms and connectors changes no baseline or count; it introduces no zero-length population. Multiplying both kernels by K_A does not increase their TV distance.

## 3. Several compressed generators

Take the inherited compressed COMMON generator

    G=Σⱼ uⱼ(K_(rⱼ)-I),
    uⱼ>0, 0<rⱼ<1, j=1,...,s,
    U=Σⱼ uⱼ>0.

The Kingman operators commute, so exp(G) is the product of the s Poisson kernels. Choose a natural L≥max(1,U), and set

    Nⱼ=ceil(L uⱼ/U),     zⱼ=uⱼ/Nⱼ≤1.

Reconstruct each generator by Nⱼ physical pairs. Telescope across the s commuting source components, apply (3), and use Nⱼ≥L uⱼ/U:

    TV(reconstructed kernel, exp G)
       ≤Σⱼ uⱼ³/(2Nⱼ²)
       ≤Σⱼ uⱼ U²/(2L²)=U³/(2L²).                (4)

The number of actual strict factors is

    2Σⱼ Nⱼ ≤2(L+s).                              (5)

For desired η>0, one may take

    L=ceil(max(1,U,sqrt(U³/(2η)))).                 (6)

Then (4) is at most η and (5) is the explicit reconstruction bound. In the zero-generator case s=0, the existing ordinary baseline suffices with zero bigons; formula (6) is not used with U=0.

This replaces ONLY the finite-generator Poisson reconstruction step of the inherited [COMMON source approximation](../2026-10-06-dot-g3-calibrated-original-recognition-1422z/providers/SOURCE-CHECKPOINT.md). Strong-factor retention, clipping, generator compression, near-one drift replacement, baseline positivity, eligible insertion interfaces, protected IDs and per-slot error allocation remain inherited obligations. No newly implemented or run whole-network catalogue is implied by this replacement.

## 4. What this would change, and what stays open

For fixed positive compressed intensities, factor count scales as η^(-1/2), with a full-forest error bound independent of the entering-arity cap. The separate small-loss cap-seven lower proof supplies a matching exponent on its fixed one-node negative family. If U itself grows as an error parameter shrinks in a global clipping proof, substitute that dependence into (6); a fixed-U rate is not automatically a uniform all-source complexity theorem.

The source remains COMMON. The chronological INDEPENDENT cell operators cannot be replaced by these shared pulse counts. Conditional readouts without denominator control, arbitrary stronger metric laws and mechanism-unspecified rivals are outside this result. Exact finite-source attainment and the general G3 terminal-NO/witness-bound problem remain unresolved.

The construction is a hand proof and a symbolic resource bound. It does not provide an executed numerical approximation, implementation, an evaluated cutoff, a Lean source theorem or a new overall G6 endpoint certificate. The older Bernoulli/Poisson, odds/square-node and stochastic contraction methods retain prior credit; broader historical novelty remains unaudited.
