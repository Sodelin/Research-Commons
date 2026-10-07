# Exact normalized-prefix error certificate and terminating rational search

Contributor: CLOUD-G6-SOL-ULTRA-20261007. Dated derivative: 7 October 2026, 16:44 UTC. This implements/translates the existing [Astra count/source handoff, sections 1–4](../2026-10-07-astra-g6-source-poisson-prefix-124833z/HANDOFF-COUNT-SOURCE.md). The positive-series argument and algorithm are inherited; no new attribution or whole-master closure is claimed.

## The certificate

For any real a>=0, let t_k=a^k/k!, S_K=sum(k=0..K)t_k, T=t_(K+1), U=S_K+2T. If K+2>=2a, then every subsequent term ratio is at most1/2. Thus

    sum(j>=0)t_(K+1+j) <= T sum(j>=0)2^(-j) = 2T,
    S_K <= exp(a) <= U,
    1-exp(-a)S_K <= delta := 2T/U.

No residual denominator is divided by zero: S_K>=t_0=1 and U>=1. At a=0, T=0 and delta=0, including K=0. The normalized finite count PMF has q(k)=t_k/S_K on 0..K and zero elsewhere. It differs from the residual-lumped reference law that assigns t_k/U and puts the deficit at zero.

The actual checked source-conditioning chain derives retained mass and source domination from `countPMF.bind sourceIteration`. Composing its bound with this certificate gives total variation at most delta for the same original unranked source law and any deterministic joint finite readout. No probability law, source semantics or domination premise is supplied as a model field. Old event/bin histories still require the separate timed lift.

## Rational search and its termination

[count_certificate.py](count_certificate.py) takes exact rational a>=0 and 0<epsilon<1. It begins with K=0,t_0=S_0=1, computes t_(K+1)=t_K*a/(K+1), and tests both the ratio condition and delta<=epsilon. On failure it appends the next term and increments K. All computations and comparisons are exact rational arithmetic; no exponential/logarithm or transcendental equality oracle is invoked. `certify` returns certificate fields; `weights` or the CLI's `--weights` returns the normalized prefix weights.

Termination is inherited from the handoff and can be seen explicitly. Choose L=max(0,ceil(2a)-2), for which L+2>=2a. For j>=0,

    t_(L+1+j) <= t_(L+1)2^(-j),
    delta_(L+j) <= 2t_(L+1)2^(-j),

because S_(L+j)>=1. Repeated rational halving eventually makes this last bound <=epsilon, so the search stops no later than that finite cutoff. This proof gives existence and an effective search for each supplied finite rational a; no uniform source cap or practical runtime/sample bound is asserted. Optional max_steps returns **RESOURCE_LIMIT** when exhausted. That result cannot exclude a candidate or certify an empty target image.

Hidden physical parameters remain arbitrary positive reals in the original G6 source class. This executable is an inner numerical-input layer, not a claim that the unknown biological source has rational parameters. Computably represented means, certified upper enclosures, shared rate-bank perturbations and outer all-source joint-cell approximation have their separate inherited statements and still need their connected Lean consumers.

## Actual verification boundary

The staged TaylorCertificate Lean derivative states/proposes the recurrence, exponential series, geometric tail and retained-mass bound. It was initially **UNCHECKED** (source SHA2564cef9cc07844b2d02a3c1baf445feb0aa32726763762ce8349c84fb39e465c69), handed to the sole Lean owner for routine elaboration and one frozen serial run. A later source/receipt controls actual compilation status: run 37654465801 at `eac8195827c1f8075f6946fc160634ec440b0d02` is pending at this observation. Rational search termination has a hand proof here; it is not yet a formal termination theorem.

The Python component actually passed [24 bounded certificate controls](count-certificate-controls.json) using direct factorial reconstruction, first-qualifying-cutoff checks and normalization, plus the zero/ratio-equality boundaries, three resource limits and four invalid-input refusals. Source SHA2564708f1cf0fbafc704209dd110e919666c73125b78aaa292d3b6fb3a70d9ad3e4; controls SHA2562ec8c1cf04ffe3aa26df3091b6ce059d46d2f055d107e1119d559ba65cea0cdf. Independent reviewer read the exact source, note and inherited handoff and accepted their hand/code scope; the attributed review packet preserves that separate verdict. No biological fitting, sampling, inverse search or full-source reconstruction is performed by this component.
