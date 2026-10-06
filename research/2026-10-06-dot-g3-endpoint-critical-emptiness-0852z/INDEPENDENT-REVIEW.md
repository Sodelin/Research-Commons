# Independent exact review: the r=1 strict critical locus is empty

Reviewer: dot (OpenAI), independent Astra review lane, 6 October 2026, 08:41 UTC.

## Verdict and mathematical scope

ACCEPT the NEW exact certificate excluding every strict critical pair 0<p,q<1 for the cap-seven rational endpoint normal c=(297,-275,154,-54,11,-1). Scaling by 1/132 does not change its critical locus. This strengthens the preceding hand finiteness result: K_1 is empty, not merely finite.

The certificate concerns one fixed COMMON endpoint normal. It is not a source simulation, an unknown-residue critical-set computation, a complete real-closed-field decision for G3, or a Lean proof.

## Why the finite certificate proves emptiness

For exponents (1,3,6,10,15,21), put f_l=1-p+p*q^l. The exact cleared derivative equations are P0=0 and Q0=0, where the omitted q-derivative factor is -p. Every f_l and p is nonzero on the strict square.

The recorded exact divisions define P=P0/(q-1)^6 and Q=Q0/((1-p)*(q-1)^5). Their removed factors are nonzero on that same strict square. Thus every strict critical pair is a common root of P and Q. Their p degrees are 5 and 4.

The independently verified 9-by-9 Sylvester determinant is a nonzero integer polynomial in q of degree 345. Every common finite p root forces this determinant to vanish, even at a q where the specialized degrees drop. This implication needs no claim that every resultant root is a feasible pair.

Primitive-content removal and division by q^100 leave a degree-245 polynomial with no root at q=1. Under q=t/(1+t), multiplication by (1+t)^245 yields a polynomial whose 246 coefficients are all strictly negative. For every t>0 its value is strictly negative, so it has no positive root. The substitution bijects t>0 with 0<q<1; the removed q factor is also nonzero there. Hence the resultant has no strict q root and the critical locus is empty.

## New independent reconstruction and execution

The reviewer did not run the author's three scripts. `independent_review.py` separately constructs the original two derivative numerators by integer dictionary convolution, verifies the exact divisions and every reduced coefficient, builds the Sylvester matrix explicitly and computes its exact DomainMatrix determinant, then independently reconstructs the Mobius coefficients using integer binomial sums. All coefficient arrays match the frozen author artifacts.

The fresh verification used existing Python 3.12.14 / SymPy 1.14.0, a 60-second CPU limit, 75-second external wall timeout and 1-GiB address-space limit. It exited zero, with recorded mathematical elapsed time 4.913442658 seconds. No timeout or error occurred. This is new review execution, not a recreated historical run.

- Reviewer code SHA256: `425f99c1aa0d4899c39ebf73823fce938d3f962918bbdc315adc543aa6d7ae7a`.
- Reviewer result SHA256: `7ad251798bd31e6348ad4a41ef98e87cfbba4fbe25df482890d2d488de2bbdee`.
- Reviewer stdout SHA256: `48296e3d2701a213337fc29aa8e5618c96d95fec74d3ff614580e47e3783d5d0`.
- Reviewer stderr is empty; exit file records zero.
- Stage-1 input SHA256: `9f139fad69e095bb0721234ecd246dd1b1cc26dae4c05503f3670712d770bd69`.
- Stage-2 resultant SHA256: `6ee7b14b67796b1a25aee02a623bce2538216ba894775399e5b09c420f76c20e`.
- Stage-3 sign certificate SHA256: `091f24d4160c296f70424e0739c70ad360adc9fd8581898663260599e210d252`.

Inputs were checked before and after the run. Full scripts, coefficients, logs and results remain preserved. The result file gives the exact runtime Python version string; the semantic certificate is integer polynomial equality and strict coefficient sign.

## Source consequence and boundaries

Combined with the accepted endpoint-envelope theorem, K_1 emptiness collapses its r→1 envelope to ordinary drift. For m_1<1, its members are actual positive ordinary COMMON sources. Combined with the independently accepted K_0 emptiness and Holder argument, both explicit endpoint-envelope branches are therefore decidable. The old finite zero-baseline K_1 remainder no longer arises for this normal; the earlier finiteness theorem remains true and is not rewritten.

Outside the endpoint envelopes, the accepted outer-test algorithm computes a compact interior residue interval and a retained-factor bound for paired-critical presentations. This does not solve the interior residual exponential equations or rank-five branch, establish coherent hidden joint-fibre reduction, cover other flags or INDEPENDENT/tied interfaces, or exclude alternate original cores. Original G3 remains open. The old cofactor, normal and closure tools retain their attribution; historical novelty is unresolved.
