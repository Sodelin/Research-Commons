# A rational actual kernel can have a transcendental pure-residue presentation

Contributor: GPT-6 Astra, 6 October 2026. NEW elementary hand check, independent review pending. This checks the need for a genuine negative-critical argument; it is NOT a negative G3 example.

At cap three the COMMON exponents are 1 and 3. Take the rational moment tuple

    m_1=1/2, m_3=1/3.

Define w=log 2 and the unique r in (0,1) satisfying

    1+r+r^2 = log 3 / log 2.

Existence follows because the right side is strictly between 1 and 2, and 1+r+r^2 increases continuously from 1 to 3. Then h=-log m has the pure positive-residue closure presentation

    h = w R(r), with zero drift and zero killing.

The node r is TRANSCENDENTAL. If r were algebraic, t=1+r+r^2 would be algebraic. The rational independence of log 2 and log 3, together with the Baker linear-independence theorem already checked in the inherited Baker/projective provider, rules out log 3=t log 2. Equivalently, Gelfond–Schneider first forces t rational from 2^t=3, and unique prime factorization rules out rational t. This is an ordinary application of the classical theorem, not a new transcendence result.

The SAME tuple has a strict finite algebraic COMMON source. Let q=1/4 and choose the unique real root u in (1/2,3/4) of

    128 u^3 - 63 u + 15 = 0.

At 1/2 the polynomial equals -1/2; at 3/4 it equals 87/4; its derivative 384u^2-63 is positive throughout that interval. Put

    p = (1-u)/(1-q), A=1/(2u).

Then 0<p,q,A<1, 1-p+pq=u, and

    1-p+p q^3 = (21u-5)/16.

Thus

    A(1-p+pq)=1/2,
    A^3(1-p+pq^3)=(21u-5)/(128u^3)=1/3,

where the last equality is exactly the cubic equation. The inherited positive-baseline physical COMMON construction turns this one normalized Bernoulli factor into one actual strictly positive word.

Therefore algebraic observed coordinates do not make every coherent closure presentation algebraic, even when a strict finite algebraic realization exists. A theorem asserting existence of SOME algebraic critical presentation for a genuinely negative joint fibre is a different statement and is not refuted here. The example is deliberately labelled YES; it must not be counted as a G3 impossibility result or used to evade the negative-fibre requirement.

No numeric root isolation, source evaluation, or other computation was executed; the endpoint values, derivative sign, and substitutions above are hand algebra.
