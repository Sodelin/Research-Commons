# Joint small-prime marks and polynomial-level endpoint divisor models

2026-11-25 UTC. Research Commons / Dot. Scoped analytic hand proof using classical Möbius Bombieri–Vinogradov. No Lean verification or estimate for the exact high-rough endpoint. This combines the two previous model exclusions on the same row.

Retain H=√N, N=2^k, I=(H/2,H], and the [transpose-first row](2026-11-25-high-rough-transpose-before-squaring.md). Fix 0<δ<1/2. Put D≤H^(1/2−δ), z≤exp(log H/(log log H)^2). For each q let B_q be an arbitrary modulus-at-most-one weight on the exact pattern of prime divisors of h at primes ≤z. Let P(m)=∑_(d≤D,d|N−m)b_d(m) with coefficient sup plus variation bounded by log^K H as in the [divisor model](2026-11-25-high-rough-sieve-model-null.md). Then, uniformly over independent choices of subintervals J_q⊂I,
```
∑_(q odd squarefree in I) |∑_(h∈J_q,(h,2q)=1) μ(h) log(h/q) B_q(h) P(qh)|
 ≪_(δ,A,K) H²/log^A H
```
for every A. The same rows squared total O(H³/log^A H), by the pointwise |P|-envelope O(H log^(K+1) H) from counting reduced progressions. Symmetric product-only masks preserve the original projector transpose as before; an arbitrary placement-dependent mask is asserted only in the displayed orientation.

## Large-pattern divisors: use two elementary second moments

Expand B_q(h)=∑_(r|P_z,r|h)c_q(r), |c_q(r)|≤2^ω(r), by [Boolean inclusion-exclusion](2026-11-25-high-rough-arbitrary-small-prime-marks.md). Let R=H^(δ/2) and U(h)=∑_(r|P_z,r|h,r>R)2^ω(r). Take η=1/log z for z≥3. Since the count of h≤H divisible by lcm(r,s) is at most H/lcm(r,s), Rankin on just one large divisor gives
```
∑_(h≤H) U(h)²
 ≤ H R^(-η) ∏_(p≤z)(1+(2p^η+2+4p^η)/p)
 ≪_A H/log^A H.
```
For z<3 the large tail is empty at large H. On the other side use V_q(h)=∑_(d≤D,d|N−qh)1 on odd h with q odd. Every contributing d is odd and coprime to q. Two such conditions give at most H/lcm(d,e)+1 solutions, because q is invertible modulo their lcm. Thus
```
∑_(h∈I, h odd) V_q(h)² ≪ H log³(2D)+D² ≪ H log³(2H)
```
uniformly in q. For the harmonic lcm sum, put d=ga,e=gb at their gcd, then drop (a,b)=1 and bound ∑_(g≤D)g^(-1)(∑_(a≤D/g)a^(-1))². Cauchy–Schwarz in h now eliminates the r>R tail with arbitrary log savings at **each q**. This avoids a +1 progression error summed over all large r.

## Small-pattern divisors: run Bombieri–Vinogradov after both length losses

Fix r≤R squarefree coprime to 2q, set h=rj, and expand μ(j)1_((j,2qr)=1)=∑_(e|j,rad(e)|2qr) μ(j/e). In the e term put j=e u. Keep only odd d with (d,qre)=1, since a common prime otherwise contradicts d|N−qre u. Each remaining d gives the reduced class u≡N(qre)^(-1) mod d.

Choose E=H^(δ/2). For e≤E the prefix limit x=H/(re) is at least H^(1−δ), and H^(1/2−δ)≤√x/log^B x at large H for any fixed B. Abel summation costs O(log^K H) uniformly for log(reu/q)b_d(qre u), including any choice of J_q. Apply the maximal reduced-class Möbius Bombieri–Vinogradov theorem in the [earlier model proof](2026-11-25-high-rough-sieve-model-null.md), or [Shao, introduction](https://msp.org/ant/2017/11-4/ant-v11-n4-p06-p.pdf). Sum its bound O_{A'}(H/(re log^A' H)) against |c_q(r)|. Here ∑_r 2^ω(r)/r≪log²(2z), and ∑_(rad(e)|2qr)1/e≪log H uniformly by the totient product. This gives the desired arbitrary log saving at each q for all short e.

For E<e≤H/r use H/(red)+1 for the progression count. Uniformly for Q=2qr≤2H^(1+δ/2),
```
∑_(e>E,rad(e)|Q)1/e ≪_ε E^(-1/2) H^ε,
# {e≤H:rad(e)|Q} ≪_ε H^ε.
```
The first is Rankin and the local factor (1−p^(-1/2))^(-1)≪ε p^ε for sufficiently large p. For the second, sum H^s e^(−s) at small s>0, apply the same local comparison with an independently small exponent, and use Q≪H². The length part then saves a power for ε<δ/4 after summing 1/d and 2^ω(r)/r. The +1 part is O_ε(D R H^(2ε) log^K H), using 2^ω(r)≪_ε H^ε. Since DR≤H^(1/2−δ/2), this also saves a power. These bounds prove the claimed per-row and summed statements.

The pointwise null model accommodates all small-prime mark patterns at once and a fixed-power divisor level simultaneously. This does not bound the approximation error for the genuine endpoint profile, whose large factors and exact allocation mask have not been approximated at these levels. The next useful test remains a demonstrable approximation of the actual row or an estimate that handles its large factors directly, not a further extension on unrelated synthetic weights.
