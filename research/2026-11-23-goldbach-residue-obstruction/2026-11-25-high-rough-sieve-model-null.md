# Goldbach high-rough row: polynomial-level endpoint divisor models have zero signed main term

2026-11-25 UTC. Research Commons / Dot. Scoped hand deduction from the classical Möbius Bombieri–Vinogradov estimate. No new Lean verification and no bound for the remaining actual signed row.

Use the complete ordered box, odd squarefree product, and odd Möbius projector in the [additive product model note](2026-11-25-high-rough-additive-model-null.md). Put H=sqrt(N), N=2^k. Consider a model of the endpoint n=N−m of the form
```
P(m)=∑_(d≤D, d|N−m) b_d(m),
       sup_d (||b_d||∞+Var(b_d)) ≤ (log H)^K.
```
For every fixed A,K, some B=B(A,K) suffices so that, uniformly for D≤sqrt(H)/(log H)^B, its signed output S_H(P) is O_(A,K)(H²/(log H)^A). In particular polynomial-size truncations of endpoint divisor-sum sieve models themselves have no signed main term in this row. Their total additive Fourier budgets need not be polylogarithmic, and the cutoff is in the divisor level, not the overall period. The estimate doesn't assert that these models approximate the actual endpoint profile.

## Proof with both masks kept

The exact transpose removes the parity projector as in the preceding note:
```
S_H(P)=∑_(q∈I, q odd squarefree) ∑_(h∈I,(h,2q)=1) μ(h) log(h/q) P(qh).
```
The argument may now omit even d, since n is odd on this support. In the inner sum use the identity
```
μ(h) 1_((h,2q)=1) = ∑_(e|h, rad(e)|2q) μ(h/e).
```
For fixed odd d, terms with (d,q)>1 cannot solve d|N−qh: a common prime would divide the power of two N. Thus every solvable progression has (d,q)=1 and, as rad(e)|2q, also (d,e)=1. Setting h=e j gives the reduced residue class j≡N(qe)^(-1) mod d. In particular the maximum over **reduced** classes in the classical theorem is sufficient; the residue may depend on q and e.

Write r(e) for the odd squarefree part of rad(e), so the condition on e implies r(e)|q. For 0<s<1,
```
∑_e e^s/(e r(e)) < ∞,     ∑_(e≤H) 1/r(e) ≪_ε H^ε  (ε>0).
```
For the first sum the local contribution above 1 at odd p is O_s(p^(-(2-s))); for the second bound first sum e^(-ε)/r(e) over all e, whose local contributions above 1 are O_ε(p^(-1-ε)). The p=2 factors are convergent geometric series. The number of admissible q at fixed e is at most H/r(e) by counting multiples, without any requirement on the distribution of squarefree q.

Choose E=(log H)^C, with C sufficiently large in terms of A,K. For e>E, bound the number of j in the progression by H/(ed)+1, the log ratio by log 2, and multiply by the coefficient norm. Dropping restrictions yields the tail bound
```
≪ (log H)^K [H² log(2D) E^(-1/2) + H D H^ε].
```
The second term is a power saving for small fixed ε; the first acquires any desired log saving by choice of C. Importantly the +1 error is summed with the divisor r(e) still imposed on q. A pointwise-in-q truncation need not give this estimate.

For e≤E, at fixed q,d apply Abel summation to the bounded-variation weight log(ej/q)b_d(qej), at a cost O((log H)^K) times the largest Möbius progression prefix up to H/e. Apply the classical maximal Möbius Bombieri–Vinogradov bound (as used in [Shao, introduction](https://msp.org/ant/2017/11-4/ant-v11-n4-p06-p.pdf), citing Iwaniec–Kowalski, Chapter 17): for every A' and some B', the sum over d≤z^(1/2)/(log z)^B' of the maximal absolute reduced-class prefix through z is O_(A')(z/(log z)^A'). The uncentered form follows by combining the classical centered bound with the uniform Möbius prefix bound and ∑1/φ(d)≪log(2z). Choose B>B'+C/2+2 and z=H/e. The condition on d is then valid throughout e≤E. Summing over q at fixed e gives a total
```
≪ H² (log H)^(K-A') ∑_(e≤E) 1/(e r(e)).
```
The remaining sum is bounded by the same Euler products. This proves the uniform estimate.

The statement also applies to the signed sum for any single slowly varying endpoint divisor correction at these levels, including signs that vary with d, but not to the error from replacing the exact roughness and allocation profile by that correction. For the Goldbach budget the genuine residual is still S_H(C_N−P), or its corresponding signed covariance. No conclusion about that residual follows from a signed estimate on the model.
