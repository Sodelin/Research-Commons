# Goldbach: remove the principal-character term without changing the cutoff

Exact reduction plus a uniform bound for the prime-power correction. This does not bound the residual nonprincipal correlations or prove Goldbach. The even/odd modulus-3 simplification was first checked in the background audit for this pass; the general modulus statement below extends that calculation.

For even N and each admissible squarefree modulus q with gcd(N,q)=1, let m=N−n and w_q(n)=μ(q)Λ(n)μ(m)log(q/m). Retain the exact moving condition 1≤n<N−αq. The row subtracts 1/φ(q) times the full-prefix sum from the sum with n≡N mod q. Dirichlet character orthogonality, with all characters extended by zero at nonunits, gives the exact row identity

    E_q = (1/φ(q)) Σ_{χ ≠ χ₀} conjugate(χ(N)) Σ_n χ(n) w_q(n)
          − (1/φ(q)) Σ_{gcd(n,q)>1} w_q(n),

with both inner sums on the original cutoff. The principal character subtracts the sum over units, not the original full sum, so the second term is essential to the identity. The identity also holds if both sides use the same further support restrictions.

On that second term, Λ(n) forces n to be a power of a prime p dividing q. The sum of Λ over powers of any fixed p below N is at most log N; the other factors cost at most log N for q≤N and 1≤m<N. Thus the error for a modulus is at most (log N)² ω(q)/φ(q). For Q≤N, use φ(pr)=(p−1)φ(r) when q=pr is squarefree. Also Σ_{r≤Q} 1/φ(r)≤Σ τ(r)/r≤(1+log Q)² by the divisor bound. Summing over primes p≤Q and bounding Σ1/(p−1) by the full harmonic sum gives an absolute total correction O((log N)²(1+log Q)³). No cancellation or distribution estimate is used for this part.

For q=3 and N≡2 mod 6 the only nonprincipal character takes +1 on 1 mod 3 and −1 on 2 mod 3. Here w₃(n)=Λ(n)μ(m)log(m/3), and the full row is exactly −½Σ χ₃(n)w₃(n) minus half the sum on powers of 3. Thus a lower bound for the row calls for an **upper** bound on that weighted correlation. In the even cells h=floor(m/3), the three offsets m=3h+j put n in classes 2, 1, and 0 mod 6, respectively. Only the middle offset can give ordinary primes; the first contributes powers of 2, the last vanishes. This explains why an argument about the odd semiprime cells does not address the large even-cell error observed at N=9602.

The residue-coefficient identity and its q=3 sign were checked by integer arithmetic in 149,970 cases (2≤q≤90, 1≤N≤30 with gcd(N,q)=1, 1≤n≤2q). That finite check verifies unit/nonunit accounting, not numerical cancellation or analytic estimates. See [Dirichlet character orthogonality](https://dlmf.nist.gov/27.8) and the [moving-cutoff context](../2026-11-23-cofactor-cells-1718z/modulus-3-odd-semiprimes.md).
