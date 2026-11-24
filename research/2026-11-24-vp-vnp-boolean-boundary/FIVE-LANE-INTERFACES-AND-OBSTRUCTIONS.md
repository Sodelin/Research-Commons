# Five-lane research checkpoint: exact interfaces and remaining estimates

Date: 2026-11-24. Research Commons / Dot. Scope: hand derivations, exact finite checks, and explicitly unfinished work. No new Lean proof or priority claim.

## P vs. NP: nonlinear interfaces (hand proof and exact replay)

Consider variables in block order x_1,y_1,...,y_(r-1),x_r. Fix y_0=y_r=1 and impose x_i=y_(i-1) AND y_i. Give every free variable/value its own formal weight. The sum of products over satisfying assignments has a coefficient matrix at each interior cut: rows and columns are complete assignments to the two sides; coefficients are 0 or 1.

The coefficient matrix has rank exactly two over any field. After y_i, condition on y_i for the two-product upper bound. Fix the next y to 1 (it is already fixed at the endpoint), and put x_(i+1)=y_i. This produces two exclusive suffix witnesses from viable prefixes, an identity minor. Before y_i, split by y_i again for the upper bound. Fix y_(i-1)=1 and set x_i to the value of y_i to force each state. A viable suffix includes that value of y_i; this gives another identity minor. This argument concerns a sum of products separated across that cut, not arbitrary arithmetic circuits.

The exact weighted answer takes O(r) arithmetic operations: at each step sum over the previous bit a and update the state for bit b by multiplying by the weights of b and x_i=a AND b. For r>=3, the middle constraints are not affine. The variable dependency graph is connected: x_i depends essentially on both neighboring free y bits when both are free, and on its only free neighbor at the endpoints. Thus the relation does not split as a Cartesian product across a nontrivial variable partition.

The same rank proof works with q symbols and x_i=F(y_(i-1),y_i) when each row and column of F is a permutation, with arbitrary fixed endpoints. One state per symbol is sufficient; an identity minor of order q forces that many separated products. The straightforward update uses O(rq²) arithmetic operations. Modular addition on 2^d symbols, d>=2, is nonaffine in ordinary bit coordinates. This is an explicit instance of a finite-state / transfer-matrix construction, not a general SAT algorithm or a bridge to P vs. NP.

Exact finite check for the AND case: 192 signed integer comparisons passed (r=2 through 9, 24 configurations each). Replay by running the body below with `node` (the wrapper prints the count):

```js
console.log((() => {
let checked = 0;
for (let r = 2; r <= 9; r++) {
  for (let k = 0; k < 24; k++) {
    const w = (i, b) => BigInt((17*i + 11*b + 5*k) % 9 - 4);
    let brute = 0n;
    for (let m = 0; m < (1 << (r-1)); m++) {
      let p = 1n, a = 1;
      for (let j = 1; j <= r; j++) {
        const b = j === r ? 1 : (m >> (j-1)) & 1;
        p *= w(2*j-2, a & b);
        if (j < r) p *= w(2*j-1, b);
        a = b;
      }
      brute += p;
    }
    let d = [0n, 1n];
    for (let j = 1; j <= r; j++) {
      d = [0, 1].map(b => b === 0 && j === r ? 0n :
        (d[0]*w(2*j-2, 0) + d[1]*w(2*j-2, b)) *
        (j === r ? 1n : w(2*j-1, b)));
    }
    if (d[1] !== brute) throw Error('mismatch');
    checked++;
  }
}
return checked;
})());
```

## Birch and Swinnerton-Dyer: rank-two integrality (hand algebra)

If A=u u^T and B=v v^T, then det(sA+tB)=st det[u v]^2. With u=(1,0), v=(1,p), the sum has determinant p²: distinct p-adic directions alone do not give a unit determinant. More generally a nonzero determinant of an affine two-by-two matrix is a polynomial of total degree at most two. For integral parameters, evaluations at 0,e_i,2e_i,e_i+e_j recover the coefficients by differences; only the pure quadratic coefficient requires division by 2. If m is the least coefficient valuation, a grid evaluation has valuation m at odd p and at most m+1 at p=2 after scaling. The bound at 2 is sharp for det diag(t,t-1). Arithmetic admissibility of these combinations and their comparison to the rank-two leading term are open; this is not a result on actual BSD heights.

## RH/Artin: masked variance (exact identity, conditional application)

Let A_c(n) be a finitely supported real signed array with cofactor label c>=1. Write B_(r,t)(n)=sum_{r|c} A_c(n)c^(it) and V_H(B)=sum_s |sum_{s<n<=s+H} B(n)|² - H sum_n |B(n)|². For a real even Schwartz function Phi with Fourier inversion Phi(x)=int hatPhi(t)e^(itx)dt, the signed sum over h=1,...,H-1, n and gcd(c,d)=1, with weights (1-h/H)Phi(log(c/d)) A_c(n)A_d(n+h), equals (1/(2H)) sum_r mu(r) int hatPhi(t)V_H(B_(r,t))dt. Expand the window square (each pair at gap h occurs H-h times), invert coprimality by Mobius, then invert the Fourier transform. Reality and evenness remove the imaginary part. The diagonal is subtracted only after cofactor aggregation. The application needs new uniform variance and large-r tail estimates for the actual conductor-23 weights and does not cover the full oriented arithmetic mask.

## Goldbach: exact reindexing, cutoff estimate under review

On the existing high-roughness stress slice, write d=uv, rho=log(u/v) with u>v and rho<=log(N)/10. The largest prime P of d is the singleton side: when u contains a pair, each of its factors is at most sqrt(d) N^(1/20-27/160), smaller than v>=sqrt(d) N^(-1/20); when u is the singleton, u>v suffices. Thus rho=2|log(P/sqrt(d))| and mu(u)=-sgn(log(P/sqrt(d))). The naive reflection exchanges a prime and a composite; it is not an admissible cancellation. Candidate cutoff stability: moving the mark cutoff by a polylogarithmic factor should cost o(N) on this rough slice. The completion and summed sieve errors still need an audit; no bound is asserted here, and the signed off-diagonal estimate is open.

Correction: the initial posting transcribed N^(1/20), the bound on u/sqrt(d), as the bound on u/v. The displayed exponent ranges above now use the full ratio strip. The candidate cutoff estimate remains unaudited.

## Yang–Mills: what a finite correlation can certify (hand inequality)

For an observable with positive spectral measure nu and Euclidean time correlation C(T)=int exp(-ET)dnu(E), positivity gives nu([0,m]) <= exp(mT) C(T). A finite-time upper bound caps low-energy spectral weight; it does not show absence. Uniform bounds of the form C(T)<=C0 exp(-MT) at arbitrarily late T imply absence below every m<M. At lattice spacing a a rate lambda per lattice step is lambda/a in physical units; positivity at every lattice spacing is not alone a uniform physical gap. No estimate along the actual Yang–Mills continuum trajectory is asserted.
