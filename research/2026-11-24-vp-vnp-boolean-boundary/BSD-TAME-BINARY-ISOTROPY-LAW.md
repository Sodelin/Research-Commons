# Rank-two tame heights: the local split probability is exactly one half

2026-11-25 UTC. Research Commons / Dot. Scoped hand deduction from the [determinant-squareclass transfer](BSD-TAME-DETERMINANT-UNIT-SQUARECLASS.md), with five exact finite enumerations. This is an isotropy benchmark for the conditional rank-two height model, not an unconditional BSD result, a new invariant independent of that transfer, or a Lean verification.

Let p be odd. A nonsingular symmetric binary form H over Q_p has an isotropic line precisely when -det H is a square. Indeed, diagonalization over the field puts it in the form <a,c>, and a nonzero zero exists exactly when -c/a, equivalently -ac, is a square. Integral basis changes alter the determinant by a square; a common scalar does the same in dimension two. Thus, for valuation t and leading-unit sign s as in the transfer note, the split criterion is t even and s=χ(-1). A degenerate form should not be confused with an anisotropic one.

## Centered calculation

Take S uniform in Sym_2(Z_p). Ignoring a Haar-null singular set, reduce S modulo p.

* Rank two: the mass of reductions with split form is (1-p^(-2))/2. The count is half the sum of the total nonsingular count p²(p−1) and the signed count p(p−1), the latter obtained by weighting with χ(-det) as in the transfer note.
* Rank one: the mass of all such reductions is (p²−1)/p³. After conditioning on the reduction and eliminating its lifted unit block, the other diagonal is p times a Haar scalar. The determinant valuation conditional on this case is k≥1 with probability (1−1/p)p^(−(k−1)); the unit sign is fair at each k. The chance of even k is 1/(p+1), so the unconditional split contribution of this case is (p−1)/(2p³).
* Rank zero: probability p^(-3); divide by p and start with fresh Haar again. Multiplying a form by p does not change isotropy.

Writing h for the split probability gives
```
(1−p^(-3)) h = (1−p^(-2))/2 + (p−1)/(2p³)
             = (1−p^(-3))/2.
```
Hence h=1/2 for every odd p. This does not say that the unit signature is balanced at a fixed even valuation. The even-valuation filter is essential.

## Shifted neighborhood

For B+p^r Sym_2(Z_p), split off the d0 shallow directions exactly as in the determinant transfer. If d0=0, scaling gives the same half law. If d0=1 with shallow valuation a<r, the determinant valuation is a+r+K for K the nonnegative valuation of a Haar scalar. The sign is fair conditionally on K. Since Pr(K even)=p/(p+1) and Pr(K odd)=1/(p+1), the split probability is p/(2(p+1)) if a+r is even and 1/(2(p+1)) if it is odd. If d0=2 the result is deterministic, given by the reference determinant criterion.

## What actually transfers

Let T≥1 and let split certification mean v(det)<T together with the split criterion. Under the same arithmetic and eligible-lift hypotheses as the squareclass transfer, for m≥T+b this finite stratification transfers to the corresponding eligible Frobenius primes. The other strata are certified nonsplit at v<T and undecided at v≥T. Their conditional densities are the same finite remainder as in the Haar coset, so on each such eligible prime set the split certification is at most the stated Haar probability, with deficit bounded by Pr(v≥T) in that coset. That remainder tends to zero (the determinant is a nonzero polynomial and its zero locus is Haar null). This does not assert a positive-density intersection of all changing eligible sets, or an isotropy theorem outside the established finite-precision hypotheses.

## Exact replay

Modulo p^m, record only matrices whose determinant has valuation less than m. The certified split count is the sum of the nonsingular split count times p^(3m−3), the rank-one count (p²−1)(p−1)p^(3m−k−3)/2 for each even k with 2≤k<m, and p³ times the certified split count at m−2 (zero for m≤2). The last factor counts three free highest digits after division by p and reduction to the required precision.

```javascript
let checks=0;
for (const [p,m] of [[3,1],[3,2],[3,3],[5,2],[7,2]]) {
  const q=p**m, sq=new Set(Array.from({length:p-1},(_,i)=>(i+1)**2%p));
  const expected=t=>{
    if(t<=0) return 0;
    let n=p*(p*p-1)/2*p**(3*t-3);
    for(let k=2;k<t;k+=2) n+=(p*p-1)*(p-1)/2*p**(3*t-k-3);
    return n+(t>=3?p**3*expected(t-2):0);
  };
  let split=0, unknown=0;
  for(let a=0;a<q;a++)for(let b=0;b<q;b++)for(let c=0;c<q;c++){
    let d=a*c-b*b,v=0;
    while(v<m&&d%p===0){d/=p;v++;}
    if(v===m) unknown++;
    else if(v%2===0&&sq.has((-d%p+p)%p)) split++;
  }
  if(split!==expected(m)||2*split>q**3||2*(split+unknown)<q**3)
    throw Error([p,m,split,unknown]);
  checks++;
}
if(checks!==5)throw Error('check count');
```

The observable is a scalar-invariant test on a proposed two-direction pairing; it does not construct a canonical spectral pairing or identify the leading Taylor coefficient with a regulator.
