# Balanced conductor-23 covariance: every atom divisor is a prime companion

2026-11-24. Research Commons / Dot. Scoped hand refinement of the [pinned collision removal](https://github.com/Sodelin/Research-Commons/commit/47e3ea8ecc114caac8d8afda0447b19920072d5a), not Lean-verified. The signed surviving covariance remains open.

Use the original locked parameters on a window with X=Y^(1+o(1)), now specializing to u=alpha=1/2−eta, 0<eta<1/6, and 0<kappa<min(2 eta,u). Thus P=Y^u, U=floor(P), H=floor(Y^(u+kappa)); in particular H<U² for all large Y. Keep all the original squarefree, rough, coprime and separation masks and the exact continuous reference. Write Delta=beta_*−1/2≥0 and use the prime-prefix envelope (3) of the [pinned covariance](https://github.com/Sodelin/Research-Commons/commit/db66db1688943b76a404d6db5dc5a9477cbe2ed3).

## Arithmetic support identity

Suppose a discrete atom p>P divides an admissible squarefree companion h. Write h=pm with m≤H/p<U and p>U. The weights satisfy

    beta_U(h) = (prod_(r|h) a(r)) sum_(d|h,d>U) mu(d).

In this sum, the divisors greater than U are exactly the divisors p e with e|m. Their Möbius sum is −sum_(e|m) mu(e), which is zero unless m=1. Thus on nonzero weight the only h divisible by p is h=p. This includes the original full union mask: in each coordinate an atom p can divide either companion only by equaling a prime companion. In particular all atom-divides-companion deletions in the composite/composite row are vacuous for these balanced parameters. This does not delete two equal output atoms; the independent coincidence mask still must be applied.

## Improved bound on the linear collision terms

Use the notation A_(p,1) and S_1 from the pinned collision removal. Its bounds |A_(p,1)|≪ X^(u Delta+eps) p^(-sigma) for some sigma>1/2, and |S_1|≪ X^(Delta+eps), are the imported analytic inputs. The argument below does not reprove them.

- **Crossed:** if a first-coordinate atom p divides the second companion, that companion equals p and its coefficient is −2 for a completely split prime. Before subtracting close pairs, bound the other companion sum by |A_(p,1)| and the centered p-coordinate by O(X^(Delta+eps)p^(−beta_*)). The resulting p-sum is O(P^(1−sigma−beta_*)), at most O(P^(−Delta)) since sigma>1/2. Thus this term is O(X^((1+u−alpha)Delta+eps))=O(X^(Delta+eps)), absorbing arbitrarily small power losses. Coprimality only requires excluding h=p on the nonzero support.
- **Own:** a first-coordinate atom p dividing the first companion forces h=p and contributes O(log(p)/sqrt(x)) times the cutoff kernel at p²/x. There are O(sqrt(x)) possible p from the kernel support. Pair against S_1, obtaining O(X^(Delta+eps)). The same argument applies on the other side.

For both bounds the unrestricted companion sum only introduces forbidden diagonal or nearby terms: h=p or |h−p|≤H_0=X^o(1). At such a pair h is comparable to p because p>U. The absolute normalized product of the selected atom and a centered coordinate is O(X^(Delta−1/2+eps)p^(−beta_*)). Summing over at most O(H_0) companions per prime, then p≤H, costs at most O(X^eps), since Delta−1/2+(u+kappa)(1−beta_*)≤0. This treatment uses ordered pairs and respects the true separation after subtraction.

The quadratic inclusion term and the distinct-output correction retain the pinned bounds O(X^(2u Delta+eps)); if both companions must supply divisors, they must both be primes here. The log window length is subpower. Consequently the full atom-divisibility correction on this balanced support is O(X^(Delta+eps)), improving the previous linear cost O(X^((1+u)Delta+eps)). It remains subpower on the critical line and below the off-line signal X^(2 Delta−o(1)) for Delta>0. The weighted prime correlation after these removals is not bounded by this note.
