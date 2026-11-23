# Where the asymmetric sieve stops in the moving-exponent regime

**Status:** Source audit and elementary reductions, not a new Goldbach bound or Lean proof. Here b is the desired factor exponent, not the cutoff called beta in part of the source.

## Fixed cutoffs versus a moving exponent

[Li–Liu, arXiv:2606.05224v2, §4](https://arxiv.org/html/2606.05224v2), Proposition 4.1 starts with a=1+b, tau=b/(1+b)−epsilon and 0<alpha<tau. Its finite detector retains prime leftovers or an eligible two-factor leftover whose least prime factor is in [N^alpha,N^tau). Propositions 4.2 and 4.3 switch to fixed-cutoff weighted inequalities for a>1.5+3 epsilon. Proposition 4.4 gives a different decomposition for the conditional part and explicitly requires a>1.05+3 epsilon, as well as 1/21<kappa<sigma≤tau<1/3. The cutoff order alone gives b/(1+b)>1/21, hence b>1/20. This is a boundary of those hypotheses, not an optimal exponent or an impossibility theorem. The paper's proved conditional exponent is b=0.4 under Elliott–Halberstam, not 0.05.

For the target b=c/log N, with fixed c>0, the same ordering cannot hold at large N. Moreover, even if one removed the fixed lower bound on kappa and retained only 0<kappa<tau<b, the stated endpoint error allowance O(N^(1−kappa)) would not certify a positive main term at the N/log² N scale by size alone. The envelope N^(1−kappa)≥e^(−c) N is larger than that scale by an unbounded log² N factor. This does not say the actual error has that size. One must bound it differently, avoid charging it this way, or replace the decomposition. The more flexible finite inequality is not itself a positive analytic estimate.

## Finite exclusion of small factors

For even N and odd first prime p, N−p is odd. To exclude factors 2 and 3 at once one may require gcd(N−p,6)=1. More generally, at each odd prime ell in a finite list, require p not congruent to either 0 or N modulo ell. At most two classes are forbidden, so a CRT combination exists with both sides coprime to the product. This is local compatibility, not primality of either side. A separate positive bound for representations subject to the restrictions is the open analytic input. For b=c/log N, any composite residual in the target family has smaller prime factor r<e^c, since q<N. Thus excluding the finite set of primes below e^c would suffice **if** the moving-exponent representation were also proved with those exclusions.

For any fixed b>0, there is no universal finite list of all possible smaller factors: choose any odd prime r and an odd prime q>r^(1/b), and put N=3+rq. This gives even N and a permitted semiprime representation. It is not evidence that N lacks a separate prime–prime representation. At b=1/10, two concrete checks (q primality tested by trial division through its integer square root) are 177156=3+3*59051 and 48828148=3+5*9765629; in both cases q>r^10. This explains why the preceding finite replay only seeing r=2 cannot justify dropping the other factors at larger scales.

See [threshold criterion and finite replay](README.md) for the previous stage. No VibeMath submission.
