# Average a cutoff, not the Goldbach target

This note gives an exact smoothing identity and a conditional one-sided criterion. It is not a Goldbach proof, not a claim of priority, and not a verified estimate on prime–Möbius correlations.

Fix an even target N. In [Huang–Li's divisor split](https://arxiv.org/html/2005.03811v2), keep the [corrected moving endpoint](https://zenodo.org/records/21939906): for m=N−n and integer k, the long term includes n only when α<m/k. Instead of requiring a favorable signed error for every α, integrate α uniformly over [A,2A], where one can take A=√N/(log N)^K with fixed K.

For any signed summand coefficient independent of α, the average of 1_{α<t} is exactly

    W_A(t)=0                      for t≤A
           (t−A)/A                for A<t<2A
           1                      for 2A≤t.

So averaging the sharp long-divisor boundary replaces its indicator by W_A((N−n)/k). At fixed k this multiplies the coefficient by a function of n with slope of magnitude at most 1/(Ak) on the ramp. The same substitution holds in the corresponding progression-average model, and therefore in the signed error, since both are finite sums. Exact rational replay tests this identity and the mean-selection inequality on 500 signed fixtures.

## The one-sided premise

Suppose the short side and the long-side model have been checked for the chosen interval, so their averaged contribution is 𝔖(N)(N−M_N)+o(N), where M_N=Σ_{n<N}Λ(n)μ(N−n). If that term has a uniform positive margin cN on the target family, it suffices for the ramp-weighted signed discrepancy itself to be at least −(c−η)N for some fixed η>0, uniformly for each large N in the family. This is a bound on the combined, signed error, not on the sum of absolute errors over all k and prefixes. Average lower control of the complete decomposition is enough because the exact underlying weighted prime representation count is independent of the split. Alternatively the average signed bound selects one favorable cutoff for this particular N, provided the other estimates have the needed uniformity in α.

Importantly the average is over **α for one fixed N**; it is not an average over successful and unsuccessful even targets. The arithmetic margin (for example [overlapping square lanes](../exclusion-debate/README.md)) and the new discrepancy bound must use the same ambient sum. If switching carriers, recalculate the margin. Prime powers on the first variable give a separately negligible error on the scale N.

## What the maneuver does not buy

The plateau of the ramp still includes all inner terms with (N−n)/k≥2A. A bad contribution with the same sign across all choices of cutoff will remain. No cancellation for the actual ramp-weighted discrepancy has been proved. The first useful follow-up is to recover a one-sided bound for a specific new band or show that a candidate mechanism fails on the common plateau. The ramp gives an exact observable and removes the demand for hard prefix boundaries; it does not remove the need for arithmetic.

For reproduction: `python3 -B replay.py | diff -u REPLAY.txt -`. Keep the RH proof-reading and the twin-prime fixed-shift comparison separate: this split explicitly uses the reflected partner N−n.
