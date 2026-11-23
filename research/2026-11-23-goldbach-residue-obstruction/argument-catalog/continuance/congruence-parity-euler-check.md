# Three follow-ups to the reviewed checkpoint

Elementary consequences, not Lean verification or new solutions. Start from the [reviewed cofactor checkpoint](../2026-11-23-cofactor-cells-1718z/README.md).

## Goldbach: another residue family with no local compensation

Use the same q=3 and h=5s with prime s>5 as in the [three-offset calculation](three-offset-local-obstruction.md). For even N≡22 (mod 30), the actual offset j=0 again has discrepancy −Λ(N−15s)log(5s)/2. Offset j=1 is even. Offset j=2 is now divisible by 5, because n=N−15s−2 and N≡2 (mod 5). Thus the two comparison-only offsets are supported on powers of 2 and 5, giving total O((log N)^3) by the same injectivity and weight bounds, with the strict cutoff left in place. The family N≡22 (mod 30) is disjoint from the earlier N≡2 (mod 6). Together they cover six of the ten classes modulo 30 of even integers not divisible by 3. This does not force the main negative sum to be large, and gives no signed bound on the full discrepancy. A finite integer check validated the two offset congruences in 30,080 cases, even allowing odd composite s.

## Twin primes: which direction of error is needed outside the list

For the squarefree Li–Liu carrier with count C, let T be the total shifted Möbius sum over all prime starts up to X, and B the sum outside the carrier. With P the count of twin starts up to X, the exact identity is 2P=C−T+B. Consequently the useful off-carrier estimate is a *lower* bound B≥T−(1−ε)C, not necessarily an asymptotic or two-sided estimate. In particular, if one could separately establish T=o(C), it would suffice to show B≥−(1−δ)C for a fixed δ>0. A global o(π(X)) alone gives no estimate on this relative scale from the known lower bound for C. The identity does not estimate B. The signed-count rearrangement was checked in 9,471 integer examples.

## RH/GRH: missing Euler factors on the boundary

For an omitted prime p not dividing the primitive conductor, write its character value as exp(iθ). The factor 1−χ(p)p^(-s) is nonzero for Re(s)>0, by the reverse triangle inequality, and has zeros on the boundary exactly at s=i(θ+2πk)/log p for integers k. If the primitive character value is zero instead, the factor is identically 1. This is the general scalar mechanism behind the mod-2 example in the pinned source audit. On Re(s)≥δ>0, a fixed finite set of missing primes M gives lower bound product over p in M of (1−p^(-δ)). That bound is explicit but not automatically uniform as the missing-prime set changes. This does not establish a nonabelian extension or replace its analytic estimates.
