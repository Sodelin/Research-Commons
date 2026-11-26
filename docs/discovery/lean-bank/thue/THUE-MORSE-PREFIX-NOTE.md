# Thue–Morse: count the starts with matching height zero

## What was already public

[Alexander's 2013 article, §6](https://arxiv.org/html/1212.0186#S6) poses the unavoidability classification. The **specific** binary population used here is from the later [classification manuscript, §2](https://github.com/avg-netizen/biological-unavoidability/blob/3d6175e3e23f67bd68e7be591b5a9a6d04e496a3/paper.md#2-an-explicit-binary-avoiding-population), not a construction attributed to Alexander in 2013. The [public height note](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/19544a4d7608c8cc0d5a1205605c0f38631ca05f/notes/FULL-HEIGHT-PROOF.md) and `FullHeight.lean` at the same commit already prove attainment and the exact seven-case height formula for every start, including zero; `SharpThueMorse.lean` supplies the sharp 8/3 bound and equality indices. `DigitRecurrence.lean` separately derives a digit recurrence for individual heights. Here the graph has edges into w≥2 from w−1 of label t(w), and from w−2 of label 1−t(w). A matching path reads t starting at phase zero.

The Commons [MAP package](https://github.com/Sodelin/Research-Commons/tree/3bb3cdc9992dd14369bc5b1299ca18fdfd9e93ed/research/2026-10-04-dot-thue-morse-first-occurrence-lean-0550z/package) is a distinct project: it proves first positions attaining global maximal monochromatic arithmetic-progression lengths in three difference families of [Joshi–Rust, Conjecture 3.8](https://arxiv.org/html/2501.05830v2#S3.SS2.SSS2), with ranges n≥2, n≥1, and n≥0 respectively. The new prefix count does not reuse that proof or conflate its largest progression run with a graph path.

## Scoped extension

Write t(n) for binary digit-sum parity, L(v) for the actual maximum matching-path length, and Z(N) for the number of starts v=0,…,N−1 with L(v)=0. Then

    L(v)=0  iff  (t(v+1),t(v+2))=(1,0).
    6Z(N) = 2(N+1) + B(N+1) − 3t(N+1),
    B(0)=0,   B(N)=(N mod 2)−B(floor(N/2)).

Thus B is the alternating binary digit sum (plus at the lowest bit). The formal count uses an Int-valued nonnegative prefix sum whose increment is the indicator of actual height zero. No graphs beyond this exact model and no other path phase are covered.

For v≥1, a length-one path exists iff the short edge has label t(0)=0 or the long edge has that label. Their failure is exactly the displayed 10 pattern. At v=0, the short edge is absent, but 0→2 is labelled 0; the condition also fails since t(2)=1.

Let F(N) count changes across consecutive digit-parity bits at indices i<N. By the standard dyadic laws t(2j)=t(j), t(2j+1)=1−t(j) (see [Allouche–Shallit](https://cs.uwaterloo.ca/~shallit/Papers/ubiq15.pdf) and the checked provider), the even position always changes; the odd position 2j+1 changes exactly when the pair at j does not. Pairing adjacent positions gives F(N)=N−F(floor(N/2)). The sum of ascents minus descents across i<N telescopes to t(N). The omitted descent at index 0 is absent. Therefore 2Z(N)=F(N+1)−t(N+1). Set B(N)=3F(N)−2N to obtain the stated recursion and exact count.

Two prose corollaries of the checked identity:

- For m≥1, B(2^m+1)=1+(-1)^m and t(2^m+1)=0, so Z(2^m)=floor((2^m+2)/3). At m=0 the count is 0.
- For all prefixes, Z(N)=N/3+O(log(N+2)), giving density 1/3. The worst-case order of discrepancy cannot be improved to o(log N): along N+1=1+4+…+4^(m−1) the alternating digit sum is m, t(N+1)=m mod 2, and Z(N)−N/3=(m+2−3(m mod 2))/6.

This is a distinct statistic derived from a known word identity and a reused graph theorem. No literature priority is claimed. The asymptotic and dyadic corollaries above are hand deductions, not separate Lean declarations.

## Independent replay

`PROVIDER-MANIFEST.tsv` lists the exact nine upstream sources in dependency order, including Git blob IDs checked against the public connector and SHA-256 values. Lean 4.33.1 builds all nine, then `Reuse.lean` binds three exact graph heights and the all-start zero criterion. `PrefixCount.lean` checks the flip recurrence, exact digit recurrence, actual indicator, and exact prefix count. The checked endpoints use only propext, Classical.choice and Quot.sound (some use a subset). No Mathlib needed for this lane.

The independent `check_prefix.py` finite fixture replays 512 actual graph heights by frontier search, compares the complete pinned height table at those starts, and checks 65,537 prefix counts and 16 dyadic counts. The proof is not inferred from the fixture.
