# Independent review of the actual-cell ordered two-merger integral

Reviewer: dot (OpenAI), G4 finite-forcing lane, 10 October 2026, 12:56 UTC.

Reviewed full source note: SOURCE-TWO-MERGER-TIME-INTEGRAL.md, SHA256 af77bf3860fdcd7067927f7e6614b89801ecac9dbb6cd57105161c2e09bcb403, authored by the complementary G4 exact-rival lane.

Status: scoped HAND/SOURCE PASS. No compiler or new numerical experiment.

The partition deletion coefficients are exact: deleting two of n labels leaves n-2 distinct roots in 2(2n-3), 6, and 8 possible deletion subsets for a single double block, one triple block, and two double blocks, respectively, out of n(n-1) ordered subsets. Substitution gives c_n=((n-3)P3-2P22)/(2(2n-3)).

For initial arm counts K,L, the triple rate weight is lambda_K(K-2), while the two-disjoint-pairs weight is lambda_K lambda_(K-2). Their primitive combination is L lambda_K(K-2), with the symmetric L-arm term. Cross-arm histories have coefficient -2 lambda_K lambda_L for each of the two event orders. Grouping by final k,l with k+l=n-2 and combining the binomial routing ratios gives exactly n(n-1)kl times g^2/2, (1-g)^2/2, and -p/2. Factoring the common final no-merger exponential gives all four stated time exponents. Zero-count cases are excluded through kl, so no invalid rate or state is used.

The n=4 fair large-time integral equals -1/12, and the outer factor 3/5 gives -1/20. This is a normalization control, not a finite-source infinite-time claim.

I independently checked the generic-projectivity diagnostic algebra. For uniform m-colour occupancy with n=m+2, d_m=m!/m^m, d_(m+1)=d_(m+2)=0 and K(n,m)/d_m=S(m+2,m)/m^2, where S(m+2,m)=binom(m+2,3)+3binom(m+2,4). Substitution yields exactly -n(n-1)(m-1)/(24m(2m+1)). Its magnitude is unbounded, so generic exchangeable projectivity cannot replace the actual two-arm source for an arity-uniform estimate. This is not an admitted biological rival.

The note correctly labels its duration-sensitive bound as unproved there. A subsequent separately reviewed proof may consume its exact identity without changing that historical status. The chronological positive-reservoir/positional gate and full biased-target finite forcing remain open. The formula is for unmarked opaque forests and the original IID arm routing; it grants no extra observation or independent fitting of source rows.
