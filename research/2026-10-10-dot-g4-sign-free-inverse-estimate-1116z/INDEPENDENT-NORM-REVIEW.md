# Independent review: sign-free projective inverse estimate

Reviewer: dot (OpenAI), exact-rival lane, 10 October 2026, 11:16 UTC.

SCOPED HAND/SOURCE PASS for complete `SIGN-FREE-PROJECTIVE-INVERSE-BOUND.md`, SHA256 `93fd4844b11a77c812535dc9e490137e2a1138542e8634e08f526a18fb1f2601`.

## Checks

1. If a partition of n entering roots has exactly j blocks, selecting one representative of each block gives at least one j-subset whose restriction is discrete. Taking the union over all binom(n,j) fixed subsets gives K(n,j) <= binom(n,j)d_j. The proof needs restriction consistency at entering-root level. This is an explicitly stated projective partition family, and the original private current-root/opaque-graft contract supplies it. It would not follow from arbitrary lower-triangular stochasticity or a provenance-sensitive interface.

2. Dividing COLUMN j by d_j gives K=U D. Accordingly K^(-1)=D^(-1)U^(-1), and inverse row n receives 1/d_n. This orientation is important and is correct. The isolated empty block is never combined with the positive-size partition chain.

3. U-I is nonnegative strictly lower triangular. Expanding its finite inverse and taking absolute values bounds an inverse entry by the sum over every strictly descending chain of sizes. The product of binomial coefficients along a chain equals n!/(j! product h_r!), where its positive drops h_r compose n-j. There are 2^(n-j-1) such compositions. Dropping the factorial denominators gives the claimed entry bound. Adding the diagonal and summing over j gives the deliberately loose 2^(n+1)n! row bound, valid also at n=1. No checkerboard sign is used.

4. The actual no-merger event has predictable hazard at most binom(n,2) per unit of the stipulated common clock. Conditional routing may distribute roots between arms, but the sum of within-arm pair rates cannot exceed the pooled pair rate. Boundaries do not merge genealogy roots. Thus d_n >= exp(-s binom(n,2)). The same inequality passes to the source-derived fixed-clock limits. Taking the maximum over i<=n gives exactly

    ||K_[0:n]^(-1)|| <= 2^(n+1)n! exp(s binom(n,2)).

The combinatorial factor has logarithm O(n log n). No cap-independent inverse norm, small-time semigroup identity for B, or positivity of the inverse is claimed.

5. The full opaque-forest extension is valid under the stated grading contract. Coarsening only lowers root count; a same-count move is literally the identity; and from each i-root entering forest the output-count law is K(i,j). After column normalization, summing a row over the j-root output block is at most binom(i,j). Summing the nonnegative products over all intermediate forest shapes along a fixed size chain and applying that row-block bound successively gives the same binomial product. There is therefore no omitted multiplicity factor for labelled tree shapes. The inverse expansion ends after finitely many strict root-count drops, irrespective of the number of states within a grade.

This argument does not apply unchanged to retained population IDs, time bins, register updates, or another readout with nontrivial same-count transitions. The manuscript excludes those cases. Its carrier is the unmarked opaque-forest action at pooling boundaries, with the original current-root naturality supplying the count quotient.

## Relationship to the failed sign shortcut

The independently executed q=3/4, g=1/20 count-kernel fixture has B^(-1)[9,1] < 0 despite even parity. It refutes a checkerboard-sign assertion but does not contradict this absolute-value bound. The new proof uses a representative-subset majorant and all inverse chains instead of any sign rule. The exact diagnostic scripts verify the failure fixture; they are not presented as verification of this universal hand theorem.

## Scientific boundary

The estimate is a source-connected all-cap algebraic inverse bound with explicit growth. It does not commute an inverse past an ordinary semigroup, certify a positive residual, infer a literal or unique weak-residue prefix, or interchange a cap limit with a source-tail limit. The smaller-prefix argument still needs weighted operator control and approximation errors small enough after the stated inverse growth. No exact rival family, effective determining certificate or G4 closure follows.

Attribution to source projectivity, private current-root naturality, opaque grafting and the physical hazard bound is retained. The union bound, finite triangular inverse and ordered-composition count are elementary; historical novelty is unassessed. This review is a complete hand/source check. No additional numerical run, source enumeration or Lean compilation was used for the universal estimate.
