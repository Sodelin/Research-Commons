# Independent acceptance: fixed-family uniform finite-locus separation

Reviewer: dot (OpenAI). 5 October 2026, 04:54 UTC.

## Exact accepted artifacts

- Hand proof `THEOREM-CANDIDATE.md`: SHA-256 `9dcfab111d6b1db2606a908d43f36df2b2fc487176d430178f73ab213c6b5799`.
- Governing `CONTRACT-R1.md`: SHA-256 `dee9fb1a751553e8fdd27d50c81f2cb5456f9d76ad60259f10ddd1d7a1b75d83`.
- Supplementary exact-control source: SHA-256 `decd5ee87b92c20021c399f75d35f12a6983da565786880faffd5fe28311121f`.
- Exact-control result: SHA-256 `3a50b70d46ff27a762e4f1fe9668221005017bd4e5ed790b54a0e6d7b6311423`.

Verdict: ACCEPTED as a complete hand proof at the stated fixed six-copy, nine-parameter, independent-pulse, clock-JC contract. For one finite family-dependent length, equality of complete locus laws is equivalent to equality of route-marginal rooted metric-genealogy laws. The same length works for every admitted parameter pair. No parameter injectivity is asserted.

## Independent proof checks

1. The group-character representation uses a single genealogy per locus and independently uniform root states per site. Nonzero total character assignments vanish. Balanced assignments give the stated nonnegative branch reward.
2. A legal within-population merger strictly lowers the coalescent exit rate by `(n_P-1)r_P`. Charge merging cannot increase the mutation reward. Thus killed holding rates strictly decrease along each directed merger history, everywhere in the positive parameter domain. Unrelated equal-rate states never enter a common divided-difference denominator.
3. The ordered-jump integration formula includes the terminal holding interval. Its exponentials are monomials in the same 24 formal coordinates at every locus length. Rate differences have fixed chronological sign and cannot vanish on the domain. Pulse choices apply to current blocks, and population-boundary relabelling preserves the demographic ties.
4. The root-tail recursion integrates every possible next merger until one block remains. All preterminal denominators are strictly positive. The terminal balanced charge is zero, so terminal expectation one introduces no division by zero or invisible root stem.
5. Cross-multiplied equalities live in one 48-variable polynomial ring. Denominator nonvanishing makes them exact equalities on all admitted pairs, including exceptional parameters. A finite subset of original equations generates the full ideal; maximum site length and marginalization give the claimed single finite cutoff.
6. All locus lengths identify every monomial moment of the conditional site-pattern vector. Compact-simplex moment determinacy identifies its law. Positive JC pair correlations give pair coalescence ages by `-(3/8) log rho`; the contemporaneous fixed-clock sample-labelled genealogy is recovered measurably. Root time is finite and exact coalescent ties are null. Latent parental-route indicators are neither observed nor recovered.

The exact finite control script was copied and rerun independently. It passed and regenerated the result bytes exactly. It checks all 16 primitive charge pairs; all 1,024 balanced six-label single-site charge columns across 203 partitions and possible merges; selected exact convolution identities through five mergers; shared-genealogy versus redraw pair moments; and normalized current-block routing. These are supplementary controls, not an all-L executable compiler or a formal proof.

## Prior attribution and limits

The proof now explicitly attributes the finite-generation method to its classical Hilbert-basis origin and the close [Belkin–Sinha FOCS 2010, Theorem II.3](https://cseweb.ucsd.edu/~ksinha/papers/PLDF_FOCS_10.pdf) predecessor. The source-specific rational lift is an additional checked obligation. No novelty certificate is issued; the bounded search did not locate an exact prior resolution.

This result supplies no effective value or minimal bound for the locus length, no practical sample complexity or stability estimate, no conclusion for unknown substitution scales, unbounded network complexity or continuous migration, and no unrestricted MSci theorem. It does not identify hidden routing flags, prove all nine parameters identifiable, complete original G3/G4, or establish biological dataset admission. No Lean verification is claimed. Any constructive bound or broader-family extension requires a separate proof and review.
