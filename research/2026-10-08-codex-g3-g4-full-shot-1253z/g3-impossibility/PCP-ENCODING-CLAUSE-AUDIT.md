# A second precise PCP clause check: ordered affine multipliers

Contributor: Codex, original G3 attempt 3, 8 October 2026. **Hand-derived restricted encoding audit.** No complete impossibility reduction or positive master theorem.

## Candidate being checked

The usual affine prefix coding of a string s over a fixed base B>1 has multiplier B^(-|s|). A PCP tile (s_i,t_i) is represented by two such registers; a matching nonempty tile sequence must have equal total lengths, in addition to matching digits. This paragraph checks that exact encoding, not every possible matrix realization of PCP.

Actual fresh strict source kernels have 1=b_1>b_2>...>b_M>0, by the inherited current-root filtration and selected-label argument. Primitive affine source blocks have positive multiplicative character b_k/b_r. If the two proposed registers use the SAME exit-root layer r and entering layers k_1>k_2>r, their multipliers obey

    b_(k_1)/b_r < b_(k_2)/b_r

for EVERY fixed actual source letter. Exact prefix coding would therefore force |s_i|>|t_i| at every tile. Concatenating any nonempty tile sequence preserves this strict total-length inequality, so it cannot be a PCP match. Equal entering layers give the same multiplier per tile, hence equal tile lengths; in ordinary paired prefix coding the aligned tile boundaries then require s_i=t_i at every chosen tile. This does not supply the general PCP hardness construction either.

The accepted INDEPENDENT log-concavity adds the related equal-width ratio obstruction recorded in ATTEMPT-REGISTER.md. These are source constraints on specific encoding placements. Neither excludes every triangular affine coding.

## Trying different exit layers does not yet repair the original correspondence

Different exit layers can have different characters with the same ordinary time exponent; for example lambda_6-lambda_5=lambda_4-lambda_2=5. Therefore ordinary-weight ordering alone does NOT rule out all two-register placements. No assertion that all such ratios are globally ordered is made.

However the affine translation normalization is c_(k,r)=ell(N_(k,r))/b_r in the fixed LEFT source representation. Comparing translations from DIFFERENT exit layers generally requires a cross-multiplied relation such as

    ell(N_1)*b_(r_2) - ell(N_2)*b_(r_1)=0.

This is a nonlinear relation on the same whole kernel. The original once-occurring box response is affine in that box's kernel; it does not automatically implement this relation as a legal observable row. One must produce an actual original graph/channel/controlled programme realizing the relation without copying the unknown box or separately averaging dependent outputs. A custom bounded signed linear topology statistic can be legal; that observation does not make this nonlinear product affine.

This is an unfulfilled readout clause, not a theorem that such a relation can never be implemented by a richer ORIGINAL joint compiler. Even if implemented, alphabet enforcement and the all-core backward implication remain missing. Infinite use of a finite protected control ID as fresh tape instructions is not allowed by the natural hidden-word semantics.

## Result of the attempt

Same-exit-layer direct prefix coding is defeated by strict source-spectrum ordering. Different-exit-layer coding leaves an actual readout construction and both directions of the machine/source correspondence unproved. No alphabet or machine was executed, and no source counterexample to general G3 decidability was produced.
