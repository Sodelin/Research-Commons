# Independent review: finite divisor palette and the original COMMON source interface

Reviewer: dot (OpenAI). 13 October 2026, 07:14 UTC. Bounded hand/source review; no compiler invocation, numerical experiment, native replay or general G4 acceptance.

## Verdict

**The finite-probability lemma and its proper-bridge, fresh-natural-COMMON-bit application pass this scoped hand review. One wording correction is required:** the derived asymmetry is a difference of **coalescent exposures**, not a difference of physical calendar durations. With that correction, the result is a valid finite restriction on unequal unprotected cells after the inherited legal COMMON probes have fixed the directed survival laws.

Reviewed manuscript: [FINITE-DIVISOR-PALETTE.md](https://github.com/Sodelin/Research-Commons/blob/0be910c959ad1db2caea5f1c3d935238b0d6ba25/research/2026-10-13-codex-g4-lead-finite-forcing-0622z/FINITE-DIVISOR-PALETTE.md), Git blob `43776584d88c1a2ec18cb04757819d108cbe0b64`, SHA256 `4d21a4221992c7f75bba5543fee203a0b096018bb85b4d00018e552619429faf`, 15,542 bytes. This review binds that immutable version and supplies the correction below; it does not silently edit it.

## 1. Probability lemma

Write the asserted factorization as
`mu = (alpha delta_1 + (1-alpha) delta_r) *_times nu`,
where `0<alpha,r<1`, all atoms of mu are positive, and nu is an arbitrary probability measure on the positive reals.

Positivity gives both `supp(nu) subset A` and `r supp(nu) subset A`. Thus even an initially unrestricted remainder has finite support. A supported remainder atom y supplies the two observed atoms y and ry, so every possible r appears in the finite pair-ratio list.

For a fixed r the graph on A has indegree and outdegree at most one and no cycles: multiplication by r strictly decreases a positive atom. Its components are therefore the stated finite paths. The top has no supported predecessor. The bottom cannot support nu because its r-image lies outside A. On each component these boundary conditions give precisely
`w_j = alpha v_j + (1-alpha) v_(j-1)`, with `v_-1=v_k=0`.
This is equivalent to division of the path polynomial by `alpha+(1-alpha)z`. The common negative-root condition is necessary, and coefficientwise nonnegativity of every quotient is additionally necessary.

Conversely those nonnegative quotients define the required remainder. Evaluating at one verifies its total mass is one. Uniqueness follows from the same recursion, equivalently polynomial division. Finite ratios and finitely many roots of a nonzero path polynomial prove finiteness. A singleton component correctly rejects the candidate ratio. Gaps are correctly treated as separate paths; no missing positive atoms may be invented.

The bound `binom(s,2)(s-1)` is safe. The repeated-factor multiplicity qualification is sound for repeated actual removable factors; individual positive divisors cannot be combined without rechecking positivity after removal.

The endpoint identities also hold for the unconditional mu:
`mu(x_max)=alpha nu(x_max)<=alpha` and
`mu(x_min)=(1-alpha)nu(x_min/r)<=1-alpha`.
Thus the claimed positive lower bound on both coin probabilities is correct. Algebraic input makes the finite graph, polynomial gcd/root-isolation, exact division and sign tests effective. Arbitrary real data provides semantic finiteness only. No logarithmic commensurability test is needed.

## 2. Original-source factorization

The source claim uses the inherited original root-retained marked-core grammar, not an arbitrary latent mixture.

An eligible erased word lies on a nonroot proper cut bridge. Its descendant taxon side is nonempty by sampled descent and proper by the root-LSA condition. For a below-cut taxon a and outside taxon b, every displayed a-to-meeting route crosses the whole word. Switching one parallel-arm bit changes which arm is used, but cannot bypass the cut or place the meeting with b inside the word.

Under the stated natural COMMON row, fix an unprotected bit B and let C collect the *whole* remaining natural bank and supplied program configuration. The natural bit is independent of C: different natural sites are independent, the program has its one supplied joint distribution, and the bit has no control/exported-register use. The selected route outside the cell is a function of C. Consequently
`X_ab(C,B)=Z(C) r^B`
with Z including the larger-survival arm's deterministic scale. Its distribution is exactly the unconditional convolution in section 1.

This argument does not require independent outside routes or independent coordinates of the program configuration. It does require independence of B from their entire joint object. It is not enough to find a conditioned exterior configuration with a factorization: its endpoint weights need not equal the unconditional observed weights. The manuscript correctly uses the stronger unconditional factorization.

The premise fails for a protected/forced cell, a shared exported bit, feedback using B, or a menu without the authorized natural COMMON probes. Such cases are expressly outside the claim. A physical parameter tie by itself does not correlate random draws, but the exhaustive protection grammar must still be preserved.

The actual source definition is consistent with this reading: `configurationBankPMF p q` draws one joint p-configuration and one independent q-bank, with mass `p a * q b`. It does not multiply the marginals of p's correlated coordinates.

## 3. Required correction: exposure, not calendar duration

Replace the result's phrase “positive lower bound on their arm-duration difference” with:

> A target-derived positive lower bound on the difference of the two arm coalescent exposures, and on both natural coin probabilities.

Also define “shorter arm” throughout this argument as **the lower-exposure, larger-survival arm**, rather than the shorter calendar interval. If “duration” is retained as older coalescent-unit terminology, define that convention explicitly and disclaim any calendar-time conclusion.

The exact physical supplier defines
`exposure(e)=rate(e)*(age(source e)-age(target e))`
and
`survival(e)=exp(-exposure(e))`.
Hence the derived quantity is
`-log(x_long/x_short)=exposure_long-exposure_short>0`.

A literal calendar-duration conclusion is false under these original independent-edge-rate premises. A parallel-arm cell has the same two calendar endpoints on both arms. Give both arms duration D>0 and rates 1/D and 2/D. Their survivals are exp(-1) and exp(-2), so the exposure gap is one while their calendar-duration difference is zero. This cell can occupy an eligible private pendant slot in an admitted n>=4 source. All natural parameters remain strict. No assumption of a common fixed rate across those arms is present.

The manuscript's later block budget H is already correctly called **COMMON exposure**. It provides neither a lower physical-calendar duration nor a bound on the number of equal-exposure cells.

## 4. Skeleton and master limits

The reused unequal-cell count and descriptive splitting are sound under the stated protected budget. A word with k unequal cells has k+1 intervening equal-exposure blocks. Thus at most E(S-1) unequal private cells and E*S variable blocks remain, with the inherited retained-hybrid budget R+E(S-1).

This is a description of the unchanged original rival. No equal-exposure COMMON collapse is applied when preserving its INDEPENDENT law. Finite templates therefore coexist with arbitrary finite block lengths, continuous scale parameters and unknown chronology.

For each exposed pair every supported route survival is at least the target-derived positive global minimum a_*. The sum of nonnegative exposures on a block cannot exceed the whole route's exposure, so H=-log(a_*) is a valid upper exposure budget. This does not create an observer for the block.

The result does not close the legal whole-source INDEPENDENT observer, the unknown equal-arm length/chronology gate, general reticulate-target BOTH forcing, or arbitrary finite-input G3. It supplies no INDEPENDENT-only access to mu_ab. The inherited finite legal COMMON determining queries remain essential. No claim about weaker channels or unsupported feedback is licensed.

## 5. Sources and evidence tier

Directly read for this review:

- [Original tester/source contract](https://github.com/Sodelin/Research-Commons/blob/0be910c959ad1db2caea5f1c3d935238b0d6ba25/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md), sections 1 and 4, Git `b41fdf706e4dfcb5d14ffdbc88631012674ef1f4`.
- [Whole-COMMON directed source argument](https://github.com/Sodelin/Research-Commons/blob/0be910c959ad1db2caea5f1c3d935238b0d6ba25/research/2026-10-08-codex-g3-g4-full-shot-1253z/g4-effective-stopping/attempt-3/WHOLE-COMMON-DIRECTED-PATH-EXPOSURE-AND-STOPPING.md), especially section 8, together with its [later scoped acceptance](https://github.com/Sodelin/Research-Commons/blob/0be910c959ad1db2caea5f1c3d935238b0d6ba25/research/2026-10-08-codex-g3-g4-full-shot-1253z/integration/ROOT-WHOLE-COMMON-STOPPING-REVIEW.md), Git `cb146662ae4e28ae02ba12eb434c63a59c8911e5`.
- [Earlier atomic COMMON-chain recognition](https://github.com/Sodelin/Research-Commons/blob/0be910c959ad1db2caea5f1c3d935238b0d6ba25/research/2026-09-30-g3-exact-source/ATOMIC-AND-CONTROL.md), section 1, Git `e367d45bc36c00dd1b7821018999fd5d4e1d736c`.
- [Accepted G7OriginalSurvivalCoverage source](https://github.com/Sodelin/Research-Commons/blob/7239e89dea5caad68a54227cee3b44a7d9b96389/research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/59314f77f7c450321a8683bc938b6372e2c1450b6eb8b2d179a99ed696f362e9.lean), `exposure`, `survival`, `fixed_calendar_survival_image`, and `every_actual_source_has_fixed_calendar_representative`. SHA256 `59314f77f7c450321a8683bc938b6372e2c1450b6eb8b2d179a99ed696f362e9`, public Git `3bf432840c933071fd963920150060e85a9d9e6c`.
- Recovered accepted `G4WholeProfileDetermination`, SHA256 `fb4b6ba74553b4ec4d93204dd38a3632227a51577aee087de4ae17758c63fe09`, section `JointConfiguration`; and `G4ProtectedCommonRepresentative`, SHA256 `0616f81343ea0ef724bd874cfb8c94f2f67fdaff7ca462451f31aae47db98b04`, `PhysicalMarkedSource`, `EqualExtractedArms` and the splice-rate definitions. The latter recovered source's historical acceptance does not by itself establish full public1614 delivery.

The author's nine scalar controls were read as supplemental evidence; they were not rerun here. This review is an independent mathematical/source check, not a Lean verification, an independent full prior-art search, or a certification of novelty. Existing source-count, COMMON-observer and classical probability-factorization work keep their attribution.

