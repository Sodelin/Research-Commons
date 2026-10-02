# Independent hard-x ROOT support audit

Reviewer: GPT-6.1 Sol / continue_g_research. 2026-10-02, 15:22 UTC.

## Verdict

CONFIRM the bounded internal constrained-ROOT hard-x support blocker in the unchanged pinned public implementation. This is a source-admission finding, not a successful invalid RNA/probability output, a selected-class SUM result or an unconditional sampler-law claim. No runtime source or binary was modified.

I verified the exact public probe source SHA256 `d185d79366ee467237f0f7d913cbec5d1a638c191965aadf52b1b77bf87ec119` and executable SHA256 `81bcec4e54639f72635a6dfecba5726c25518856bbc15bd337aca7447bba5a39`. Independent resource-bounded runs reproduce all three recorded outputs byte-for-byte. The probe is an own diagnostic wrapper over the unchanged public ExactSession, not a new algorithm or source repair.

## Exact fixture

- Sequence: `AAGAAGGCGGUCGAAUCCGCCG` (22 nucleotides).
- Dot-control scaffold: `.....(((((......))))).`
- Target generated structure: `..[[......]]..........`, pairs (2,11) and (3,10) in zero-based coordinates.
- Left forced-x scaffold: `...x.(((((......))))).`, forcing position3 unpaired.
- Right forced-x scaffold: `.....(((((x.....))))).`, forcing position10 unpaired.

The target therefore pairs the forced-x endpoint in each x case. The original scaffold pair set is unchanged and has no x endpoint. The ordinary nucleotide pairings are canonical; this is neither a malformed length nor an out-of-bounds large input. Earlier eight-nucleotide all-dead cases, including their dead dot control, remain inconclusive controls rather than contrary evidence.

The dot query succeeds. Both x queries have successful ordinary inside computation, preserve constrained target ROOT weight `3765781.2113994271`, then return failed probability status, false reachable flag, negative-infinite log probability and NaN energy. These status fields are retained; the positive diagnostic weight is not advertised as a successful probability.

## Why this is genuinely ROOT-live

Fresh reads at `TakumiOtagaki/PKProbDesign` commit `27afdd054272dbda8a74c8aad156970a44c23cd8` match the saved public bytes for sparse_tree.cc, generate_exact_basic.hh, w_final_exact_inside.hh and api/exact.cc.

The constrained Viterbi traceback helper computes the actual ROOT trace and accepts its positive value only when the actual generated-pair set equals the requested generated target. Otherwise it explicitly zeroes the ROOT chart value and clears the trace. Thus the preserved positive value here is not merely an unused auxiliary chart cell or a proper-subset target fit: its actual ROOT generated set contains the x pair.

`evaluate_energy` records that ROOT weight, renders the actual trace's generated structure and only then calls union composition. Composition rejects reuse of the forced-x endpoint. `probability_from_evaluation` copies the diagnostic target weight before returning on that failed evaluation. Consequently the public API's final rejection is correct; it occurs later than the offending positive ROOT derivation.

The source parser represents x with partner−1. The ordinary V gate distinguishes free values below−1, while the VP open-endpoint path uses the broader negative partner test. This source-level distinction agrees with the observed witness. Parser/scaffold table correctness alone therefore cannot derive generated HardAllowed.

## Consequence and limits

An all-input claim that every positive constrained ROOT trace respects the forced-unpaired input is false for this unchanged implementation. That is a concrete blocker for connecting those positive source traces to the independent Γ hard-constraint ensemble. The earlier Lean parser/scanner/carrier and abstract weighted-law theorems remain correct at their explicitly conditional scopes; they did not instantiate this generated HardAllowed premise.

The trace weight is constrained MAX, not selected-class SUM. We have not independently quantified invalid mass in the unconditional SUM partition or RNG output distribution. Those require their own source-frame/weight and sampling bindings; the API error must not be silently treated as a proved normalized filtering/renormalization law. This audit makes no full physical-energy or whole-engine certification claim.

The next E admission task should diagnose/correct this exact source-support boundary under the user's authorized workflow, or explicitly account for a changed filtered model and its normalizer. It should not prove a false all-positive-root contract, silently exclude x inputs or redefine the independent paper hard constraint. No repair or upstream communication is authorized or performed by this review.
