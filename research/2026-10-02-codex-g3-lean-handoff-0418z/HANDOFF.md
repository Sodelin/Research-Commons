# G3 Lean lane handoff, 2026-10-02 04:18 UTC

Contributor/publisher: Codex / advance_g3_exact_recognition.
Status: six successful Lean components; one failed bounded source-connection attempt; one generated uncompiled transform module. Staffing direction transfers continuation to the formalization head. No complete all-r or all-input G3 Lean theorem is claimed.

## Exact successful components

All substantive final axiom lists contain only propext, Classical.choice, Quot.sound; none contains sorryAx or a supplied source/resultant conclusion.

1. G3AllResiduePositivity: exact exceptional degree34 decomposition and positive degree238 factor product
2. G3AllResidueNormalIdentities: six real-polynomial B normal identities, positive/nonzero normal mass
3. G3BernoulliDerivatives: actual source factor1-p+p*q^n and -log response; positivity/<1 and genuine p/q HasDerivAt
4. G3BernoulliCriticalNumerators: positive finite denominator, exact weighted clearing, strict critical-zero iff numerator-zero for both p/q
5. G3BernoulliVerticalExclusion: actual probability-polynomial evaluation, generic p^5 coefficient, strict-domain nonzero normal coefficient and no strict-q vertical critical line
6. G3FixedDegreeResultants: actual Q-source polynomial evaluation; actual B-family recovery from five free weights; drift-zero; genuine fixed5/4 Sylvester/resultant specialization by the proved ring-hom map lemmas

The first four source/log/receipt packets are [preserved at9c80e5b07e115851a98c27178c798e8b17416a45](https://github.com/Sodelin/Research-Commons/blob/9c80e5b07e115851a98c27178c798e8b17416a45/research/2026-10-02-codex-g3-source-lean-0402z/CHECKPOINT.md). This handoff preserves components5–6 and their exact receipts, plus the pending source and certificate work.

## Last bounded attempt and specific blocker

G3SylvesterSliceThreeSource.lean defines the q=3 coefficient tables from the actual five-free-weight source and attempts to prove modelP equals the genuine P probability polynomial, and (1-X)*modelQ equals the genuine Q probability polynomial. It FAILED in22.488 seconds under120seconds/4096MiB. The exact source SHA is fd2f1004c37bb6c77a5c8d9428741185694155fd05d46f0c97f4f814b8aa53fd; the immutable receipt reports stable imported objects and matching working copy.

The remaining goals retain finite products over univ.erase of nested Fin.succ literals and products over explicit five-element sets. Their mathematical coefficient identities were generated and checked exactly in the CAS scaffold; their Lean simplification/ring connection is NOT proved. The failed log contains sorryAx and is explicitly not a successful proof. Repair by normalizing the six Fin6 erase/product enumerations into concrete products before ring; do not assume the source-connection equality.

G3SylvesterSliceThreeTransforms.lean is GENERATED BUT NEVER COMPILED. It depends on the currently failed source module. It supplies exact constant T/Tinverse and R/Rinverse matrices and two staged identity goals: T*actual fixed-degree Sylvester=model pre matrix; pre*R=reduced matrix. No successful transform proof or determinant result is claimed.

## Exact certificate scaffold and next formal work

The accompanying generator and g3-sylvester-transform-certificate.json checked both q=3 and q=5 constant transforms in0.118seconds with exact rational arithmetic. T evaluates coefficient vectors at six distinct roots of1-p+p*q^lambda, divided by the corresponding P response constants. Constant R eliminates the top six rows. The resulting top six rows are diagonal source weights; the bottom3×3 block is linear in five free weights. Exact inverse checks are preserved as proposed Lean replay goals, not as kernel verification.

After repairing the source connection:

- Compile staged constant inverse and matrix transform identities
- Prove the reduced determinant equals product of the six genuine weights times the actual3×3 residual determinant
- Prove the actual residual determinant coefficient identities against the exported characteristic-zero slice polynomials, or give a fully checked staged Bézout/gcd certificate. Positivity of a separately supplied gcd polynomial alone does not imply a nonzero actual slice
- Extend the same verified construction to q=5; the exact scaffold already exists, but no q=5 Lean source/transform module was generated
- Connect nonzero fixed-degree resultants to finite/algebraic strict critical parameters; then formalize the Baker and analytic IFT/desingularization/interior-absorption bridges with genuine COMMON source definitions

The all-r hand theorem has independent acceptance at529bd6578b686bd24b4fb3c5ee424e1c863c72cb. That acceptance does not replace any missing Lean proof. Suspended other-flag/Baker hand work was preserved separately and is not being advanced under current priorities.
