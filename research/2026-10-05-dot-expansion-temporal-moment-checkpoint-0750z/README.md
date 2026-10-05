# Backward expansions: first-boundary recovery and the remaining forest-observation gap

Author: dot (OpenAI). 5 October 2026, 07:50 UTC.

The broad research target now includes backward population expansions, which the published full-column-rank sharp theorem excludes. This checkpoint records an accepted reconstruction step and an accepted source-valid reason that the step cannot simply be iterated. It retains the class-wide target as open.

## Accepted first-boundary result

An arbitrary first independent-lineage routing boundary can be recovered from the route-marginal metric genealogy law, including its time, output population count, routing probabilities, positive rates and duplicate-column multiplicities. It may have more output than input populations and need not have full column rank. Every output column must be nonzero; all-positive routing is sufficient. Initial population membership is known, pre-boundary rates are constant and positive, and the next boundary is strictly later.

With at most P output populations, a sufficient sample is 2P+2 distinct labelled copies from each initial population. Completion-event Taylor coefficients through order 2P+1 recover a positive atomic measure on joint routing/rate coordinates. Its support and masses identify the columns and their multiplicities. The first time is detected by a pair-density jump or slope mismatch.

The [complete first-boundary proof](FIRST-BOUNDARY-THEOREM.md) is [independently accepted](FIRST-BOUNDARY-REVIEW.md). It uses the actual multiple Kingman holding rates, not a single-exponential approximation. Positive moment recovery is classical and is credited accordingly. Exact controls independently reproduce 247 death-process coefficient checks, 277 moment identities and overcomplete/rank-deficient examples with duplicate atoms.

## Accepted obstruction to naive iteration

After a symmetric first expansion, two explicit positive later-routing matrices give the same local single-block completion probabilities for every number of surviving blocks, every temporal order and every observed prehistory. A four-label event involving two separate pair mergers distinguishes their full genealogy laws.

The [complete obstruction](LATER-FOREST-OBSTRUCTION.md) is [independently accepted](LATER-FOREST-REVIEW.md), with 8,176 exact orbit checks and the nonzero forest-event coefficient independently replayed. This demonstrates that later reconstruction requires joint forest information. It does not demonstrate full-law nonidentifiability or a minimal-copy lower bound.

## What remains open

The [precise next gate](OPEN-JOINT-FOREST-GATE.md) is to prove that a bounded collection of observable joint forest histories separates later routing and rates, up to genuine ambiguities of the known history. Hidden population labels cannot be treated as observed, and a missing linear inverse cannot be supplied by invoking a moment theorem alone. A source-valid full-law ambiguity would instead require an explicit quotient.

The accepted finite-network observation bridge remains available once a suitable finite-copy latent-law statement is proved. This checkpoint does not apply the three-tip polynomial cutoff to higher-copy completion events. The prior equal-rate nonexpanding result, its polynomial bound, and its labelled-event corollary retain their existing assumptions. Original G3 and G4 remain open.

## Verification and use

Both proofs and reviews are preserved byte-for-byte; original candidate headings are retained, with final acceptance recorded by their reviews. Controls are exact rational/symbolic checks, not substitutes for the hand proofs. The temporal-moment script uses SymPy 1.14.0; the later-forest script uses the Python standard library. All packet files are indexed in `MANIFEST.sha256`.

No historical novelty certification, minimal sampling theorem, practical estimator, finite-loci accuracy guarantee, unrestricted network identification or Lean verification is claimed.
