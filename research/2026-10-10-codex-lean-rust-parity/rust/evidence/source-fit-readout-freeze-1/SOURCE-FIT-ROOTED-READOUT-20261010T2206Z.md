# Exact completed rooted readout of a supplied survival bank

Contributor: `/root/rust_implementation` (Sol role), 10 October 2026, 22:06 UTC.
Status: NEW source implementation and static interface review; compiled/native
execution is pending with the sole scheduler. No target, old compiler, Lean or
native process was run for this capture. Accepted calendar/word/completion,
bank, frontend and application bodies were not edited by this contribution.

The additive [source_fit_readout.rs](../src/source_fit_readout.rs), SHA256
`7a3a75b60af55f1138e82aa66c5a2e94b5dc9c8a597eadb0ff25230f03dae7c5`,
uses the existing `source_word::word_row` on the natural whole-calendar word
held by the checked [Bank](../src/source_fit_bank.rs). The bank remains
`e31b80a3648e6aa15c8c99f30f4eb94e3fb06c6487f7241064391c05c12ffa5a`.
No new coalescent, clock, boundary, completion or source-inference recurrence is
introduced. This is the forward consumer of the
[supplied-bank contract](SOURCE-FIT-BANK-BRIDGE-20261010T2154Z.md), not a replacement
for the recovered exact source fitter.

## Typed callable interface and explicit observer

`readout(&Bank, &Request) -> Result<Decision, Error>` is the public function.
`Request::natural(&Bank)` selects one weight-one natural configuration and the
explicit `ROOTED_UNRANKED_COMPLETE` observer. The Bank must hold Natural
initialization, ANCESTRAL_COMPLETE and nonempty Copy; other requests return
Unsupported without a table. Arbitrary conditional/warm-start codes are outside
this consumer. A full ordered-view observer is not silently coarsened.

The module runs the unchanged word once and retains its complete ordered
selected-state polynomials, source-valid range witnesses and work record as
evidence. It aggregates complete rows to one rooted genealogy using the existing
`unordered_forest`. Representative IDs, child orientation and latent register are
forgotten only for the explicitly selected observer. No copied-label or retained
representative multiplicity is inserted or divided out.

The resulting `Outcome.tree` uses GLOBAL integer leaves. To recover the old
copy-string alphabet, use the inverse lookup `global_labels[i] -> copy_labels[i]`
and then canonicalize child order in that alphabet. A global label is never a
local array index. The preserved permuted request includes
`[9007199254740993,0,17]` to challenge both this lookup and exact large integers.
The module returns the numeric canonical tree and keeps the Bank's label maps;
string relabelling is a disclosed frontend/readout transport, not an implicit
change of the observer.

## One bank, exact substitution and unsupported boundaries

Every configuration uses the same original x bank and unforced original gamma
bank. Original gamma is P(parent1), equal to one minus inherited g=P(parent0).
Parallel incoming occurrences remain distinct, and a forced bit is never
complemented. The natural whole-calendar agenda enters each original hybrid once.

For each word monomial, active slot survival powers contribute the rational
whole-edge exponent `k * delta_slot / duration_edge`. Gamma values and program
weights are substituted exactly. Identical rational edge-exponent keys are then
summed across ALL complete ordered rows in the chosen genealogy fibre. Exact
zero coefficients are removed before the integrality check.

Inactive edge and ancestral axes stay separate in the collection key, even
though both are unused by the expected natural calendar. They may cancel exactly;
any surviving use returns Unsupported. Any surviving nonintegral edge exponent
also returns Unsupported, naming the tree, original occurrence and exact
exponent. No logarithm, arbitrary algebraic root or decimal is evaluated. Only
surviving nonnegative integer powers are evaluated at the shared rational x
bank. The returned E-variable polynomial and rational probability are exact.

This order is essential: requiring integrality before complete-fibre summation
would reject terms that cancel, while discarding inactive axes before summation
could falsely manufacture a completed law. No generic native coefficient
refinement or per-row integrality theorem is inferred from the source-level
whole-edge gathering provider.

## Optional program and labelled joint response

The library Request permits one to sixteen unique labelled program terms with
positive exact weights summing to one. Each forcing vector has exactly one entry
per original hybrid: None is natural; false/true specializes original gamma to
zero/one and selects original incoming parent0/parent1. This is a disclosed
ROOTED_UNRANKED_COMPLETE polynomial specialization of the natural completed word.
It changes the once-drawn latent register law too, so it is NOT advertised as a
controlled full-Code/register law. The first frontend consumer is natural only;
exposing more program controls requires the corresponding old compiler check.

Each `ConfigurationLaw` retains its label, weight, forcing and alpha-weighted
outcomes. Its mass equals alpha. The caller must explicitly set
`forget_configuration_label` to additionally return their mixture, of mass one.
A mixture is not a labelled-program response. No requested observer is changed
to manufacture a successful result.

## Decisions, budgets and evidence fields

TABLE contains observer, unchanged `word_table`, all labelled configuration laws,
optional mixture and collector work. Existing provider UNKNOWN keeps the complete
unchanged word limit, including stage/kind/population/required/cap. Collector
UNKNOWN uses a separate stage/kind/decimal-required/cap record and returns no
partial table. InvalidInput and Internal remain distinct errors. Unsupported
returns a reason without a rational PMF. A serializer must preserve these
distinctions and enforce the already declared bounded frame transport.

Collector defaults/hard maxima are: word_rows4096;
monomial_contributions262144; normalized_terms65536;
arithmetic_steps1000000; rational_bits4096/default and65536/hard;
power_exponent4096. Program length is at most16 and each label is1..128bytes,
unique and NUL-free. Program mass/domain/shape are checked explicitly.

The raw term count times program length is checked BEFORE collected edge keys
are generated. One running normalized-term count covers every configuration's
entire fibre collection, and a separate running count with the SAME declared
cap covers the optional returned mixture. New nonzero keys are prechecked;
exact cancellation decrements the count. `largest_normalized_terms` records the
maximum observed across both collections. The latter mixture accounting corrects
design's preliminary source-only draft finding; no earlier draft was compiled.

Checked add/multiply/power inputs and results obey the new rational bit/operation
limits. Existing provider internals retain their existing provider limits; this
collector does not claim its own bit counter proves all inherited work or OS
resources. Work is observed accounting, not a certificate of exhaustion or
complexity. Scientific flags stay false: supplied-equation satisfaction does not
authenticate generated source equations, observation fit, source admission,
timed merger histories, full-Code evaluated laws or full solver completion.

## Focused verification plan and current evidence

Three controls are authored, not executed: the existing natural completed-word
consumer with a large permuted global embedding; exact fractional-term
cancellation before Unsupported; and rejection of a surviving fraction or
ancestral axis. The scheduler should run these and the five existing bank
controls, followed by the NEW standalone frontend's scoped tests. There is no
reason to rerun unchanged old117/native/calendar suites for this separate binary.

The input-only old COMMON, INDEPENDENT and permuted witnesses and immutable
expected rooted rows are in [fixtures/source-fit](../fixtures/source-fit).
[Source capture receipt](../evidence/source-fit-bank-bridge-1/RECEIPT.json),
SHA256 `b5c8492ab2d4f7435afa098e44bab4f3ead862567bc74c30a918fbd6536b23bc`,
records seven independent Fraction/reference controls and zero target processes.
Native acceptance should compare all new complete probabilities with those saved
old laws, preserve the asymmetric1/3 ->2/3 gamma orientation, and challenge wrong
equations, shared cut identity and large global-label mapping.

Root owns shared exports and the new standalone frontend. The sole scheduler
owns all compilation/target execution. Design owns independent static and
coefficient review. No general source/parser/Lean refinement is asserted here.
