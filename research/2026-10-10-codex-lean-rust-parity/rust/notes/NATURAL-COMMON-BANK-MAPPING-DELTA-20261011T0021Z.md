# Natural COMMON: new mapping details and remaining carrier gaps

Contributor: Codex Rust implementation role; 2026-10-11 UTC. This is a
source-only follow-up to the unchanged original-control plan
`SOURCE-FIT-ORIGINAL-CONTROL-REUSE-20261010T2312Z.md` (SHA256 `66051721…`).
The natural141 kernel run is scheduler-owned; this note makes no acceptance
claim for its new proof roots and starts no compiler, native or reference work.

The frozen sources compared are the exact preserved versions of
`G6OriginalCommonPrefix.lean` (`68e0130b…`) and
`G6NaturalCommonForestFactorization.lean` (`fcadb6c4…`), existing bank
`source_fit_bank.rs` (`e31b80a3…`), rooted readout (`7a3a75b6…`), word
(`7fbb4e63…`), boundary (`f089b81f…`), frontend DTO (`a4e86fe9…`) and natural
frontend consumer (`0eef0719…`). Full identities and inspected declarations
are in the adjacent JSON capture. The current native `443a1eb6…` was only
rehashed; it was not executed or copied.

During this review the current prefix path changed to proof-only compatibility
derivative `ce9ec8df…`. Its preserved `68e0130b…` version remains exact, and
current factorization remains `fcadb6c4…`. The pin assertion stopped before any
passing capture, and that failure is separately preserved in
`NATURAL-COMMON-CURRENT-PATH-PIN-FAILURE-20261011T0024Z.json`. Root directed this
comparison to use the original exact versions. The current prefix diff adds a
dated explanation and proof normalization for append membership and
singleton/nil simplification; imports, definitions, and theorem statements
are unchanged. Its kernel acceptance is pending in this review. This static
mapping does not supersede the failed compiler attempt or accept its repair.

The existing documents already correctly distinguish original gamma from old
gamma, natural initialization from conditional transitions, and the rooted
observer from controlled full-register laws. No correction to those contracts
or runtime code is needed. Three additional mappings are worth retaining.

## Exposure order determines the residual coin orientation

`NonrootBigon.arm_sources` gives the two original incoming occurrences the same
upper vertex, and both have the original hybrid as target. Consequently their
full strict-calendar durations are the same positive number D. The fitted bank
keeps each occurrence's own survival x_b and defines its rate by
`rho_b = -log(x_b)/D`. The new source definition is exactly
`tau_b = rho_b * t`; there is no factor of two in this transport. At the full
bigon duration t=D, its reference unit-rate survival is exactly x_b.

For the supplied rational full-arm survivals, the new positive minimum-exposure
baseline and nonnegative residual have the following exact symbolic mapping:

```text
tau_short = min(tau_0,tau_1) = -log(max(x_0,x_1))
delta     = tau_long - tau_short
exp(-delta) = min(x_0,x_1) / max(x_0,x_1).
```

This is a representation consequence of the already defined logarithmic bank,
not a newly evaluated logarithm or native factorization theorem. For a shorter
common interval t, the ratio is raised to t/D and remains subject to the bank's
existing unevaluated fractional-power boundary. For equal arm survivals,
delta=0 and residual survival=1: `residualEpoch` uses the algebraic identity
epoch. This must not be submitted as another strictly interior fitted survival
or used to assert construction of a positive physical identity edge. The
baseline remains strictly positive because both original rates and D are
strictly positive.

`longArm` is the original occurrence bit, not an ordinal invented by sorting
exposure values. True addresses parent1; false addresses parent0. Original
gamma is P(true/parent1), and the existing bank converts it as
`gamma_original = 1 - g_old`. Therefore the residual is applied with probability
gamma_original when longArm=true, and with probability
`1-gamma_original = g_old` when longArm=false. For old g=1/3 these are 2/3 and
1/3 respectively. An implementation must bind the actual occurrence map before
selecting that weight; probability complementation never complements the
stored or forced bit. The equal-exposure case permits either longArm because
both residual branches are identity.

## Full Old records need more than final native rows

The new `erasedRecord` is the entering Code plus every endpoint in the finite
initialized prefix vector, with the selected private register erased. `old` can
read that entire pair, including an empty prefix's entering Code. The
`actual_natural_stored_selector` theorem ties the end-of-prefix COMMON selector
to the same original once-drawn seed. `actual_private_bit_law` uses original
gamma; the prefix independence is obtained from the source private-seed history
theorem under `NoPrivateWordRead`, not supplied as a caller independence flag.

The native word initializer agrees in its declared semantics: one Boolean per
original hybrid, P(true)=original gamma, nonhybrid bits false, and no new draw
in conditional COMMON boundary rows. Every native boundary and word transition
checks preservation of the whole entering register. These existing primitives
and their saved controls can be reused; another register/route engine is not
needed.

However, `word_row` aggregates to final selected-view coefficients and keeps
one range witness per final key. It does not retain the entire initialized
prefix endpoint vector. The completed rooted consumer subsequently forgets
the latent register and cannot serve as an arbitrary `Old` reader. The source
prefix adapter also preserves the actual `Finset.toList` tied-node order,
whereas the native calendar uses ascending original IDs. Existing phase
commutation establishes endpoint PMF transport; it does not on its own
identify every intermediate prefix column or arbitrary readers of those
columns. Any future full-Old consumer needs an explicit record/readout
correspondence, rather than another endpoint comparison.

This finite endpoint vector is distinct from timed merger histories within an
epoch. Neither the new contract nor current native snapshots provide such
merger-age data.

## Local erased forest is not the current completed rooted observer

The new factorization requires that **every live owner on every entering-law
support row** is at the named original hybrid. Carried copied descendants stay
with their current ancestor. A generic whole-calendar fitted-source request
does not imply that local premise. Other populations cannot be silently
rescaled; a proper cohort needs the existing restricted-copy/context transport.

The new `erasedForestRegister` keeps the entire full unranked forest and every
other register coordinate. It can have multiple roots and is not an ancestral
completion. The current `ROOTED_UNRANKED_COMPLETE` observer instead requires a
completed single genealogy at the original ancestral root and deliberately
forgets all latent registers and representative/orientation details. Thus its
accepted finite rooted tables do not discharge this local forest/register
readout or the future-context premises. The source future-erasure theorem has
an explicit same-source `NoPrivateWordRead` guard; erased private bits must not
later be read by another COMMON action.

Conditional forcing remains exactly as in plan `66051721…`: draw the natural
initializer unchanged, then apply a mask only to conditional transition
polynomials. The current typed rooted forcing specialization substitutes gamma
in the whole natural polynomial, including the initializer; it is disclosed
as a rooted observer specialization, not a register-preserving controlled
source process. Nothing in the new natural factorization changes that boundary.

No engine, test, rebuild, reference producer, source-admission flag, timed
readout, full-Code runtime claim, or public interface is added by this note.
The existing saved bank/readout/labelled-program controls are referenced only;
they are not rerun and cannot stand in for the new support, full-Old,
private-erasure, or proper exterior-context correspondence obligations.
