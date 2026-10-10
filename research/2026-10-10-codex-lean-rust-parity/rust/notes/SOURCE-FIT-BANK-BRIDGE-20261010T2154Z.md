# Exact supplied-survival bank bridge

Contributor: `/root/rust_implementation` (Sol role); 10 October 2026, 21:54 UTC.
Status: implemented NEW Rust source, source review/compiled execution pending.
No accepted library, application, DTO, backend or runtime was modified. No Rust,
Lean, old solver, old compiler or native process was executed for this packet.

The [new module](../src/source_fit_bank.rs) represents a supplied rational
assignment as one exact physical bank. It checks the supplied sparse polynomial
trace, keeps every original edge occurrence, converts the inherited parent-zero
probability to original parent-one probability, and produces the existing
calendar agenda and symbolic word. It preserves logarithmic inverse rates and
unevaluated positive-root relations rather than rounding them into the current
rational Calendar DTO.

This supplies a practical representation interface between the existing exact
source fitter and existing calendar/word consumers. It does not reconstruct the
source-observation equations, validate the provenance of those equations, admit
the full original source class, or produce timed merger histories. In particular,
caller-supplied zero equations can be satisfied without establishing any fit.

## Existing providers and conventions

* [Recovered exact fitter](../../../2026-10-04-dot-practical-solver-recovery-1803z/01-exact-source-solver/package/solver.py)
  SHA256 `42e4353d3033e807e26bc409c724fcdee2a01552a630c9364f428f92f9ffe0db`:
  `encode_value`, `decode_value`, `verify_witness`, `physical_realization` and
  `equations`. The same graph and x/g assignment are used for every supplied
  observation row, including randomized programs. Its physical realization
  uses tip ages zero, other ages one plus maximum child age, and
  `rate_e=-log(x_e)/duration_e`, with ancestral rate one.
* [Original frontier compiler](../../../2026-10-01-g7-continuous-design/law_compiler.py)
  SHA256 `eb829017262d571d32d2ac4e08e4afffcd00c02210e2b1ec6337dee59862cdb7`:
  `Network.structure` preserves incoming edge occurrence order and sorts hybrid
  names; `Network.parameters` uses x_e and g_h; `compile_law` gives g_h to
  incoming parent zero. A forced bit remains the original incoming 0/1 bit.
* [Current calendar producer](../src/source_calendar.rs), SHA256
  `d993e8808a4f227001a393db123b1be00f70a5c940388586d909772bbb3ff3a8`,
  and [current word consumer](../src/source_word.rs) retain interval slots,
  original populations, shared register, global sample embedding, natural
  once-only register draw and original gamma=P(parent1).
* [Current public Calendar DTO](../calendar-cli/src/request.rs), SHA256
  `1bb2b9569f47c101705e63b011cc4c8b4a58f6e8702bb404813d7659702f462a`,
  requires exact rational inverse rates. A general `duration/(-log(x_e))` is
  not supplied by that type. This bridge does not change it.

The three quoted source hashes above are checked in the fresh source capture.
The calendar hash in this note is also checked, rather than inferred from old
receipts. A correction must preserve this note and capture separately.

## Frozen typed request and transport contract

`Request` contains the existing `Context`, vertex-name/taxon/hybrid/copy-label
bijections, the exact old variable bank x0..x(E-1), then sorted-name g_h,
`ExactValue` vector, sparse `Polynomial` equations, one global COMMON or
INDEPENDENT mechanism, FULL_VIEW or ANCESTRAL_COMPLETE terminal, existing
compiler limits and new exact arithmetic limits.

It retains the separate declared hybrid labels (for example `site_alpha`) and
engine name (for example H0), taxon labels versus engine leaf names, local Copy
alphabet versus global integer embedding. It rejects missing/duplicate labels,
reordered variable banks, and a native incoming parent order inconsistent with
the inherited ascending original occurrence IDs. Parallel endpoint pairs are
never deduplicated. This is a narrower typed consumer than an arbitrary native
hybrid ordering; it reports refusal instead of silently reordering parents.

The canonical request schema is `source_fit_bank_request_v1`. The canonical
result schema is `source_fit_bank_result_v1`. Encoding is compact lexical-key
ASCII JSON plus LF; rational strings are reduced p/q with positive denominator.
There is no raw JSON parser added here. A future wrapper must use the existing
duplicate-rejecting JSON discipline and bind its raw input bytes/source hashes
separately. The complete semantic request is echoed in every result. A successful
Bank stores its Request privately; encoding it against a foreign Request fails.

Hard class bounds are those of `Context.validate`: graph/bank at most32,
copies at most4, plus original E+ancestral bank at most32. Label UTF-8 length
is1..128bytes. Sparse trace is nonempty, at most4096equations/65536terms,
all exponent vectors have exact E+H length and exponents at most4096.
Algebraic descriptor degree is1..64 with one-based index in1..degree;
this checks shape only, not the count/location of actual real roots.
AncestralComplete requires nonempty Copy.

New soft limits/defaults are:

| Limit | Default | Hard maximum |
| --- | ---: | ---: |
| equations |4096|4096|
| terms |65536|65536|
| arithmetic_steps |1000000|1000000|
| rational_bits |4096|65536|
| power_exponent |4096|4096|

The canonical request is bounded to64KiB before generation; result frame to4MiB.
Input rationals exceeding the absolute65536-bit guard are refused before gcd
normalization. Within that hard guard, canonical shape/domain validation precedes
soft limits. Input, intermediate and output rational operands/results obey the
soft bit bound. Exponentiation checks each multiplication; a fractional exponent
numerator/denominator is compared to the exponent cap before machine conversion.
Matrix/forest/epoch recurrences are not added. Work records count supplied rows,
terms and checked add/multiply/divide operations; comparisons, fixed-small height
construction, normalization, serialization and inherited compiler work are not
presented as independently verified work or a global complexity proof.

Soft exhaustion yields UNKNOWN with no partial Bank. Compiler limits retain the
old word/slot/variable order. OUTPUT `result_bytes_lower_bound` reports the prefix
size at the encoder's rejected next token, explicitly a lower bound on the full
frame, not a claim to have generated it. UNKNOWN is operational, never an
infeasibility or source-exclusion certificate.

## Exact bank and cut semantics

Every rational assignment value lies strictly in(0,1). Every supplied trace
equation is evaluated with that one assignment using capped BigInt rationals.
A nonzero row is a refusal, not a source exclusion. An algebraic RootOf descriptor
is preserved in the bound request but returns UNSUPPORTED; no root positivity,
algebraic equality, trace check or log evaluation is claimed.

For each original occurrence e with parent p and child c, derive the old exact
height ages and positive duration d_e=age(p)-age(c), keeping the one fitted x_e.
The returned symbolic inverse rate is d_e/(-log x_e), with ancestral inverse rate
one. Original gamma is1-g_old; old g=1/3 gives original gamma=2/3. The forced
parent bit itself is not complemented.

The unchanged calendar compiler is called with temporary unit inverse rates
solely to obtain dates/cohorts/slots/letters/one Natural child word. Both its
proxy physical_coordinates and its parent unit-rate Request are discarded.
The new result is not `source_calendar_result_v1`, and no unit-rate request or
old physical-rate-checked flag is emitted. Exits precede entries exactly as in
the existing producer. The child word contains no numeric inverse rates.

For an active original edge slot of duration delta, its coordinate is the SAME
atom power x_e^(delta/d_e), never a new fitted cut atom. For x_e=p/q and positive
reduced exponent a/b, the primitive integer constraint is
q^a X^b-p^a=0 with0<X<1. Since0<p<q and b>0, there is exactly one positive root,
inside that interval. This is an exact defining relation, not an evaluated root.
Only integer exponents are rationally evaluated. Fractional powers remain
unevaluated even when a particular root happens to be rational.

The bridge checks that active slots cover each whole edge with exponent sum one.
Inactive original edge coordinates remain disclosed symbolic unused metadata;
they do not emit independent root constraints. Finite agenda ancestral coordinates
are disclosed unused `exp(-delta)` for ancestral unit rate. Additional interval
requests must lie wholly inside the same edge and have positive duration.

## Scope and verification state

Successful status is SYMBOLIC_BANK with `supplied_trace_checked=true` only.
All of `source_observation_fit_verified`, `source_provenance_verified`,
`source_admission_verified`, `certificate_valid`, `timed_readout_verified` and
`full_solver_verified` arefalse. Algebraic/UNKNOWN results do not assert a trace
check. The same formal bank can later be consumed by the existing symbolic word;
this module itself does not execute it, compute a completed PMF, introduce a
timed readout, or prove the native encoder's correspondence to typed Lean inputs.

Five meaningful Rust controls are authored, **not executed**: saved full COMMON
trace/orientation/shared cuts; wrong equation/foreign Request/parent and interval
rejection; distinct parallel occurrences; lossless algebraic UNSUPPORTED; and
input/root budgets with domain priority. The evidence capture independently
rechecks the preserved old rational witnesses/physical fields using Fraction
arithmetic and a whitelisted equation AST. That is source capture/reference
arithmetic evidence, not a compiled Rust execution claim.

Next action: root may export the stable module and schedule the small Rust build/
controls. A separate proposed completed rooted-unranked consumer can reuse
`source_word::word_row`, substitute this single bank, collect rational edge
exponents after the explicit genealogy readout, and evaluate only integral
surviving exponents. Residual fractions/used inactive/ancestral coordinates must
remain Unsupported; arbitrary algebraic evaluation and a new source engine are
unnecessary and are not proposed.
