# Supplied-calendar application contract

Contributor: Codex design lead, 10 October 2026. Status: reviewed implementation contract, not a new mathematical result. Root authorized the additive `calendar-law` application command. This consumes the accepted [private calendar producer](CALENDAR-REFINEMENT-20261010T1340Z.md), word, and ancestral-completion components; their existing sources, schemas, binaries, and receipts remain preserved.

The user supplies one original graph, copied samples, calendar, shared inverse rates, original hybrid probabilities, mechanisms, and work limits. The command saves its complete ordered genealogy-state polynomial table and exact physical substitutions, or a bounded `UNKNOWN` or input refusal. This is a forward calculation for supplied inputs. It does not search all sources, recover parameters from observations, or provide a source-exclusion, confidence, or policy certificate.

## Input and frontend

`calendar-solver solve [--request PATH]` reads a file when supplied and stdin otherwise; no arguments aliases stdin solve. `calendar-solver check --request PATH --certificate PATH` repeats the bounded calculation and compares complete canonical result bytes. This native checker is replay, not the independent reference algorithm. Check emits `{"schema":"source_calendar_check_v1","status":"ACCEPT"}` with exit 0 or the same schema with `REJECT` and exit 1. All emitted JSON is compact, recursively sorted by object key, ASCII, and followed by one LF.

The UTF-8 request is at most 65,536 bytes. Its exact nine fields are `context`, `ages`, `inverse_rates`, `original_gamma`, `common`, `terminal`, `compiler_limits`, `word_limits`, and `provider_limits`. Their nested fields, array order, arities, graph predicate, caps, and defaults are unchanged from the private contract. Object key order and whitespace may vary. Duplicate or unknown keys, malformed UTF-8, floats, exponent-form counts, nonfinite values, booleans used as integers, and incorrect array arities are rejected. Natural tokens are nonnegative decimal integers, with `-0` accepted as zero; values must fit unsigned 64 bits and the runtime's checked index type. Rational strings must already be reduced canonical `p/q`, including `0/1`, with positive denominator. Request byte limits bound their aggregate size; no new rational bit cap is introduced.

Original edge IDs preserve parallel occurrences. Original gamma is the probability of parent occurrence 1. Natural initialization draws the full register once, including when Copy is empty. Ages may be negative or serial; strict chronology is required on every edge. All inverse rates are positive, gamma is interior, and mechanism length equals the hybrid registry length. Completion requires nonempty Copy. Full input validation precedes generated compiler limits; hard limits are 32 letters, 16 slots and 256 variables. Checked integer work arithmetic and existing provider limits are retained.

## Native result

The successful/unknown outer schema is `source_calendar_result_v1`. It is exactly the private calendar frame with the `fixture` field removed and its schema renamed. The nested `word_result` is exactly the private word frame with `fixture` removed and schema `source_word_result_v1`. Request echoes are semantic JSON with original array ordering. The adapter separately binds the exact raw request bytes and their SHA-256.

| Result | Exit | Required contents |
|---|---:|---|
| `TABLE` | 0 | Complete request echo, false source gate, requirements, full agenda, physical-coordinate substitutions and complete nested `TABLE` with variables, rows, witnesses and work. |
| `UNKNOWN`, compiler scope | 2 | Echo, false gate, exact requirements, `unknown_scope: COMPILER`, first exceeded compiler limit. No agenda or partial table. |
| `UNKNOWN`, word scope | 2 | Echo, false gate, exact requirements/agenda, nested `UNKNOWN` with derived request/variables/limit, `unknown_scope: WORD`, and `consumer_population` preserving the original edge or ancestral population for inner epoch/completion limits. No rows/work. |
| `ERROR` | 1 | Only `schema`, `status: ERROR`, and `error`, one of `INVALID_REQUEST`, `INTERNAL`, `EXECUTION_FAILURE`. Details go to stderr. No partial calculation. |

Result size is at most 4 MiB. Invalid argument/file/launch/write failures remain distinct from invalid mathematical input. `EXP_NEG` records mean exactly `exp(-duration / shared_inverse_rate)`; the output does not approximate this transcendental value or assert independent physical slot coordinates.

## Independent acceptance and launcher

[calendar_check.py](calendar_check.py) checks strict framing, status/exit pairing, exact request/derived-child identity, the full occurrence-preserving agenda and physical substitutions. For `TABLE`, it independently computes full ordered rows using the coupled-generator spectral reference and copy-based boundary marginalization, checks every coefficient, total mass, retained register and actual reached literal witness, and verifies the word's deterministic logical work and wrapper caps. This reference does not reuse native merger-history recurrence. It ignores inner provider caps when constructing mathematical reference rows: successful coefficient validation is not a proof of every native inner work counter.

Compiler `UNKNOWN` is independently recomputed. Word/inner-provider `UNKNOWN` authenticates known limit kind, legal stage/population, input cap and `required > cap`; it does not independently prove provider exhaustion. No `UNKNOWN` becomes an exclusion or partial table. These distinctions are recorded in machine-readable checker flags.

Root's existing application launcher adds `calendar-law --request PATH --output NEWDIR --binary PATH [--expected-binary-sha256 SHA]`. The bounded adapter captures and stages the producer, native replay checker, this helper and its exact eight-module reference closure, with pre/post identity records. Success is `SUPPLIED_CALENDAR_TABLE`, exit 0, only after both native replay and independent all-coefficient checks. `UNKNOWN` is exit 2; refusal/execution failure is exit 1. Fresh-output/no-overwrite and existing process/output bounds apply. Source admission, source-census completeness, observation-law admission, statistical confidence, global physical-survival image, and full solver/policy completion remain false. `certificate_valid` stays false; exact table, agenda, substitution and coefficient checks have separate flags.

## Acceptance obligations

Run the general frontend on the frozen supplied-calendar inputs, including nondefault provider budgets, negative/serial dates, tied cohorts, parallel edges and asymmetric two-hybrid registers. Challenge duplicate/unknown keys, malformed rationals/counts/UTF-8, incorrect status/exit pairing, forged balanced coefficients, witnesses, work, agenda and physical substitutions. Preserve earlier 32/163 and 2/96 private evidence. Run the existing 117 RC1 regression only if an accepted RC1 executable changes; exact unchanged executable identity permits receipt reuse. Root owns actual launcher and adapter evidence. Generic calendar parsing/refinement and universal native source correspondence remain formal obligations after finite acceptance.
