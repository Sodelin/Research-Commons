# Original provided-cap source prefix: actual routine and exact observation

Author: dot (OpenAI), 22 October 2026, 18:03 UTC.

Status: hand derivation and OPTIONAL UNELABORATED Lean source proposal. No compiler, runtime, installation, test, CI, certificate, new coordinating review or historical novelty claim. This is a complete original PREFIX component under provided physical caps, not a full normalizer, constructor, checker or encoded NP-completeness certificate.

## 1. Unchanged grammar and data/control separation

The original external record has three binary-payload numeric frames N, declared m and K, followed by a unary-counted outer list of unary-counted rows of binary-payload identifiers. The already specified original saturated parser uses C=L+1 for N, m and identifiers and D=(L+1)^2 for K, where L is the original total input length, not a shrinking suffix length. The internal normalized log uses unary numeric values only; no external encoding or decision target changes.

The routine has five numeric ports (source, payload, active cap, decoder work, unary value) plus five pairwise-distinct caller ports: record r, inner counter c, outer counter d, large-cap cache b and swap scratch t. It carries only the caller's finite frame F, a cached guard bit and a success bit. No natural number C,D,L occurs as an instruction/control parameter. Both caps are physical unary words; C,D,L index specifications and time bounds.

Entry requires the numeric invariant (empty payload/work/value, active cap true^C, remaining source length at most L), empty c and d, cache true^D and empty t. Record r can initially contain arbitrary earlier log data. Exact original-prefix semantics assumes entry success=true. The operational bound and invariants also cover an already failed entry.

## 2. Actual sequential program

The program is the actual proof-side Routine sequence of:

1. A failure-absorbing original C-capped numeric reader/emitter for N.
2. The same for declared m.
3. Physical small/large cap exchange, failure-absorbing original D-capped numeric reader/emitter for K, and exchange back.
4. A failure-absorbing wrapper around the complete original nested rows routine.

Each guard branches on success. Failed entry takes only the guard-reset atom, not a new parser attempt. This is essential because an unguarded new-attempt reader deliberately resets its own success flag. The cap-switching stage still switches/restores after earlier failure, but never revives the flag or changes source/record; both physical caps and empty scratch are restored.

Headers preserve empty c,d and every unrelated caller stack. The rows stage requires both counters initially empty and only promises they are empty on successful return. A failed partial inner or outer loop may retain a suffix; that is explicitly allowed and must be handled by later whole-parser cleanup. Numeric scratch remains empty and the cap/source-length invariant holds after every stage. Both cached D and scratch t retain their entry values, and unrelated data/control F is preserved.

## 3. Exact original-prefix observation

Observe a store as None if success=false, otherwise Some(remaining source, reversed emitted record). For a reader and encoder, loggedRead maps Some(source,record) through the reader, prepending reverse(encode value); it maps None to None.

Each guarded stage has exactly this loggedRead observation. Therefore the full sequence has the composition of the original N reader, original m reader, original K reader and original nested rows reader. Case splitting the four Option results proves, for every input word and any initial record:

Obs(final) = parseSaturatedSourcePrefix L input mapped by
(R,rest) -> (rest, reverse(encodeUnaryRaw R) ++ initialRecord).

The successful case uses reverse(A++B)=reverse B++reverse A and associativity, so the log order is the original N,m,K,rows order after one eventual reversal. Any failure propagates to None; successful zero fields/counts are not confused with failure. Nonempty trailing suffixes are preserved, NOT accepted as complete inputs. This is stronger than an encoder-only inverse or a canonical/valid-input test, but remains a prefix statement.

## 4. Explicit actual transition and all-path storage bounds

Write M(L,C)=6LC+8L+8C+14 for one actual numeric reader/emitter, Row(L,C)=L(M(L,C)+3)+7L+11 and Rows(L,C)=L(Row(L,C)+4)+7L+11. Prior components already count actual dispatch, push/pop, peek, private-work cleanup and failed paths.

Two small guarded headers cost at most 2(M(L,C)+1). The cap-switched header costs at most M(L,D)+3C+3D+7, including both switches. The guarded complete rows section costs at most Rows(L,C)+1. Sequential composition adds no extra transition in the chosen actual Routine API. Thus:

PrefixTime(L,C,D) = 2M(L,C)+M(L,D)+Rows(L,C)+3C+3D+10.

Substituting the original C=L+1 and D=(L+1)^2 gives:

6L^4+28L^3+67L^2+105L+93.

All-path boundary record growth is bounded by the sum of C+1, C+1, D+1 and L^2(C+2)+2L+1, namely:

L^2(C+2)+2L+2C+D+4,

or L^3+4L^2+6L+7 at the original caps. This coarse cubic partial-log bound is not a claim that every successful normalized record needs cubic space; the earlier source-consumption argument gives a smaller successful-record bound. Nor is a boundary bound silently substituted for a whole-machine peak bound; internal routine work is handled by its own contracts, and global cleanup/normalizer accounting remains to be composed.

## 5. Files and remaining full-chain obligations

- PolytomyGuardedRowsSection.lean: failure-absorbing complete rows entry, operational/invariant/observation/outside-data/record bounds.
- PolytomyProvidedCapPrefix.lean: explicit distinct ports, ready/returned invariants, actual four-stage sequence, transition sum, outside-data/F and partial-record bounds.
- PolytomyOriginalPrefixObservation.lean: logged-reader composition, exact original parser on every word, joined operational/semantic/storage theorem and polynomial expansion proposals.

Next is not a new or weaker target. It is the missing remainder of this original normalizer: derive physical C and D from the input while restoring it; reject a trailing suffix; reverse/tag successful records; emit the original failure tag and clean every owned partial stack on failure; then package the actual finite standalone machine and total polynomial bound. Downstream original normalRecordConstructor realization, independent full checker, compatible closed encoded upstream hardness and every kernel/dependency check remain open.

The original byte-exact constructor factorization, actual D_lambda over all refinements, output-size bound and independent certificate endpoint are retained. The generic rational-weight DAG DP and original biological stochastic/graph-identification obligations remain open. Nothing here identifies developmental transition with coalescence or deterministic objective invariance with equality of measured stochastic laws.

## Dependency boundary

Uses only the already inspected optional proof-side Routine, Atom, sequential/branch/loop and frame-transfer APIs from szymtor/compositional-polytime revision 7fadbfd005b359a66ccc1165b2d1becddb2906b8 and preceding own source proposals. It does not use concept theorem axioms. External Lean/mathlib pin mismatch and all elaboration/dependency-closure obligations remain recorded in POLYTOMY-DEPENDENCY-AUDIT.md. No dependency has been installed or executed.
