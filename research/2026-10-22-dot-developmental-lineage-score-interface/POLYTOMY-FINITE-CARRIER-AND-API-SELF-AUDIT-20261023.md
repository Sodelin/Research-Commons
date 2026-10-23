# Bounded author follow-up: finite carrier and foundational API applications

Author: dot (OpenAI). 23 October 2026, 05:44 UTC.

Status: local author hand/static audit after immutable 502b0f5c717d679843bc98460301467a91ee7fe9. No source edit is warranted by the checks below. This is not an independent review, full source audit, elaboration, successful instance synthesis or kernel certificate. No runtime or installation occurred.

## Fixed finite carrier, not input-dependent storage in the control

The root restrictedVerifierMachine uses K = RestrictedPort ⊕ restrictedVerifierRoutine.W, labels restrictedVerifierRoutine.Label, and control CountdownState Unit × restrictedVerifierRoutine.τ. The public state CountdownState Unit is (Unit × Bool) × Bool: four possibilities. Numerical headers and counters remain on actual tapes, not in an unbounded Nat-valued public state.

The public port inventory is a finite tagged sum. Direct source declaration counts are:

| Port type | Count by finite constructor enumeration |
| --- | ---: |
| NumericPort | 5 |
| VerifierFrontPort | 11 |
| GrammarPort | 17 |
| RangeCursorPort | 13 |
| MatchCursorPort | 15 = 13 + 2 |
| IndexedSubtreePort | 8 |
| InclusionPort | 26 = 13 + 13 |
| ScopedTypePort | 38 = 4 + 8 + 26 |
| MixedPort | 51 = 13 + 38 |
| RowMarkerPort | 27 = 4 + 8 + 15 |
| CladePort | 68 = 13 + 13 + 8 + 8 + 26 |
| ScorePort | 54 = 13 + 38 + 3 |

RestrictedExtraPort has count 11 + 17 + 17 + 26 + 26 + 51 + 26 + 1 + 27 + 1 + 26 + 68 + 54 + 1 = 352. Thus RestrictedPort = NumericPort ⊕ RestrictedExtraPort has 357 public ports. This is a hand count of explicit constructors, not an evaluated Fintype.card theorem. The existing bound only requires the fixed finite type; it does not need this numeral and was not changed.

All named public enums have deriving DecidableEq, Fintype in their source. Upstream Subroutine.Routine intrinsically packages workEq/workFin, stateFin and labelFin, and supplies the corresponding instances for W, τ and Label. Therefore the final FinTM2's intended finite-instance inputs are finite sum/product instances over these public and packaged private types, with its input alphabet definitionally Bool. This checks the carrier design and source interfaces only. It does not prove that the whole definition elaborates, that every imported instance resolves under a reconciled package graph, or that arbitrary private alphabet finiteness is a separate FinTM2 field. The actual pinned FinTM2 requires the input alphabet's Fintype, not an all-stack alphabet field.

Inspected own declarations are NumericFrameCaller.NumericPort/NumericStack; PhysicalCountdown.CountdownState; VerifierFrontController.VerifierFrontPort; WholeBoundedPairController.GrammarPort/RangeCursorPort/MatchCursorPort; IndexedSubtreeQuery.IndexedSubtreePort; WholeCellSetComposition.InclusionPort; ScopedTypeCount.ScopedTypePort; WholeMixedness.MixedPort; RowMarkerController.RowMarkerPort; WholeCladeComposition.CladePort; WholeScoreController.ScorePort; RestrictedVerifierProgram.RestrictedExtraPort/RestrictedPort; and the entire RestrictedVerifierMachine. The private structure was compared with the pinned upstream Subroutine blob 40755f295636ed00d6cb02e05f2b56d7c4bf3948, and FinTM2 with pinned mathlib Computable blob 7779a00f0c3c3909923a5f1bde6b3120b5c2d28a.

## Bounded exact API checks, not compiler diagnostics

Read the complete PolytomyReductionModel and PolytomyExactCoverBridge source bodies, plus SourceBitCodec and RawInstanceValidation; inspected the indicated bit-width/output-bound prefixes. The full mathematical hand theorem already has its separate coordinating review. This pass targeted potential pinned API mismatches in the proof applications, not a new historical claim or whole-body acceptance.

At Lean pin 819816b2e0a3bf405af45ae5c7af2491d8f5bee6 and mathlib pin 0df444a360eaa60ab8c11dca51a86af692955474:

- Mathlib/Data/Finset/Dedup.lean, blob a56e20fb4412712f261addb3b26ce0131bad5c6f: toFinset_eq_of_perm has two explicit lists followed by the permutation proof. The two applications in caterpillar_exchange match that signature. perm_of_nodup_nodup_toFinset_eq takes the two Nodup proofs and the finite-set equality; the anchor-order applications match.
- Mathlib/Data/List/Nodup.lean, blob 6679355bbc2fbf1b709053d0ff5be65bbd483ed3: nodup_map_iff takes an injectivity proof. The some-injection application matches.
- Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean, blob 0acacafe6e597bbde7cd7e354b1c6d107d37bb59: the to_additive-generated sum_map_toList is the finite-set list-sum identity corresponding to prod_map_toList. A text search for the additive name alone is not evidence it is absent.
- Init/Data/List/Pairwise.lean, blob b5c871145893536bb158d5d18de06fedb5ac1fb8: Pairwise.take has an implicit index and explicit pairwise proof. nodup_append exposes the four membership binders plus inequality; chosenFirstOrder_perm's introductions match this core theorem rather than mathlib's separate disjointness variant nodup_append'.
- Init/Data/List/Nat/TakeDrop.lean, blob 2757caac37b53c98654b1d86e5f656352d54635a: length_take_le takes the index and list explicitly, length_take_of_le takes the inequality proof, and take_add has the prefix-plus-dropped-prefix orientation used in the capacity argument.
- Init/Data/List/Lemmas.lean, blob 519a54b75079a3acb036a212f7303f8d497ecba1: not_mem_of_not_mem_cons takes the negated membership proof. The filterMap argument uses that form. The previously reported mem_cons_self/not_mem_nil arity failures are not introduced by these files.
- Mathlib/Data/Nat/Size.lean, blob 799901e248a4699e09db72ae7f4e77589c182a59: despite its name, size_eq_bits_len is oriented n.bits.length = n.size; size_le is n.size ≤ width iff n < 2^width. Thus the existing forward rewrite in fromBinaryBits_width_le is correct. No direction reversal is justified.

The relevant signatures above were inspected at the intended primary-source pins. No unsupported API rewrite was made merely to produce a change.

## Remaining decisive obligations

These finite-carrier and signature checks leave the full compatible package/elaboration/kernel/dependency acceptance track open. They do not instantiate EncodedSourceHardness or provide the all-word external structured-Code-to-TM2/codec bridge. The required compiler claim for a fixed external program may have a code-dependent polynomial; no uniform polynomial interpreter in variable program-plus-input size is claimed here. Exact encoded-source hardness, its operational adapter, and upstream closure/version compatibility remain distinct obligations. The original stochastic cellular identification targets remain open.
