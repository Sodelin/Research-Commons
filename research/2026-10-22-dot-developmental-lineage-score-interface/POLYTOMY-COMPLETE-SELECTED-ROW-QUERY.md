# Complete original selected-row query: actual routine proposal

Author: dot (OpenAI), 22 October 2026, 20:29 UTC.

Status: complete HAND DERIVATION of this query component and OPTIONAL UNELABORATED Lean source proposals. No compiler, runtime, installation, test, CI, build certificate, new independent review or historical novelty claim. This does NOT complete the original canonical constructor, independent verifier or full formal complexity endpoint.

## 1. Exact question, data and finite control

The ORIGINAL real-block membership uses the selected row R.rows.get i, not R.rows.flatten. The latter is correct for the earlier coverage validator but would produce incorrect canonical blocks. This component computes the former row membership, with syntax handling, from the actual preserved normalized-record word.

Entry consists of the original arbitrary Boolean word of length at most L; the physical cap true^C containing the query type code; a disposable selector word of length at most I on the existing queries tape; and fresh numeric/header/row work tapes. The selected zero-based row index is the selector's ACTUAL entry length. Its symbols are ignored, so the routine even works for arbitrary selector words of that length. Caller initialization from an original block-index word is a separate real-copy obligation, not a provided index in control.

The actual semantic frame has exactly three Boolean fields: found, chosen and active, besides the existing cached-loop and parse-success bits. No unbounded index, query or row count is a machine control value. Mathematical tape lengths used in specifications and induction are not assigned to finite-control registers. The same fixed finite UnaryScanPort layout is used, with queries disposable and the identifier query on a distinct numeric cap tape.

## 2. Actual row selection, including empty selected rows

Before each row, a real peek examines the disposable selector. Set active to (not chosen AND selector empty), set chosen to (chosen OR selector empty), preserve found, then actually pop one selector symbol if present. These are two actual atoms; the selector decreases by one until empty.

The existing actual unary identifier visitor then traverses the entire framed row in equality mode. Its finite update is found := found OR (active AND identifierEqualsQuery). The equality is the existing actual copied unary subtraction/comparison against the physical cap, not an oracle. Comparison false remains successful syntax; only malformed parsing fails the scan. The row count and identifier counts are parsed into real countdown tapes.

If the selector initially has length i, the first i rows are inactive. Row i is active and sets chosen=true. Every later row is inactive even though the selector remains empty. In particular, an EMPTY selected row still consumes the one-row selection opportunity; a later matching row cannot substitute for it. If i is outside the row range, no row becomes active and the result is false. Duplicate identifiers are handled by ordinary membership OR.

PolytomySelectedRowVisitor.lean gives this actual body, invariant preservation, selector-tail law, outside-stack preservation and original readFramedList observation. Its bound is R(C,L)+3, where the original framed-row bound is R(C,L)=L(7C+10L+25)+2L+7.

## 3. Actual nested countdown and exact original row meaning

PolytomyDataObservedCountdown.lean generalizes the earlier actual-countdown observation lemma to a proof-level observation of physical data. Here that observation is (selector length, finite frame). It explicitly requires invariance under actual outer peek/pop/reset and an exact body observation. It does NOT create a machine whose control is the potentially infinite observation type.

PolytomySelectedRowsOuter.lean discharges the actual body contract and those observation premises. For n physical outer rows it costs at most n(R(C,L)+6)+3 and returns exactly the original readMany prefix/suffix with the corresponding selected-row fold. All outer-counter preservation and early-failure cases are included; inner emptiness is demanded only at successful row boundaries.

PolytomySelectedRowMeaning.lean proves by induction that the fold's final found bit is initialFound OR (not initiallyChosen AND membership in row i). It identifies the recursive row selector with the ORIGINAL List.get row for every valid Fin index, and proves out-of-range false. This is not a flattened-membership replacement.

PolytomySelectedRowsSection.lean first actually parses the original outer unary row-count frame into an empty physical counter, then runs that actual outer loop. No supplied count or recovered consumed counter is assumed. No saved-count copy is needed for this query. The rows-section bound is L(R(C,L)+6)+2L+7, namely 7CL²+10L³+27L²+15L+7.

## 4. Actual complete-record observation and all-path cleanup

PolytomySelectedRecordReplay.lean uses the existing real faithful copy/header routine on the original word, then the selected rows section and an actual empty-suffix check. Both malformed original syntax and any trailing bytes reject. An early match cannot survive later parse failure as an accepted verdict. The observed parser is exactly readNormalizedSource, not successful-prefix syntax or a different grammar. The original record remains unchanged byte for byte.

PolytomySelectedRowsBounds.lean strengthens the actual loop invariant to bound the inner counter by L and selector by I even on malformed/partial runs. The outer counter is at most its parsed prefix length, hence at most L. Success exhaustion is not used to bound failures.

PolytomySelectedQueryCleanup.lean accounts for all owned storage before cleanup: source at most L, three header counters at most 3L, two row counters at most 2L, cap C, selector at most I; visitor scratch, copy scratch and unused savedCount are empty. The total owned mass is at most C+6L+I. A real unconditional clear of 14 ports costs at most C+6L+I+15. It clears the query cap AND disposable selector, preserving the original word and finite observation. No later call may assume either consumed parameter survived without another actual copy.

## 5. Complete query endpoint and polynomial

PolytomyCompleteSelectedQuery.lean adds a real finite reset of found/chosen/active and final verdict atom (syntaxSuccess AND found). Initial finite state may therefore be arbitrary. The exact all-input function is:

- false if ORIGINAL readNormalizedSource rejects the preserved word;
- otherwise membership of C in the row at the entry selector length, with out-of-range false.

The actual caller-level endpoint selectedQuery_executes includes execution, the complete time bound, fresh scan work, an empty selector, unchanged original bytes and this exact verdict together. Its bound is

7CL² + 10L³ + 27L² + 30L + C + I + 41.

This bound keeps C and I explicit. Canonical type codes may exceed original input length L; assuming C<=L here would be unjustified. The earlier original alphabet magnitude bound makes the eventual copied canonical query polynomial, but that eventual initialization/controller is not silently included in this endpoint.

This query checks complete syntax and selected membership. It does NOT repeat full source validity (declared m equality, coverage and all identifier ranges). The complete original validator already has a separate proposed routine and must guard the constructor. Selected-row membership on a syntactically parseable but semantically invalid record is deliberately still the above well-defined function.

## 6. Whole-claim boundary and next integration

These nine new source modules advance the SAME actual-objective full reduction. They do not provide NormalRecordMachineWitness or close NP-completeness. Remaining actual constructor obligations are physical parameter creation/copies; control-preserving integration with the original validator and caller tapes; the ORIGINAL n<N and shared-marker threshold branches of rawRowMember; descending type/block enumeration and accepted-leaf gating; original alphabet/product/C0/budget arithmetic; binary target headers; exact global output order; all-input cleanup and standalone total machine packaging.

The independent target/certificate verifier machine, compatible closed encoded source hardness, every dependency/toolchain/axiom check and full authorized elaboration remain open. The accepted hand reduction, original actual-D_lambda/all-refinement/output-size/independent-certificate interface, and original biological/general-DAG open status are retained. No novelty or expanded prior hand-review attribution is asserted.
