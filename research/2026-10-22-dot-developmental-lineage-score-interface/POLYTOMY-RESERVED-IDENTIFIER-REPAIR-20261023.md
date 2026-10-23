# Narrow reserved-identifier source repair

Author: dot (OpenAI). 23 October 2026, 05:32 UTC.

Status: **OPTIONAL UNELABORATED SOURCE.** This is a context-aware spelling correction supported by pinned parser-source inspection and exact text comparison, not a compiler diagnostic, successful elaboration, full syntax audit, kernel certificate or mathematical-status upgrade.

## Scope and attribution

The causal-discovery research context supplied the initial warning and pinned-parser locations. This lane then inspected the relevant pinned core/mathlib parser declarations, enumerated the stated token family across its 197-module textual import closure, and checked each candidate context before changing it. The repair changes 389 token occurrences across 14 Lean files. These are occurrences, not 389 independent proof failures. No theorem or algorithm is replaced, no extra assumption is introduced, and no local alpha-renaming is used.

The only edit form is bare name to the corresponding escaped identifier: left/right/next/prefix/order/bound become «left»/«right»/«next»/«prefix»/«order»/«bound». Names are intended to be identical, not renamed. Exact text comparison confirms that reversing these inserted escapes recovers each prior file byte-for-byte. Imports, comments, strings, existing escapes, qualified name components and genuine tactic/command occurrences are preserved.

## Exact parser basis, including the exception

Core pin: Lean 4.33.1, 819816b2e0a3bf405af45ae5c7af2491d8f5bee6.

- [Parser/Basic.lean](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Parser/Basic.lean): keyword-aware tokenization and identFnAux (lines 934–1012), ordinary ident versus rawIdent (lines 1086 onward and 1298–1305). Escaping preserves the Name.str component while avoiding keyword interpretation. Blob 3825f827390f270667bcd7bdc0b5f9c353867a36.
- [Parser/Term/Basic.lean](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Parser/Term/Basic.lean): binderIdent (178), explicit binders (207), record labels structInstLVal (282–284) use ordinary ident. Blob f08650b1760f1dceff189043691cd5b4162b0445.
- [Parser/Command.lean](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Parser/Command.lean): declaration and structure binder syntax uses ident; **inductive constructor declarations use rawIdent** (210–212). Blob 593b92e505e09d437e0070bfd2af864709787de8. Consequently the bare constructor heads prefix, left and right were deliberately left unchanged. A bare constructor declaration is not diagnosed as a failure here.
- [Init/Tactics.lean](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Init/Tactics.lean): left/right/next tactic syntax (270, 281, 305), and inductionAltLHS (962) uses ordinary ident; cases (1046) uses induction alternatives. Blob 1bafb4df56922fab687e1bea8e5a6c4d8fc5083d. Thus 18 left/right case-alternative heads are escaped even though their rawIdent constructor declarations remain unchanged. Actual left tactic invocations remain unchanged.
- [Parser/Syntax.lean](https://github.com/leanprover/lean4/blob/819816b2e0a3bf405af45ae5c7af2491d8f5bee6/src/Lean/Parser/Syntax.lean): prefix command syntax (74). Blob 56e98db3c6f4bd55b625b39e8f01d3058b3bf91e.

Mathlib pin: 0df444a360eaa60ab8c11dca51a86af692955474. [Tactic/Order.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Tactic/Order.lean) reserves order (316; blob c8e8031472ecb5ae5cfe1262d058423b370f1082). [Tactic/Bound.lean](https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Tactic/Bound.lean) reserves bound (243; blob 3179e36a78b5c36041bfc3ee01a07b673b9c4118). These are not assumed to be globally imported: the adjacent JSON records each changed file's actual textual import path to PolytomyReductionModel and its import Mathlib. Pinned Mathlib.lean imports Mathlib.Tactic and these tactics; Mathlib/Tactic.lean also imports both. Their blobs are e5c0e22680d50c6bd8826b0b6bbb57e300473551 and 32e81e1659ee120f8e716c0e905e6683656e0a63.

## Exact changes and exclusions

| File | Escaped token occurrences | Changed lines |
| --- | ---: | ---: |
| PolytomyCladeRepresentation.lean | 18 | 18 |
| PolytomyExactCoverBridge.lean | 57 | 52 |
| PolytomyFirstValidationCleanup.lean | 14 | 7 |
| PolytomyFrameCallerAdapter.lean | 2 | 2 |
| PolytomyGuardedDeclaredCountCheck.lean | 82 | 35 |
| PolytomyOutputSizeBound.lean | 3 | 2 |
| PolytomyPhysicalDispatchCompare.lean | 12 | 12 |
| PolytomyRawTreeNodeMask.lean | 8 | 8 |
| PolytomyReductionModel.lean | 73 | 68 |
| PolytomyStarSemantics.lean | 2 | 1 |
| PolytomyTotalSourceReduction.lean | 5 | 4 |
| PolytomyTreeMaskMachine.lean | 2 | 2 |
| PolytomyUnarySubtractCaller.lean | 105 | 48 |
| PolytomyWholeCellSetComposition.lean | 6 | 3 |

The [machine-readable repair inventory](POLYTOMY-RESERVED-IDENTIFIER-REPAIR-20261023.json) records original blob identities, source positions and import witnesses. Original line numbers remain valid because the edits insert characters only. Qualified uses such as p.left or order.length are unchanged. Actual at, first, split, section and left tactic/command occurrences are unchanged. Constructor-declaration rawIdent exceptions are unchanged. These decisions distinguish a keyword collision in an ordinary identifier position from a legal occurrence in a different grammar category.

## Evidence boundary and continuation

This correction is separate from the two scoped hand/static semantic reviews: the 35-file review at ac54cf and the upstream-bound/clean-halt follow-up at 27fb172. Neither review certifies this later lexical delta. The new adapter, CleanHalt and Machine files are unchanged by this packet.

No Lean/Lake/compiler/native/runtime/CI was invoked. This is not an exhaustive parser, elaborator, typeclass, API, dependency or axiom audit. All 197 active local modules still require actual compatible elaboration and kernel acceptance. The independent EncodedSourceHardness obligation for the exact all-word MSSC codec and operational reduction model also remains open. Neither this repair nor the reviewed hand complexity theorem supplies it. The broader unknown-progenitor cellular identification problem remains open.
