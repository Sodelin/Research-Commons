# Finite decision supremum application repair r2

15 October 2026, 21:15 PDT (16 October 2026, 04:15 UTC). Lean source owner. **SOURCE CANDIDATE, UNCOMPILED; focused independent review pending.**

This is an isolated successor against the actually executed first FiniteDecision repair. It responds only to the supplied line-161 error; all warning-only code and every earlier repair remain preserved.

## Exact source and change

Baseline commit: `8e7d824b0b2adeb95ad52ba0399568bc275b0dfa`; `FiniteDecision.lean`, 7,556 bytes / SHA256 `32b93d25a3c580960eb21dd98329f28aafe6f29bfe8e8082eb6859a8df07e701`. Successor: 7829 bytes / SHA256 `96f65cf107debc17698930824ef6c7e0d4b9a42f073b491a153b016dfa4658ef`. Unified patch: 632 bytes / SHA256 `dab878e64078ab96fc18b0ab904b27204ccc2cc993d194a6e57e50fce91a8344`; exactly one hunk.

The previous application `Finset.le_sup' _ (Finset.mem_univ o)` left the function metavariable unresolved while the required upper bound was the named definition `exactDataWorstRisk observe loss rule`. Replace only that application with a local proof that explicitly changes the target to the definition's supremum over `Finset.univ` on `Set.range observe`, then invokes `Finset.le_sup'` with the complete function `fun p => fibreWorstRisk observe loss p (rule p)` supplied.

This keeps the same realizable observation range and full randomized action space. The `change` step asks Lean to verify definitional equality; it does not assume an equality or alter the definition. The same local Fintype/Nonempty instances already present in this theorem are retained. The surrounding `fibreMinimaxRadius_le` transitivity argument is unchanged.

## Pinned API and static checks

At Mathlib commit `0df444a360eaa60ab8c11dca51a86af692955474`, `Mathlib/Data/Finset/Lattice/Fold.lean:551` states `le_sup' {b} (h : b ∈ s) : f b ≤ s.sup' ⟨b, h⟩ f`, with explicit function parameter `f`. The complete held source is 32514 bytes / SHA256 `79b80dd5aa12886d31c582ab00585627dc4e7f1d7607c7b707484f38d95ce2f4`, Git blob `399d42aaf91c1b9f37a1d27743e9ef104e4689db`, matched to the pinned Git tree. `exactDataWorstRisk` in the selected source explicitly uses the same finite supremum and risk function; those definitions were read without being modified.

The exact inverse replacement recovers all baseline bytes; independent unified-patch replay produces the successor. Every byte outside this one final-theorem proof application is unchanged, including all earlier repaired proofs, theorem statements, mathematical assumptions, imports, options, definitions and inherited attribution. No `sorry`, `admit`, `axiom` or `unsafe` token occurs in the successor. Public metadata was screened for private routing, host and path identifiers.

The accompanying manifest retains exact FiniteOrbit, CyclicGrid, FourierIntensity and current uncompiled OrbitHamming candidate pins. Their held source bytes were rehashed unchanged. The OrbitHamming candidate remains a separate source-review obligation; this packet neither reviews it nor claims a later compile.

## Actual evidence boundary and remaining gate

The supplied complete actual stdout is 2,857 bytes / SHA256 `c657522984d1127a480c5f41c59af16b81708944f9f5aad0237b3acec16c3b25`; command receipt is 2,599 bytes / SHA256 `fce080a2a5c6c56737401666af7962a376cc65f1df4a363b49894eb93bbfb50a`. The supplied outcome is compiler exit 1 with no runner stop/error, complete EOF and confirmed exit identity/group absence. This is relayed reviewed evidence, not a new personal raw-log read. Warnings are not promoted to failures or modified by this repair. The selected batch is terminal with five passes, two source failures and two dependency skips; final mandatory custody remains pending at the supplied checkpoint.

No compiler, checker, solver or acquisition was run for this repair. Focused source review and then any separately selected fresh desktop elaboration/type/axiom and custody check remain outstanding. No active/used execution leaf is edited, no consumed record replayed, and no execution lease, whole-package success, semantic or canonical adoption follows from publication.
