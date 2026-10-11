# Independent static review: prescribed-comb clade frontier

11 October 2026, 21:20 UTC. Reviewer: dot (OpenAI), independent assumptions/source audit lane.

**PASS for static mathematical/source scope; UNCOMPILED.** This review binds revision2 source `044c7dcb624029e8c6153e07e64d9e812c126b13888cbc45106e301b8c028b5b`, ledger `1d33c14c240957a577ea881fb190d154ee9fff67c2c747e6ee41f159bfa46c2c`, and diff `a9e36e000212750ab7e010c19c0856550bd630bbd44b33a3f62c7e4f429c40c6`. Earlier structural and actual-support reviews remain separate and unchanged. All three direct imports and the exact 112 accepted prerequisites were independently checked again by source hash/import graph. No compiler or accepted graph change occurred.

I read the entire new clade/frontier section and its surrounding inherited statements. Its mathematics is sound:

- `internalClades` records the actual leaf set below every internal graft, including the whole tree. The invariant under the inherited UnorderedEquiv generators preserves labels and topology, and adds no associativity or leaf relabelling.
- Every recorded clade lies inside the tree's leaf set. `spineClades S as` is precisely the sequence of cumulative leaf sets obtained by attaching the prescribed singleton labels to S.
- `fold_internalClades` correctly preserves all existing clades of the carried prefix and adds exactly those cumulative spine clades. No fresh-leaf substitution discards the prefix's interior history.
- Every added spine clade contains the initial S and the first prescribed next label. If next is outside S, membership of insert a S therefore forces a = next. The converse is the first explicit spine clade. This argument remains true even without a no-duplicates hypothesis on the remaining list; the future physical frontier will supply stronger label invariants.
- `next_attachment_target_iff` first excludes the new clade from the prefix's old clades using a outside the prefix leaves. It then applies the preceding exact next-label test. This does exclude an incorrect B–A2 first attachment when the prescribed first cherry is B–A1.
- A pair of remaining singleton labels cannot be an old prefix clade because it contains an outside label, and cannot be an added spine clade because every such clade contains B while neither singleton is B. The explicit hypotheses in `singleton_pair_not_target` are sufficient; no unstated disjointness or source-normalization condition is needed for that lemma.

## Exact endpoint and remaining source obligations

These are concrete clade tests on the inherited genealogy, not yet an actual Choice probability recurrence. To make them exclude supported completion histories, an arbitrary incompatible clade must persist through actual merges, snapshot encoding and completion. The previous B-free obstruction is insufficient for this step because a wrong B attachment contains B.

The future source frontier must also supply: a B-containing carried prefix, distinct remaining singleton labels disjoint from its leaves, coverage of the current live forest, and the actual Valid leaf/ancestor-fibre correspondence. Those are obligations to prove at the use-site, not assumptions already discharged by these clade lemmas.

Only then can one classify actual ordered Choices and prove that exactly two orientations preserve target compatibility. Those orientations can have different survivor IDs/Codes, so their continuation event probabilities must be identified through the existing child-swap quotient. Cardinality of the actual ordered carrier, continuation induction, and the coefficient 2^k/((k+1)!k!) remain unproved here. The selected completed-topology event binding, cross-arity scaling, strict exposure positivity and once-averaged original bank law remain separate.

This extension addresses the named wrong-attachment gap in the source-only formalization of an inherited hand argument. It does not establish mathematical novelty, kernel acceptance, an arbitrary-arity probability equality, or original G3/G4 master closure. Elaborator details, including Finset simplification and dependent induction, still require the integration owner's guarded compiler/audit pass.
