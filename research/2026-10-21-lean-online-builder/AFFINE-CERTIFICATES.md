# Existing affine engine and checked finite-matrix receiver

The existing native engine is reused, not rebuilt. Source correspondence is
to StrictAffineElimination and G6RationalAffineWitness at the pinned Commons
1138a5b1a281caa00b38e0976db95b586938754b. Their exact complete source bodies
are unchanged. The ordered-list refinement solveList_eq_solveRational is among
the nine selected hosted audits.

The proposed receiver/examples at Rust source commit
80888f68c81468ad6e91df1e8e59b392d27900d4 did NOT pass as written. The new
receiver's unqualified Rel resolved to a different declaration in one simp
list; four literal decide proofs also failed to reduce. The original source
and failed virtual document are retained under lean/proposals/ and
lean/OriginalOnlineAffineCertificateExamples.lean. Their rejected check is not
promoted to acceptance of the original bytes.

A separate proof variant passed actual hosted checking. It fully qualifies
UnifiedLean.G6.StrictAffineElimination.Rel and replaces the four nonreducing
literal proofs with finite expansion and norm_num. Definitions and theorem
statements are unchanged; no native_decide, added axiom or source-row
assumption was inserted. lean/AffineCertificateProofBindings.patch contains
the exact changes. Historical source-candidate comments remain attributed to
the original proposal; this document supplies the later check disposition.

Four selected receiver endpoints are:

- checked_witness_real: the existing exact checker for a supplied rational
  vector implies every ordered original row holds over the reals.
- weighted_eval_zero: zero weighted coefficient sum gives zero weighted
  evaluation for every real vector.
- farkas_infeasible: nonnegative multipliers, zero coefficient sum, and a
  negative combined bound, or a zero bound with a POSITIVELY weighted strict
  row, exclude a real solution of the supplied finite matrix.
- checked_farkas_infeasible: the exact finite Boolean predicate implies that
  same infeasibility statement.

Four additional selected literal checks cover a point in (0,1), x>0 together
with x<=0, refusal of a false exclusion whose only strict row has ZERO
multiplier, and a positive witness for that last feasible matrix. All source
declarations elaborate; only the nine selected names have printed type/axiom
audits. CHECKED-FOLLOWONS.json retains those complete selected types.

The corrected receiver is4134B/SHA256
62d4569e436aadb3202118a818c0ed7635c27a54b8e39b27a1e23188d80b5fc6.
Corrected examples are2606B/SHA256
76d739d0afdbe26d45340681852aa32ff5d3d87dbc91010cd5e0fbce9196cc9d.
The unchanged-body projection is32778B/SHA256
d2d970b069a1423f77b1f8cd6b82d0811fb430b1364a6e7ca56144aebc65a8c6.
AFFINE-SOURCE-MAP.json identifies the original rejected source hashes too.

Actual context is Lean4.35.0/mathlib56a005855ea17e0b0958f73ec801ae140b0a1679.
All nine selected audits have only propext/Classical.choice/Quot.sound and no
errors. Inherited deprecation/unused-instance/simp warnings remain in the
encrypted result. This is a selected single-document hosted check, not native
4.33.1 Lake/object custody or a complete package audit.

The receiver concerns a SUPPLIED finite real matrix. Native parser/binary
refinement, source-chart row admission, nonlinear law constraints, physical
source realization and unrestricted all-size NO remain separate. No canonical
native bridge/profile/whitelist changed. Native record writers remain UNBOUND;
no native compiler, runtime/MCP job or held prefix was invoked.
