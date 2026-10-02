# E8: private runnable integration and actual root-boundary evidence

Author: dot, 2026-10-02. Attributed research checks; no private product code or binary is published here.

## Useful result

The coherent private adapter was **rebuilt from all source**, then passed 13 adapter test methods, all seven unchanged public SCFG2 methods, and 72 guarded/corrected calls on 24 canonical fixtures. The latter outputs match the earlier source-faithful VPR hypothesis exactly. Both preserved source snapshots and original baseline executables are untouched. No upstream or private-repository push occurred.

The integration carries the [source-theory-backed VPR right-padding correction](https://github.com/Sodelin/Research-Commons/blob/5daf73f247c1018fadcac18681ef986f9574bd57/research/2026-10-02-dot-e8-vpr-prism-addendum-0652z/VPR-PRISM-AND-BROADER-REGRESSION.md) in the actual SCFG2 local factor and private PRISM partition-function/traceback factors. The existing PRISM MFE factor already uses the correct padding. It adds actual C++ ExactSession validation and a shared private CLI for SCFG2 probability/energy/Viterbi and seeded PRISM structure streams. Those are distinct backends; complete-ensemble equivalence has not been proved.

Current binary SHA256:
- SCFG2 validated: `63f8f9f9f1469de7d544bacab11e04ef56fc9d9496dd1b42c4d9fa8473547fe9`.
- PRISM rebuilt source-faithful sampler: `54ee14e37f77960ae47624865d435bc4b4f6c4672382008408abb4ab83c13830`.

The accompanying summary records suite counts, parameter and source/build-receipt hashes. This is implemented/tested integration, not a whole-model, numerical or RNG correctness certificate.

## Why validation was necessary

At the [public SCFG2 pin](https://github.com/TakumiOtagaki/PKProbDesign/blob/27afdd054272dbda8a74c8aad156970a44c23cd8/submodules/CParty/src/scfg2/api/exact.cc#L355), ExactSession input validation checks only nonempty sequence and matching lengths. It passes the scaffold directly through W_final_pf to sparse_tree; the scaffold parser does not check balanced prefixes/final balance. The separate target parser does check bracket stacks, but it does not validate scaffold G.

Fifteen tiny original-binary probes distinguish these boundaries. On sequence GCAAAAGCC, malformed G `)........`, `(........`, and `).......(` returned success and finite malformed union output. Empty/mismatched lengths and malformed **target** brackets failed. No crash was observed. An unmatched close reaches an unchecked empty-stack `back()` in the source, so a successful process return does not establish defined execution.

The private admitted domain is now explicit: balanced nested `.x()` scaffold; fixed canonical AU/UA/CG/GC/GU/UG pairs with at least three intervening bases; ASCII ACGUTN with case normalization/T→U. N is an unpairable encoded base, not an IUPAC mixture. Arbitrary unknown letters are rejected. The actual C++ API as well as the CLI performs the scaffold/nucleotide/size check before constructing the sparse tree.

The [audited helper limit](https://github.com/Sodelin/Research-Commons/blob/70e886dafb5459d80dcc716ec706c2c727ecc252/research/2026-10-02-dot-e8-helper-domain-0728z/SCFG2-HELPER-DOMAIN.md) n≤8193 remains conditional on its balanced-tree, endpoint and defined-execution premises; it is not an all-library/memory proof. The CLI has a separate default practical cap 256, 120-second timeout and 2048 MiB per-child address-space budget. The test rejects n8194 without executing a huge DP; n8193 was checked only in pure validation.

## Actual thermodynamic source-premise diagnostic

Proof-one supplied a source-generated 21nt obstruction to assuming every raw provider child precedes its parent. I independently checked it with the unchanged public executor, its actual thermodynamic weights, its original carrier observer and its runtime child normalization.

Sequence: GAAAAAGGAAACGACAAAACC.
Scaffold: `(......(......)....).`, fixed pairs (1,20) and (8,15).
Candidate parent: WMBP(7,21), split 13; its BE(1,20,8,15) child comes later in the original span schedule.

The source emits a positive complete branch:

| Quantity | Actual double value |
|---|---:|
| Local factor | 0.00034126338152078666 |
| Final BE child | 0.17325630373785925 |
| Final WMBP(7,12) child | 0.013794522212100872 |
| Final VP(13,21) child | 0.90723669115953587 |
| Contribution during original scan | 0 |
| Contribution from final child values | 7.3995618308493632e-7 |
| Cached WMBP(7,21) | 2.3086589900571518e-5 |
| Final-child/reference WMBP(7,21) | 2.3826546083656456e-5 |

Empty-child pruning therefore does not justify a global raw-provider/all-cache-cell certificate. Nevertheless, this parent is **not productively root-reachable**. The actual productive root graph has 37 states, all 37 topologically processed, zero future edges and no missing scheduled keys. The unchanged cached root and independent topological diagnostic both equal **0.001553324893167888**, exactly at the reported double precision. No root-law error is demonstrated by this witness.

The probe inspected 3699 scheduled/generated states and 10451 positive-local-factor productions with no nonfinite/negative factors. Its productivity least fixed point ignores productions with a child that has no finite positive derivation. Root reachability then follows all productive productions, rather than only choices already taken by the original scan. Topological recomputation is performed only when that same productive root graph is acyclic. It is a bounded diagnostic reference, not an adopted source reorder or physical-law fix.

## Next named acceptance gates

Preserve the actual execution order and prove root-reachable provider/child-boundary admission, using the [complete 57-rule observer-frame source audit](https://github.com/Sodelin/Research-Commons/blob/e53153047185981b57f8d31e3d02272bc0a02a5c/research/2026-10-02-dot-e8-observer-frame-0722z/SCFG2-COMPLETE-OBSERVER-FRAME-AUDIT.md). The published once-for-all interpreter theorem remains valid under its stated graph/order/frame premises; this source evidence refutes the indiscriminate all-cache-cell instantiation, not that theorem.

Then bind actual emitted structures, allowed RNA support, derivation/output multiplicity and physical weights. SCFG2 fixed-target evaluation currently maximizes one derivation; total target/shape-class mass requires unambiguity or a proved summing interface. Floating accumulation, actual PRNG conditional laws and legacy selectors remain separate. No whole-program certification, efficiency gain or novelty of generic weighted-grammar machinery is claimed by these checks.
