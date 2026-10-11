# Private erased Selected-prefix observer proposal

Codex Rust implementation role. Source-only proposal; no compilation, target import, test, native/reference execution or public export. It borrows frozen `source_selected_prefix.rs` 46172afa and leaves its source, five passed tests and public 443a binary unchanged.

The required data exist. `prefix::Table` exposes complete Selected states, an exact shared-prefix DAG, final path polynomials, immutable bank/order metadata and a validated canonical Snapshot range witness for each state. Its views contain ordered genealogy and original location for EVERY local Copy plus every original V register slot. It consumes that table directly.

## Exact callable interface

A future private harness includes the unchanged recorder as module `source_selected_prefix` and this new sibling module. No shared lib/main/Cargo edit is proposed.

`observe(&prefix::Table, &Spec) -> Result<Decision, Error>`

`Spec = {original_hybrid, old_prefix_len, limits}`. The named original hybrid must be COMMON. The Old cut includes the entering view and each of the first `old_prefix_len` supplied-letter endpoints; it cannot exceed the input endpoint or the position BEFORE that hybrid's original Enter letter. The final forest/register comes from the input table's endpoint, which may lie after the Old cut. This makes the two times explicit. Using the entire entering/endpoints vector means selecting Old cut equal to the input prefix length, where the private-read guard permits it.

On TABLE, getters retain a borrow of the exact input table, unchanged full polynomial variable bank, named hybrid/vertex, projected Selected states and shared Old-path nodes. Each joint row is `(old_leaf, final_forest_register, polynomial)`. `record_views(old_leaf)` returns exactly the entering erased view and ALL declared Old endpoints in their literal input order. A nonterminal Old leaf is rejected. The full final register contains every original V slot with only the named vertex false; the forest uses the existing `forest::Forest` type and supports zero, one or multiple carried components. It is not completed-one-tree readout.

Only output clones are erased. Input witnesses, stored seeds, cached conditional rows, gamma coordinates and all transition inputs remain immutable. Existing `Initial::Natural` still occurs once in the already constructed recorder table; that recorder then uses one-letter `Initial::Conditional` calls. The observer invokes neither path and reports zero added child-law queries. It neither sets gamma to zero nor applies the old-g complement again.

## Pushforward definition and representation

For selected view v, let E_h(v) preserve genealogy and population while resetting only register[h.vertex]. The final forest/register F_h(v) retains that erased full register and ALL unranked carried trees. For every source row p with entering/endpoints path, the coefficient contributes exactly once to:

`( [E_h(v_0), ..., E_h(v_oldcut)], F_h(v_final) )`.

The output coefficient is the exact sum over that joint fibre. Shared nodes are interned by `(projected parent PathId, projected complete Selected state)`. Equal projected final states do not identify different Old vectors. Endpoints AFTER the explicitly declared Old cut are forgotten by this declared observer, while the complete latent input DAG remains available unchanged. Final forest/register keys additionally distinguish the requested final object. No factor for copies, ancestral blocks, representatives or graft orientations is introduced: source-word/recorder rows already contain their coefficient fibres.

The unranked forest calls the existing `population::unordered_forest(context, range_witness)`; no second tree-canonicalization algorithm is written. It selects each live carried component once, recursively forgets child order, retains all labels, and sorts by least GLOBAL label. Old genealogy stays ordered and uses local Copy IDs. `context.global_labels` is the explicit bijection to decode final global IDs; it need not be increasing and must not be interpreted as a local array index. Equal erased selected states are collision-checked for equal forest/register outputs, so a contradictory witness cannot silently define the quotient.

Validated Snapshot trees partition Copy into disjoint fibres; each copy's Selected genealogy is its fibre's complete tree. The forest therefore depends on the full Selected view rather than its representative. This source inspection is not a checked native/typed quotient theorem or literal Code-history binding.

## Accepted providers and missing correspondence

The freeze pins all exact bodies and acceptance inputs. SourceProgramTransport d009 `actual_program_step_projection` and G2SourceFiniteHistory19924449 `history_projection` transport a complete selected entering/endpoint record. SourceForestSilentPruning86f61cc8 and SourceFiniteProjection09398c92 describe that projection; they do not prove Code injectivity. PrivateRegisterErasure b9c845b5 and PrivateRegisterHistory b1226729 erase exactly P={h.val} at every recorded position, retaining correlated Old under NoPrivateWordRead. PrivateSeedHistoryFactorization8bba9735 binds the original once-drawn seed. UnrankedGenealogyObservation1ee53650 and ContextualForestReplacementfeab5f5e provide the full label-preserving carried-forest quotient.

Accepted Natural141 source3fc defines erasedRecord and erasedForestRegister and permits arbitrary Old readers of the erased Code record. This proposal supplies the honest smaller specialization where Old factors through the ENTIRE erased Selected entering/endpoints vector. It does not support arbitrary literal-Code Old, whose ancestry/representative/dead-option fields are absent.

Required typed bridges: selected encoding commutes with single-site Code erasure; existing canonical forest equals typed rootForest after the explicit label bijection; every input polynomial coefficient/conditional row and initializer corresponds to the typed source step/history; and the exact supplied-letter list equals the required original compiler prefix/bigon word. Endpoint phase-permutation equality is insufficient for arbitrary intermediate Old columns. The finite native cut guard does not certify typed NoPrivateWordRead or calendar provenance. The final endpoint need not be a completed root, and this observer does not infer the local all-copy-at-hybrid, arm-exposure or baseline/residual premises of Natural141.

All literal-Code Old, native/source refinement, source admission, timed-history, compiler-order, NoPrivateWordRead verification, independence and COMMON factorization flags remain false. This proposal computes no baseline/residual epoch, identity physical edge, passive observation menu or full solver.

## Bounds and refusal

Default/hard count maxima: input states8192/nodes65536/rows4096/terms65536; projected states8192/nodes65536/joint rows4096; new live term slots131072, exponent cells8388608, rational additions1000000. Rational bits default4096/hard65536; the input recorder's exponent4096 bound is retained. Caller count limits may be zero or lower; above-hard limits, invalid hybrid or a past cut beyond the private read are INVALID_INPUT. Checked usize arithmetic rejects overflow.

Input collection counts and total raw term contributions are charged before mapping/state collections or joint sums. Per-state probes have fixed existing four-copy/32-vertex bounds. Every state/node/row insertion and exponent-key allocation is checked before collection growth. New term-slot accounting includes output rows AND the scratch mass polynomial. Exact coefficient operands and results are bit-checked around each addition, including the constant1; temporaries have at most twice the bounded operand bits plus one numerator bit. Exact zero coefficients/rows are removed, and final formal mass must equal1.

UNKNOWN contains only limit metadata and observed work, with no partial state DAG or table. Work/exhaustion is informational, not a source or infeasibility certificate. Runtime guards and typed bank/dictionary binding await validation; hard maxima do not claim generic performance.
