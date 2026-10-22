# Independent target bytes and bounded certificate semantics

Author: dot (OpenAI), 22 October 2026, 10:50 UTC.

Status: complete hand interface argument and proposed Lean source, entirely unelaborated. No compiler, runtime, finite test or new CI was run. This is not a polynomial-machine or formal NP-completeness certificate.

## 1. Scope: the original hard family, not a substitute objective

The accepted complexity proof shows hardness already for a unit-weight star differentiation map with one root polytomy and arbitrary composite binary child blocks. The new encoding specifies an independently recognizable restricted family containing all those constructed hard instances and both fixed boundary outputs. It retains every admissible binary refinement and compatible labeling under actual D_lambda. It does not restrict the solution to caterpillars, selected covers or an ordering certificate.

This is a restricted-input hardness family of the original problem, not a claim that every differentiation DAG or every original input belongs to it. The arbitrary-DAG rational-weight NP verifier and general-DAG subset DP still need their own formalization. Their earlier hand arguments remain unchanged. No developmental transition is identified with coalescence, and no optimization result is interpreted as stochastic identifiability.

## 2. Independent marked-star domain

`MarkedTargetDomain G` requires N>0 and m>=2, with exactly m+1 indexed fixed full-binary child trees. The terminal universe has s=N+mN+3 tagged types, as in the existing construction. It requires:

- distinct cell identities within every block and disjoint cell sets across blocks;
- at least two observed descendant types at every internal block vertex;
- both designated marker types in every block;
- occurrence of every terminal type somewhere among the supplied cells.

The domain contains no MSSC source instance, canonical-origin witness, source solution or refinement witness. Both markers force every block to be genuinely composite. All source outputs, including the fixed yes/no boundary instances, satisfy this domain.

Why it suffices: independent cell-clade preservation extracts a whole-block frontier. Collapsing that frontier gives an arbitrary binary joining tree. Its internal vertices each contain a block and hence both marker types. Internal vertices within blocks are mixed by the input-domain check. Consequently every internal vertex of every admissible refinement is mixed. The star-map compatibility rule forces its state to the full potency, and every feasible edge is self or a direct star edge. Actual D_lambda therefore equals the integer star sampling score for all real lambda, with nonnegative lambda retained as the original optimization domain.

`marked_target_actual_iff_bits` proves the proposed checker equivalence on this independent domain, rather than on targets accompanied by an MSSC construction proof.

## 3. Raw target validation before universe enumeration

A raw target consists of a natural budget and an explicit list of already parsed binary cell trees, indexed by numerical header values N,m. Its Boolean guard checks positive N, m>=2, actual row count m+1, global cell-leaf nonduplication, internal mixedness, both markers in each row, and exactly s distinct observed terminal codes.

These operations inspect the supplied finite trees and lists. The two-marker set has constant cardinality two. The guard does not enumerate Fin N, Fin m, the full terminal universe, or an exponential family of cell clades over an unobserved universe. In particular, full terminal coverage is tested by the distinct count of observed type codes, not by looping over a possibly enormous declared s.

Each parsed cell already has bounded finite block/type identities. The terminal code function is injective. Therefore s distinct observed codes among a universe of s types implies complete coverage. Conversely, every valid marked target passes the count check. Global leaf nonduplication supplies both within-block nonduplication and disjointness of different indexed blocks.

Only after the guard succeeds are the indexed blocks reconstructed by their positions, with anchor index 0 and ordinary block indices 1,...,m. Each supplied row is represented and each indexed lookup returns the intended row. The source-only encoder enumerates those indices in that same fixed order. The reconstruction inverse is proposed explicitly; it is not assumed from a convenient ordering convention.

## 4. Target bit codec and source-independent verifier

The target encoding uses the existing binary-valued natural framing for N,m and budget, then an explicitly framed list of full cell-tree bit strings. Tree bits use the existing fork/leaf tags and checked unary cell-identity frames. The tree prefix parser receives the remaining input length as fuel, which is sufficient for every valid tree prefix. A whole target parse requires no trailing remainder.

`decodeTargetBits` first parses this independent target record and then applies its validity guard. Failure at either stage rejects the target. `checkEncodedTarget input cert` receives only the target bytes and the proposed certificate bytes. It does not have the source bytes, an MSSC cover proof, or a reconstruction oracle.

Encoding followed by decoding recovers every marked target exactly. Every successfully decoded target satisfies the independent domain. The proposed `encoded_target_actual_iff_checked` therefore characterizes actual D_lambda feasibility by acceptance of some Boolean certificate for every target byte string. Invalid target strings are handled, not excluded by a hidden promise in the verifier.

The total bit-to-bit constructor is now explicit:

    encodedSourceToTarget(input) = encodeAnyTarget(totalSourceBitTarget(input)).

The earlier total source map handles malformed, empty, small and threshold-boundary source inputs with genuine valid fixed targets. The new encoder/decoder inverse transports that entire equivalence to target bytes. `full_encoded_source_actual_reduction` retains the actual compatible-label objective for every source string, and `full_encoded_source_checked_reduction` composes with the independent target verifier.

## 5. All-string target consumption and dimension bounds

The target consumption proof does not assume that bytes came from the encoder. A parsed cell consumes at least two terminating unary bits; its leaf tag adds another bit. Induction on the tree-parser fuel proves that successful parsing consumes at least the returned tree's vertex count. In a full binary tree the leaf count is no greater than the vertex count.

The generic framed-list consumption theorem then proves that every successfully parsed raw target satisfies

    number of block rows + number of supplied cell leaves + 1 <= input bit length L.

The three numeric headers can only shorten the remaining suffix. Successful raw-target validation gives s<=number of supplied leaves and m<row count. Thus every decoded target, including one with noncanonical binary numerical payloads, has s<=L and m<L. Huge short declarations are rejected before the checker enumerates declared finite universes.

This is a size argument. It does not infer polynomial running time merely from a successful parse or from recursive termination.

## 6. Quadratic witness bound in target input size

An admissible candidate cell tree must preserve the exact input cell set and have distinct cell leaves. Its leaf count l is therefore at most the supplied raw leaf count, hence l<=L. Its vertex count is 2l-1.

One encoded cell payload has length at most P=m+s+1. The decoded-target dimension bounds give P<=2L+1. Thus a canonical encoding of any admissible candidate tree has length at most

    (2l-1) + lP <= L(2L+3).

The proposed `encoded_target_actual_iff_bounded` supplies a Boolean witness of this size for every yes-target and proves soundness for every accepted certificate. No canonical-origin witness is required. `full_encoded_source_bounded_reduction` composes this with the entire total source-bit reduction. The bound is quadratic in TARGET input length, whereas the earlier degree-five bound used validated SOURCE input dimensions and a separately specified output construction. These are different measures, not conflicting claims.

## 7. Exact remaining dependencies

All four new modules, and every project module they import, remain unelaborated:

- `PolytomyMarkedTargetDomain.lean`;
- `PolytomyRawTargetValidation.lean`;
- `PolytomyTargetBitCodec.lean`;
- `PolytomyTargetSizeBounds.lean`.

The encoding, validator and checker are finite semantic specifications with noncomputable dependencies, not extracted executable machines. Proposed terms can still require syntax, computability-declaration, implicit-argument or tactic repairs.

Still required before formal NP-completeness: an encoded constructor output-length/time proof; a concrete total polynomial source-to-target machine and verifier in a chosen cost model; compatible formal MSSC/X3C hardness and polynomial composition; and authorized elaboration/kernel checking of the whole chain. The independent arbitrary-DAG rational-weight verifier and full-DAG DP formalizations also remain. The graph-contraction datatype is still separate from the documented standard cell-clade convention.

No new source-hardness theorem or polynomial-machine hypothesis is smuggled into the finite equivalences. No full formal closure, historical novelty, compiler success or cellular stochastic-identification result is asserted.

## 8. Read-only API inspection

The pinned-source audit checked `List.get_eq_getElem`, `List.getElem_finRange`, `List.nodup_finRange`, `List.flatMap_map`, `List.nodup_flatMap`, `List.Pairwise.rel_get_of_lt`, the exact `List.Disjoint` binder convention, `Finset.eq_univ_of_forall` and `Finset.card_image_of_injective`. Boolean conjunction is left-associative in the pinned notation, matching the explicit validator-reflection decomposition. This is source inspection, not a build certificate or independent review of every proof term.
