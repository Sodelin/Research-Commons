# Full-bank capacity and routing meaning

The source-typed G6 receiver uses the complete original bank
`V ⊕ (Option E ⊕ Hybrid N)`. Its layout is a bijection, so its width is
`|V|+|E|+1+|Hybrid N|`. The [accepted binary census](https://github.com/Sodelin/Research-Commons/blob/539c814ac470fde8147b0e1e6d5307972585b6f8/research/2026-10-01-sol61-head-audit-1956z/G7-EXACT-MASTER-REVIEW.md)
gives `|V|=2n+2h-1` and `|E|=2n+3h-2`. The existing unreduced layout therefore
needs **4n+6h-2 coordinates**. This is a direct size deduction, not a new
Lean check, source-count bound or claim about irreducible information dimension.

| Four-taxon source | Full bank width | Existing transport capacity |
| --- | --- | --- |
| Tree | 14 | Exceeds canonical AFFINE8 |
| One hybrid | 20 | Within unadmitted CHART32 width |
| Two hybrids | 26 | Within unadmitted CHART32 width |
| Three hybrids | 32 | At unadmitted CHART32 width |
| Four hybrids | 38 | Exceeds both existing widths |

The row cap is an additional constraint. With every structural registry
listed once and no extra chronology/exposure/coin bounds, the eight-block
compiler emits `|E|+2n+(|E|+1)+2h=6n+8h-3` structural rows. Repeated registry
entries and supplied interval/equality constraints add rows in their actual
order. Canonical AFFINE8/64 cannot carry an unreduced original G6 full bank
for n>=4. The existing CHART32/128 core remains outside canonical dispatch.
Certified preprocessing can reduce width when it also supplies the relation
lifting its result back to the full original bank. Truncation does not supply
the receiver's exact emitted-matrix equality. Capacity exhaustion stays UNKNOWN.

[ORDERED-BANK-LAYOUT.md](ORDERED-BANK-LAYOUT.md) now records the hosted-checked
generic bijection for these exact four coordinate ranges, including uniqueness
of the ancestral slot. The original-Code instantiation is source-only; exact
captured arrays, source admission, port meaning and row emission remain required.

## One shared bank needs an explicit incoming-port map

The retained [native LAW compiler](https://github.com/Sodelin/Research-Commons/blob/4e556c4ae6225d18fabf30bc7d3347a468749ebc/research/2026-10-10-codex-lean-rust-parity/rust/src/law.rs)
defines `G:h` as the probability of `Hybrid.incoming[0]`. Its literal routes
assign `[forest,empty]` weight G and `[empty,forest]` weight1-G; independent
routing uses G for group0 and1-G for group1. The incoming table is explicitly
replaced by that original hybrid registry pair.

The physical Lean bank instead has gamma=P(original parent1). Thus an adapter
that identifies native incoming[0] with original parent0 must substitute
`G:h=1-gamma(h)`. An explicitly reversed incoming-port map instead permits
`G:h=gamma(h)`. This is a convention relation to prove at the actual registry,
not an implementation bug claim against the unchanged native compiler.
The CHART `COIN:h` interval alone does not authenticate its routing meaning.
The same port/parameter map must hold across the natural COMMON/INDEPENDENT
laws and all supplied rows of one physical source.

Original forcing already has a source supplier:
`UnifiedLean.Source.OriginalFixedIDControls`, SHA256
`5b32ee2edff84d6ef7c75549b55e7368380fcff9dbb3b0cd4397584746bb224d`
at Commons1138a5 source-store. `actual_forced_current_coin_pmf`,
`original_forced_node_compiler`, `actual_forced_hybrid_kernel` and
`actual_forced_owner_route` bind true to original parent1 and route each CURRENT
owner once. Under the index-preserving map above, forcing original parent0
sets native G=1 and forcing parent1 sets G=0. These endpoints represent a
legal intervention while the natural physical inheritance bank remains strict.
The current native LAW request has no mask field; a controlled-law adapter still
needs the exact mask/substitution theorem and original-menu legality. The
existing source lemmas do not by themselves refine a native polynomial parser.

## Source-class and origin boundaries

The original `RootedBinary` fields in SourceNetwork, SHA256
`0e0a2a3ed6bdbbd7242980a6428ebf8ec0ec85d077d2ccf9cd8dfef4e1bd2eb7`,
cover binary degrees, reachability, DAG and root LSA. Required cut-child and
outer-labelled planarity predicates remain additional source-class premises.
The native structural validator and a feasible affine cell cannot silently
discharge those G6/G7 admission conditions. Active exposure/chart coverage,
nonlinear actual observation laws, complete registry/layout refinement and
authenticated process origin also remain explicit.

Exact native sources independently fetched and byte/Git-blob verified at
commit4e556c4ae6225d18fabf30bc7d3347a468749ebc:

| Source | Bytes | SHA256 |
| --- | --- | --- |
| natural_cell.rs | 12724 | 774a26a70f99bdc760fa15835267c6fc0753bb2db0419844d65895b29f1ecf9e |
| protocol.rs | 23633 | 0bcf6e0e099d5983604c8d3e6fe189fbb0431de390b7d0f8c7306bbbced2e72a |
| law.rs | 16506 | e519d232bbea12fa7181a7f5c8c700608d2debf412e519fe7f26abc03564c8a2 |

The complete first two bodies and the LAW request/routing/incoming assembly
were inspected. No native/parser/solver execution, new compiler run or
canonical profile/dispatch change accompanied this source audit.

## Raw input bounds do not bound derived exact rows

The original protocol bounds RAW rational numerators/denominators to256bits.
Its CHART compiler can produce larger exact coefficients or bounds. For
example, a=2^129 and b=a-1 are permitted denominators, while
1/b-1/a=1/(a*b) has a258bit denominator. This is a source/arithmetic deduction,
not a newly executed test or a proposed larger input limit.

The original CHART checker recomputes and compares the complete canonical
MATRIX prefix. It does not parse those derived entries as a fresh raw AFFINE
request. Certificate vectors use rational(token,false), while the complete
certificate retains its original4MiB framing. Preserve that route and exact
values; imposing the raw256bit bound on derived rows would add a restriction
the original interface does not have. This is an independent reason that a
raw AFFINE codec cannot silently substitute for the CHART matrix receiver.
No rounding, truncation, new grammar or canonical CHART admission follows.

The original4MiB certificate limit is checked at protocol::check; it is not
a final CHART producer-output guarantee. The CHART execute branch has no
matching final length gate, while LAW has its own separate gate. No overflow
was executed or established. Projection row caps do not bound rational sizes,
full output or wall time. Preserve actual resource/refusal/UNKNOWN outcomes
and complete recovery through the existing encrypted writer.

The direct RC1 request limit is65536B. The unchanged unified runtime and MCP
bridge each limit literal request_json to262144 UTF8 bytes INCLUDING escaping
and envelope fields; the bridge's runtime-result-file cap is8MiB. These are
separate layers, not larger usable canonical certificate limits. Native_bridge
still admits AFFINE/LAW only. An exact direct CHART result cannot acquire
canonical dispatch by naming an outer task. The Rust source review at
77920422868495bd9abba49e4ca941b45fd595bc records these call-site boundaries;
its loose prefix-only arithmetic bound remains peer-authored/unformalized and
is not adopted here as a complete result/resource theorem.
