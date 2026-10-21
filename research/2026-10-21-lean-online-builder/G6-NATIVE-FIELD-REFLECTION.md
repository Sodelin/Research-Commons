# Exact cell fields and ordered-row correspondence

The existing `GParity.Chart` already supplies the value-level CHART records,
forms, parser and eight-block `emitRows`. Its9852-byte original source at
Commons1138a5 has SHA256337d5e41153a356df2e9a8d8c7998d1f1d41bc56a331bcae10e8d2693768612a,
Git blob3fd849119888d8a22ed26d2dd19ba75c9bf7bb04. It is reused unchanged.
The existing Rust `natural_cell.rs` remains unchanged too. Neither source
alone proves parser, mutable-validator or executable refinement.

## Concrete field relation required after the captured Code

| Captured native field | Existing typed field/relation |
| --- | --- |
| Ordered EDGE source/target, ROOT, LEAF, HYBRID/site/ports | Literal Code arrays and `sourceOfValid`, with exact census, `BinaryValid`, `RegistryValid` and M0 |
| `V:i` age atom | `.node v` with exactly `v.val=i` |
| `Q:q` age atom | `.fixed q`, exact rational value |
| AGE LT/LE/EQ | `AgeComparison.strict/weak/equal`, preserving left/right order |
| Bound LT:q / LE:q | `RationalBound` with the same value and strictness bit |
| NONE interval endpoint | The same absent Option endpoint, with no replacement numeric bound |
| EXPOSURE population E:i / A | `some e` with `e.val=i` / the ONE ancestral `none` |
| EXPOSURE younger,older | The same atoms; duration is older minus younger |
| COIN:i interval | The interval on `decodedIDs i`, with the complete original hybrid order |

The [checked layout](ORDERED-BANK-LAYOUT.md) gives the exact age, edge inverse,
ancestral inverse and hybrid positions. It does not derive the table's
captured-array/Code relation or interpret the routing coin. Under the selected
M0 incoming0=parent0/incoming1=parent1 map, physical gamma is parent1 probability
and native LAW G=1-gamma. CHART interval arithmetic alone carries no LAW meaning.

## Actual new universal form proof

`NativeCellFormReflection.lean` relates the existing typed affine constructors
to the existing list-valued CHART constructors. It proves constant/variable,
subtraction and scaling correspondence; the actual affine row; ordered
strict/weak/equality comparisons; and lower-then-upper interval scaling.
Equalities emit two weak rows in the original order. Absent endpoints emit
no row. Coefficients, rational bounds and strictness bits are retained exactly.

Four complete selected declarations passed actual hosted Lean checking:

- `Astra.NativeCellFormReflection.encodeForm_variable`
- `Astra.NativeCellFormReflection.affineRow_correspondence`
- `Astra.NativeCellFormReflection.comparison_correspondence`
- `Astra.NativeCellFormReflection.scaled_correspondence`

All selected axioms are exactly propext/Classical.choice/Quot.sound, with no
sorry or additional axiom. Benign inherited unused-variable/deprecation and
new unused-simp-argument warnings remain recorded. Context is the existing
Lean4.35.0/mathlib56a005 hosted lane, with unchanged manifest3bafb347b291b221e474e7c02b2390a921c7be64ec272c300699c46eab37a270.

The standalone proof is4127B/SHA256
29ed474cd1a291bc2855775b22b0726c8aae34113d62efcead283d487aa9a0de.
The bounded virtual document is39234B/SHA256
7ce2eed4770e527b335a9cbee408ff5bcdb6dc8734ad40e2895182d9faa6bad7;
its audit-suffixed submission is
11947b1f16f56fa1b75a0257a1f21325cfe2d6b11155349ca9c4a726ee590f98.
`lean/NativeCellFormReflection-SOURCE-MAP.json` and the preparation script
pin all original bodies and the exact definition projections. Only unused
open lines are removed from that projection. This is not full physical import
elaboration, native4.33.1 acceptance or Rust execution refinement.

Three prior proof revisions were rejected and retained. The first used a
looping simp and did not reduce the native enum comparisons; the second still
left variable indexing unresolved; the third exposed a dependent-bound proof
transparency issue. The final proof unfolds the list target before obtaining
its bounds, uses explicit index rewriting and reduces each enum case directly.
`FORM-REFLECTION-REVISIONS.json` pins those source identities. No original
compiler definition or theorem statement was changed to make the proof pass.

## Eight-block complete emission still needs its use-site theorem

The original `G6NaturalCellOrderedCompiler.compileCellList` orders the rows as:
edge duration positivity; two weak rows for each tip-age equality; edge inverse
positivity followed by ancestral inverse positivity; all hybrid lower open
bounds; all hybrid upper open bounds; supplied chronology in order; supplied
exposures in order; extra coin intervals in original hybrid order.

The primitives above match those blocks. A general captured-Code adapter must
still assemble the exact complete registry lists and prove

    decodeRows D (GParity.Chart.emitRows reflectedInput)
      = compileCellList N layout ... chronology exposures coins.

That ordered equality is the first remaining aggregate emission relation.
`compileCellList_toFinset` then supplies the existing `hemit` premise. Do not
deduplicate before checking original row multipliers. CHART's internal unit
bookkeeping weights are distinct from the externally supplied contradiction
weights; `decodeRow` erases only the former's irrelevant representation.
The strict zero-bound contradiction still needs a POSITIVE multiplier on a
strict original row, with all multipliers nonnegative and combined coefficients
zero. No condition of nonnegative combined coefficients is substituted.

There is already a concrete source receiver, `G6TwoTipChartFixture`,10703B,
SHA2561d7e4d7509022405182bd8c98e98e59d73d013899b4cecd29d55a854a2972bfb.
Its complete body was read: `nativeRows_eq_emitted` and
`nativeTypedRows_eq_emitted` compare actual value-level emitRows to that one
two-tip typed source, with and without fixed chronology/exposure cells.
This is an existing bounded supplier, not the general Code theorem or the
n>=4 G6 class. The source contains five `#eval` commands: it was NOT executed
or added to the proposed import context. No fixture suite was replayed here.

The proposed context now includes the unchanged GParity.Chart plus the new
form proof:545 modules/4518048B,533 original and12 owned/import variants.
All prior543 entries remain unchanged; the exact full source remains uncompiled.
Graph/selection metadata and the silent pre-Lake refusal preserve that scope.
Original source class/menu, active-chart coverage, physical readout/provider,
complete source acquisition/NO, native result origin and actual writer custody
remain independent requirements.
