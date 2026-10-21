# Existing finite-code source and registry decoder

The current original G7 source already supplies a generic decoder. A new
RootedBinary constructor or source grammar is unnecessary. The complete bodies
below were read and checked against the pinned Commons1138a5 source graph.
Their original authorship/status is retained; no new native/Lean run is claimed.

| Module | Bytes | SHA256 |
| --- | --- | --- |
| G7OriginalAdmission | 10308 | 16c824d8c16d69cea022a43b8029c2624e5b4af31d2a1fdb06a7ae2d6802789c |
| G7OriginalFiniteEncoding | 4694 | 30f27653e12e4637acfa4c7195f34c232d862b38d2b8b813ab4150cde6949078 |
| G7OriginalCensus | 4894 | cb05c3483553a3feb79909d343dcabd22e65ae7059ad639a285bce5f2044b517 |

Exact source paths are
`research/2026-10-12-dot-accepted-connected-union1613-1737z/source-store/<SHA>.lean`.
G7OriginalAdmission imports the already selected G7FiniteReachability
(`25673c4d0a0ec0891ff204ff79c018d8e9ad1971962183e0a7332b6d709d2a35`).
Adding the admission module required only ONE extra module beyond the prior
540-source context, producing the immutable541-module/4497681B snapshot.
The later two layout modules make the current context543 modules/4504069B.

`GProgram.G7.OriginalFiniteEncoding.Code X ID` stores original source/target
arrays, root, named taxa, named hybrid sites and ordered parent occurrences.
Its finite V/E carrier sizes are the original binary census for the supplied
taxon/complete hybrid-ID counts. Parallel arcs remain distinct coordinates.

The existing namespace `GProgram.G7.OriginalAdmission` exposes:

- `BinaryValid`, `RegistryValid`, `CutChild` and their actual Decidable instances;
- `sourceOfValid c hb`, constructing the inherited RootedBinary from BinaryValid;
- `decodedIDs c hb hr`, a bijection onto ALL actual hybrid vertices;
- `decodedRegistry c hb hr`, retaining original parent0/parent1 occurrences;
- `decoded_parent_exact`, identifying each decoded parent with `codeParent c i b`.

The first concrete native-to-typed use-site binding is therefore the exact
captured-request-to-Code relation, not an assumed source-admission flag:

1. Preserve integer counts, source/target occurrence arrays, root, taxon IDs,
   hybrid IDs and the selected M0 incoming-port order in one literal Code.
2. Supply BinaryValid and RegistryValid evidence for that exact Code, and
   CutChild where required. An independently checked finite-code proof can be
   used; native Boolean success is not itself a Lean proof.
3. Reuse sourceOfValid, decodedIDs, decodedRegistry and decoded_parent_exact.
4. Instantiate the checked generic bank-layout equivalence with those exact
   occurrences: native AGE, edge inverse rates, one ancestral coordinate and
   hybrid-coordinate order. ORDERED-BANK-LAYOUT.md pins the hosted theorem and
   the source-only OriginalCodeBankLayout use-site. Arbitrary Fintype numbering
   does not authenticate that particular order.
5. Relate every original chronology/exposure/coin field to the typed functions.
   The existing compileCellList_toFinset then supplies exact emitted-set equality
   from complete registry lists; the list/wire relation still preserves duplicate
   rows and the associated multiplier positions.

The native row-export source at Rust proposal
`73f344954f125fd0437c5bbbaaf19c7803307e0a` was inspected with its complete
contract: `native/cell_row_export.rs`,7879B/SHA256
`11e9e68a5ad4769148bc60592845504c9eaf01182e3c5465078037c55dc89b6e`.
Its private owned request/Chart/Compiled and read-only accessors preserve the
original compiler, order, dimensions, ports and one ancestral slot. No apparent
source/API/ownership mismatch was found within those inspected boundaries.
It remains UNCOMPILED/UNEXECUTED, including its five staged controls. No generic
parser/refinement or installed-library acceptance follows from this source review.

The later source-only adapter at
`2f96fbc855ff570dfc048c86a03e77cb5064cb63`, SHA256
`9e458889c66b3070ebe29cd93387030f6ecd6ffa20a169830af3d428eef81da3`,
adds an early exact `RC1 CHART ` prefix guard. Its complete body and narrow diff
were inspected: non-CHART tags cannot enter the generic parser's COUNT/LAW
validation, while every CHART byte still uses that original parser. The staged
unsupported-command test is amended, not executed or counted as a new suite.
Rejecting a tag does not authenticate its content. Both revisions retain their
separate exact hashes and uncompiled/unexecuted status.

The original admission file explicitly leaves outer-labelled planarity/cofacial
taxa separate. Its executable binary/cut-child/registry portion can support the
declared nonplanar G6 source class; the original planar G7 class still needs its
additional premise/test. Active exposure/chart coverage, source-law/readout
correspondence, all-history policy execution, native origin and the unbound
encrypted first-writer/controller remain independent obligations.
