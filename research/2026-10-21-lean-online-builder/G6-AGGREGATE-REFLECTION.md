# Complete ordered cell emission from individual fields

The four generic aggregate declarations in NativeCellAggregateReflection.lean
passed actual hosted Lean4.35.0/mathlib56a005 checking. Their complete types
and standard-axiom lists are in CHECKED-FOLLOWONS.json. No errors, sorry/unsafe
warnings or nonstandard selected axioms were accepted. Inherited/style and
unused-section warnings are retained. The original native and Lean compilers
are unchanged.

The principal theorem proves

    decodeRows n (GParity.Chart.emitRows input)
      = compileCellList N layout edges leaves populations hybrids
          chronologyIds exposureIds chronology exposures coins.

It DOES NOT take that equality, or hemit, as an input. Its explicit
FieldReflection premise gives the individual original field relations:

| Relation | Content |
| --- | --- |
| Coordinates | Raw dimension equals n; age, inverse-rate and hybrid indices match the supplied ONE bijective layout |
| Edges/taxa | The exact ordered source/target and leaf-index lists are maps of the supplied typed registries |
| Populations | Native range of edge occurrences followed by the one ancestral coordinate matches the supplied population list |
| Hybrids | Native range matches the supplied hybrid occurrence order, reused in both open bounds and extra intervals |
| Chronology | Exact comparison/left/right record list in its original order |
| Exposures | Exact population, younger/older atoms and lower/upper interval endpoints in original order |
| Extra coins | Exact interval/index pairs from zipIdx match that same hybrid list |

The proof assembles ALL eight existing blocks: edge positivity, two tip-age
equality rows, inverse positivity, lower hybrid bounds, upper hybrid bounds,
chronology, exposures, and extra coin intervals. Strictness, absent endpoints,
rational coefficients/bounds and duplicate row positions remain exact.

erase_emitRows_eq_encoded first erases only CHART's INTERNAL unit bookkeeping
weights and proves equality with the encoded original typed list. It does not
assert equality of the complete weighted wire records. decoded_emitRows_eq_compileCellList
then reuses the original decode/encode theorem. emitted_coefficient_lengths
proves every ORIGINAL emitted coefficient list has length n; decoder padding
is not used to hide a malformed length. decoded_emitRows_toFinset uses the
existing compileCellList_toFinset, with explicit completeness of every supplied
registry list, to derive the existing hemit equality. External ordered Farkas
multiplier positions and their complete length are unaffected.

Exact standalone12798B/SHA256
6df93dd4ae74f3b12adcda4c59bece901e7a6bacb47e8f27dedd52650d3657f2.
The checked virtual projection is69573B/SHA256
21c2e9a0bc27610b0494d6e40a5ba295a8a62997e7f7e6f117466e39deda53e7;
submitted-audit SHA256
025b94d09e2fdb9e4679fc80c9305aa07e22d5b0fd483b94dd928eac564b2827.
The SOURCE-MAP and reproducible source-only preparer pin all originals and exact
selected definitions. They include complete SourceNetwork, the original Hybrid
abbreviation, original cell/list compiler, and exact encode/decode definitions
and theorems. This is a bounded source/data/compiler projection, not full
physical import or native Lake/object acceptance. The same bounded union
capture client and before/after identity checks used by the admission component
were retained. Three rejected source revisions remain explicitly rejected.

The revised proposed native context adds this ONE module to the prior545:
546 modules/4530839B,533 original plus13 owned/import variants. Every prior545
module entry is unchanged. The native writer/controller remains UNBOUND and
the quiet outer launcher remains unexecuted.

The FIRST remaining use-site obligation is constructing FieldReflection for
the actual captured request/Code, rather than asserting it in a dictionary.
That includes original occurrence lists, numeric positions and all reflected
fields. Concrete BinaryValid/RegistryValid, original port convention M0,
CutChild/required planarity/menu/readout and authenticated request/result origin
remain separate. The theorem concerns the supplied finite cell and does not
give complete source acquisition, all-size NO, G3/G4 closure or native parser/
executable refinement. The original exact CHART prefix/checker and independent
request/certificate/runtime/MCP limits remain mandatory.

The later G7-CODE-CHART-REFLECTION.md supplies this field relation as a proved
construction for literal Code and its actual validity proofs/orders. The
remaining actual-capture data equality and byte/native/physical refinement are
not assumed supplied by that forward map.
