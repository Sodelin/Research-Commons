# Independent representation-pilot review

Reviewer: dot, independent representation review, 2026-10-02.

**Verdict: PASS for the explicitly scoped finite representation and query pilot.** No universal optimality, new mathematical field, new biological observation, full calendar-law compression, or completed G5 formalization is established.

## Reviewed artifacts

- pilot.py SHA-256: `7d9209f6df21de787afc23be42907d2be0388739aea18381401358742dc67e2c`
- results.json SHA-256: `a91aab51bd045d14e784255e34c6726d16382c1dacc73c07984bb1d2f75a683c`
- accepted_binary_source.py SHA-256: `61014ea67e0ce587f74adc49f1bb4e9e6407e93862203de7c7bd0aa3bee428b4`
- RepresentationTransport.lean SHA-256: `db183916d2ec3bd8916e729eb4cd48db8915e899cb4f929fd9bf01eb99651a5e`

The source copy was compared byte-for-byte with the accepted binary-matched-pair-laws fixture. Review did not modify the integration artifacts.

## Independent finite controls

A separate edge-list/parent-map routing implementation, without calling the fixture's switchings, ancestral_path, or active helpers, reproduced all **750** support states and **3150** direct encoded possible/sure block-query answers. This independent query implementation queried the packed representation directly, rather than querying its decoded copy.

Domain: the fixed original-ID roster `(a,b,c,f,z)`, the triangle and star source fixtures, all 25 nonempty panels of sizes 1–3, and these 15 endpoint/interior times:
`0,1,2,3,4,9/2,5,11/2,6,7,8,11,14,15,16`.
These hit every distinct temporal support regime of these fixtures: changes occur only at node ages, with the older-side endpoint convention, and all t >= 16 use the common ancestral tail. This does not test arbitrary sources or an arbitrary observed-law parser.

Independent lowest-common-ancestor computation on switched parent chains reproduced all 10 pair meeting-age measures for both sources and confirmed exact equality. Under the fixture's stated permanent-meeting/unit-rate premises, the associated shifted-Exp(1) mixture laws are equal. Any deterministic recoding, including full Haar and the reported digest, consequently preserves that equality; this is not a cryptographic hash collision claim.

At t=7 the abc support codes are:
- Triangle: `(1,2,4), (1,6), (2,5), (3,4)`
- Star: the same four events plus `(7)`
The joint event grouping and original-ID roster are essential. Pair projections erase this difference.

Additional independent checks:
- 370 codec roundtrips over every possible support subset for every roster panel of sizes 1–3, including empty support
- 224 bitmap query checks: all 32 triple support subsets, including empty support, times seven nonempty blocks
- 160 original-ID group-merge cases over all five-label set partitions

The integration's 3150 decode-based comparisons are valid codec self-consistency controls. Alone they would not independently validate source extraction. The separate routing/query controls above address that limitation within the stated finite domain. Neither implementation extracts H_U from arbitrary observed calendar laws; H_U is supplied from source fixtures. Merger membership masks preserve extant label groups but not complete rooted merger history or times.

## Serialization and optimality

For the reported star triple example, default ASCII JSON payload lengths are 105 bytes for explicit labeled support, 40 for the bitmask event list, and 2 for the integer support bitmap. The bitmap also requires its coordinate schema; the displayed partition catalogue is 40 bytes, original-ID roster 25 bytes, panel roster 15 bytes, and time string 3 bytes. These are component lengths, not standalone-file totals. Whether metadata is implicit, shared, or stored must be declared before comparing complete storage.

The Haar comparison is 40-byte eight-coordinate indicator payload versus 48-byte full rational Haar payload, with common coordinate metadata excluded. It shows no compression gain in this serialization. Haar is an exact invertible transform here, not a measured lineage waveform.

Five bits suffice for arbitrary subsets of the five Bell(3) partitions. A five-bit worst-case fixed-width lower bound applies if the declared contract admits all 32 subsets, or at least 17 distinct objects that must be distinguished. It is not an optimality theorem over these two biological sources or the full continuous calendar-law domain. Even the query quotient differs from complete support: the seven possible/sure query signature has 30 classes on all 32 supports, with bitmap pairs 14/15 and 30/31 colliding. This quotient still needs five fixed-width bits in its worst case, but that fact is a different contract.

## Benchmark review

The final benchmark correction is adequate: cached query comparisons return the same seven Boolean pairs; matched support-conversion comparisons cache query encodings for both methods; full bitmap setup now includes catalogue, lookup, query masks and event masks; one-shot bitmap timing includes this setup, conversion and queries.

Final integration medians, microseconds per seven-query batch:
- Raw support: 5.599
- Event-list masks, preconverted: 5.314
- Event-list masks, matched support conversion: 9.924
- Support bitmap, preconverted: 0.688
- Support bitmap, matched support conversion with cached setup: 5.331
- Bitmap one-shot, all setup and conversion: 17.012
- Bitmap full setup alone: 11.629

An independent timing check also found a strong cached advantage (raw 5.52 us, bitmap 0.772 us) but essentially a tie after bitmap support conversion (5.50 us). Its broader setup routine, which also generated the support vector, took 16.56 us and is not the same setup routine as the final integration report.

**Supported conclusion:** the support bitmap accelerates repeated already-prepared queries on this one tiny support. One-shot bitmap use is slower than using the already-available raw support; setup must be amortized. These seven-repeat/1000-operation Python hot microbenchmarks are not randomized, end-to-end, asymptotic, or evidence of a general representation optimum. Bell-number catalogue growth matters beyond this small panel.

## Lean

The final source was independently compiled with Lean 4.33.1 and the provided mathlib environment; exit code 0. Printed axiom audits use no axioms or only standard propext, Classical.choice and Quot.sound, with no sorryAx.

Formal scope is generic collision/fiber transport with a decoder, injectivity of finite-set incidence predicates, exact two-coordinate rational Haar inversion, and a coarse-coordinate collision. This does not formally verify the Python bitmask implementation, recursive eight-coordinate Haar implementation, source support extraction, or the biological G5 theorem. The joint-incidence lemma is an abstract incidence map on finite sets of whole blocks; it is not a formal proof of a particular machine-integer packing algorithm.

Initial compile errors and misleading time-grid comments were repaired before this reviewed version. Initial conversion-cost asymmetry was also repaired before this verdict.
