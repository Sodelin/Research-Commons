# Complete distinct quartet support does not determine the full displayed-tree family

This finite counterexample is in the abstract NANUQ adjacent singleton/doubleton plane-tree representation class. The observed features are every distinct displayed quartet set, on the same finite label set and circular order. The target property is whether one displayed full tree contains both `abc|de` and `ade|bc`.

Both unrooted plane binary trees have tip contour `a0,a1,b0,b1,c,d,e`. For each, a arises from a0 or a1 and b from b0 or b1; c,d,e are singleton tips. Choices of a and b are independent. Both trees thus have exactly the same label order and copy multiplicities.

## Explicit trees

Names r,u,w,l,m below are internal vertices. In each row all three neighbors of each internal vertex are listed; this specifies the entire undirected adjacency.

| Vertex | A neighbors | B neighbors |
|---|---|---|
| r | e, a0, u | e, a0, u |
| u | r, d, w | r, d, w |
| w | u, l, m | u, c, l |
| l | w, a1, b0 | w, a1, m |
| m | w, b1, c | l, b0, b1 |

Equivalently, suppress the artificial outer root in these ordered Newicks; their left-to-right leaf orders specify the stated plane contours.

- A: `((a0,(((a1,b0),(b1,c)),d)),e);`
- B: `((a0,(((a1,(b0,b1)),c),d)),e);`

## Exact results

| Selected a,b | A: nontrivial full splits | B: nontrivial full splits |
|---|---|---|
| a0,b0 | `ade\|bc`, `ae\|bcd` | `ade\|bc`, `ae\|bcd` |
| a0,b1 | `ade\|bc`, `ae\|bcd` | `ade\|bc`, `ae\|bcd` |
| a1,b0 | `abc\|de`, `ab\|cde` | `abc\|de`, `ab\|cde` |
| a1,b1 | `abc\|de`, `ade\|bc` | `abc\|de`, `ab\|cde` |

The two split unions agree, and all distinct quartet sets agree:

| Four labels | Distinct resolutions in A and B |
|---|---|
| abcd | `ab\|cd`, `ad\|bc` |
| abce | `ab\|ce`, `ae\|bc` |
| abde | `ab\|de`, `ae\|bd` |
| acde | `ac\|de`, `ae\|cd` |
| bcde | `bc\|de` |

The common raw distance matrix (uniform over distinct quartet resolutions, not physical selections), in order a,b,c,d,e, is:

```text
 0  9 11 11  9
 9  0  8 11 12
11  8  0 10 11
11 11 10  0  8
 9 12 11  8  0
```

The stronger co-occurrence property differs: A displays the pair `abc|de` and `ade|bc` together (a1,b1), whereas B does not. A has three distinct displayed full trees and B has two.

## Replay and limits

Run `python check_nanuq_paired_fixture.py` with the supplied JSON in the same folder. The checker reconstructs both graphs from the fixture, checks finite binary tree admission and both tip block orders, checks all four choices in each tree, derives each quartet by exact integer four-point distances, derives splits by exact physical edge cuts and recomputes the common raw matrix using rational arithmetic. This is an exact executable finite fixture, not a Lean proof of the general NANUQ program.

The fixture concerns abstract plane trees with repeated occurrence labels. It does not assert that either tree lies in the image of the original rooted-LSA outer-labeled galled-network opening operation. That would require an explicit pair of admissible source graphs and a checked source-to-occurrence correspondence before calling it a counterexample in that narrower source class. It also does not assert agreement of weighted switching laws, full joint quartet laws, or full displayed tree families. This fixture is not an Alexander whole-infinite-avoider statement.

Comparable earlier abstract result: [contiguous multicopy extension, §6](https://github.com/Sodelin/Work-on-Samuel-Alexander-Research-/blob/e2502c82ab9a77c00543932f775a71e5374221f7/research/nanuq-all-level-2026-09-29/CONTIGUOUS-MULTICOPY-EXTENSION.md#6-the-full-tree-family-can-shrink-an-explicit-small-example). Unlike the source's tripled-copy fixture, both trees above use at most two copies per label and have identical copy multiplicities.
