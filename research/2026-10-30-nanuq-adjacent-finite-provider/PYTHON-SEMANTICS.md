# Retained Python / Lean semantics correspondence

This is a definition-level correspondence audit plus a computational cross-check, NOT a formal semantics theorem about the Python language or an original-network graph theorem.

| Retained `all_level_screen.py` | Lean provider |
|---|---|
| `tips` repeats label x iff mask bit x is set | `occurrenceLabels n mask` |
| increasing 4-combinations `qs` | `quartets n`; exact fixed-size identities checked in each data module |
| interval `[lo,hi]` | `(lo,len)` with `len=hi−lo+1` |
| membership of two labels on each edge side, either orientation | `edgeWitness` using actual occurrence slices and `contains` |
| three topology bits `1 << (3*qi+r)` | `edgeContribution` with the same bit positions; all three resolutions initially retained |
| subtree OR recurrence, leaf summary0 | `Tree.summary`; `summary_mem` proves coverage for every ordered binary syntax tree from checked interval closure |
| `(pattern >> (3*qi)) & 7` | `code=(pattern >>> (3*qi)) % 8`; `code_bit` proves its three-bit semantics |
| guard `code in (1,4,5)` | same checked guard, not an assumed noncrossing restriction |
| uniform DISTINCT topology mean | `twiceMean`; `twiceMean_exact` proves exact rational equality, without truncation under valid codes |
| default `twice_cherry_score=0` | original score0 for a sole nonseparating topology; NOT the modified-score1 control |
| anchors0/shared1/disjoint2ρ | `anchor`, equal to manuscript M with no further scaling |
| circular boundary coefficient | `alpha`, identical four-point difference; split-sum weight is alpha/2 |

`Tree.code_physical_iff` connects a code bit to a witness on a syntactic subtree interval edge. Translating an actual plane graph into this ordered syntax, and proving quartet restriction for arbitrary size, remain separate open adapters. No declaration silently imports those properties.

`PYTHON-CORRESPONDENCE-CONTROL.json` records an additional exact comparison: all120 mask-specific DP top sets agree with the unchanged retained screen, and the union sets agree with the retained independent graph-distance/four-point checker. The union counts are1,3,16,102. This control is not needed as a trusted premise of the Lean certificate soundness theorem. Its source hashes bind the actual compared Python inputs.

The source-to-network claims still require the manuscript's source-plane/order, restriction, source-score, and global support/composition proofs. Original NANUQ d is not replaced by a switching-multiplicity weighted metric.
