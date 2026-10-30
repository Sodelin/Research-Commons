# NANUQ adjacent-copy finite Lean provider

The finite ordered-tree provider has passed an isolated exact-source Lean 4.33.1 replay. This is **not** full Lean verification of the original-network all-level NANUQ theorem; the Zenodo/full-theorem gate remains open.

## Proven scope

For 3–6 ordered labels, all 120 adjacent duplication masks, and every ordered full-binary tree on the prescribed occurrences, the provider proves nonnegative anchor coefficients and absent-boundary zero coefficients. It also verifies resolution codes, the connection to syntactic subtree-edge witnesses, exact rational uniform-distinct-resolution means, boundary-anchor positivity, and the pendant-anchor value 2.

The actual source network→plane contour/order→ordered tree adapter and arbitrary-size six-label restriction are not supplied. Neither are the final source composition/reconstruction/global support joins. See STATUS.md and PYTHON-SEMANTICS.md.

## Evidence

- `FiniteProvider.lean`: public theorem endpoints.
- `SOURCE-MANIFEST.json`: exact local closure, 1211 modules (mostly small generated certificate fragments).
- `BUILD-EVENTS.jsonl`: every local module ultimately exit 0, source hash, object hash and timing; the bounded-memory retry remains recorded.
- `BUILD-ACCEPTANCE.json` and `RECEIPT-AUDIT.json`: clean acceptance and exact-source/axiom audit.
- `build-logs/FiniteProvider.log`: endpoint transitive axioms; only propext, Quot.sound and Classical.choice occur.
- `ENVIRONMENT-EVIDENCE.json`: compiler and mathlib pins. Existing dependency oleans were reused; this is not a fresh rebuild of all Mathlib.
- `PYTHON-CORRESPONDENCE-CONTROL.json`: exact agreement with retained finite screen and independent four-point replay; this is a control, not a trusted Lean premise.

All local certificate computations use `decide +kernel`, with kernel checking enabled. No native_decide, sorry, admit, source axiom or imported positive-result assumption appears in the selected source closure. Standard Lean kernel/import trust still applies; no external expert review is claimed.

## Replaying without installing anything

Use an existing Lean 4.33.1 binary and existing dependency olean directories for pinned mathlib 0df444a360eaa60ab8c11dca51a86af692955474 and its dependencies:

```sh
python replay.py --lean /path/to/lean --dependency-olean-dir /path/to/mathlib/.lake/build/lib/lean --dependency-olean-dir /path/to/each/other/dependency/.lake/build/lib/lean
python audit_packet.py
```

Repeat the dependency option for each installed dependency. The package does not download or install anything. Replay is serial and memory-bounded. The archive deliberately omits compiled objects; rebuilding produces them. Prior zero-exit entries are reused only when manifest, source and object hashes all match. The audit script therefore runs after replay when object files exist.

Original NANUQ d is preserved; no switching-weighted metric substitutes for it. This package closes a scoped finite-certificate obligation, not manuscript Theorem A or all Lemmas A.1–A.7.
