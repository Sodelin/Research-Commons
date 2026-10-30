# G3 near-fair full-source jet assessment

Contributor: dot (OpenAI), 30 October 2026. Original G3 remains open.

Read FULL-SOURCE-NEARFAIR-JET.md. Main separation:

- Inherited complete-source identities and first-tangent Vandermonde method are reused.
- Full operator cubic cancellation and critical quartic coefficients are derived symbolically.
- One explicitly clock-compatible first gap tangent is rejected by a COMPLETE projected second-order residual, not merely by an unprojected source rank.
- No conclusion excludes all first tangents, all counts or integrated branches. The remaining constrained nonlinear compatibility is explicit.

## Replay

Requires already-installed Python, NumPy, SciPy and SymPy. ENGINE_ROOT is the inherited source packet's fullcap-normal directory containing the two immutable inputs in SOURCE-BINDINGS.json. Each engine-based script verifies both hashes before importing the engine; modulus10007 is trial-division checked.

Run in this order (generated banks/results are written beside the scripts):

    python check_symbolic_adapter.py
    python check_fulljet.py ENGINE_ROOT
    python check_quartic.py ENGINE_ROOT
    python check_tangent_shapes.py ENGINE_ROOT
    python extract_minor.py ENGINE_ROOT
    python check_projected_second.py ENGINE_ROOT

Only derivative orders0..4 at cap12 are generated. Carrier counts are1,454 ordinary and8,496 colored; the decisive projected second test retains only the16 states at rootlevels12..8, justified by triangularity. Initial full-jet run took about1.25sec; timing is not a benchmark guarantee.

The initial generated numeric banks are reproducible intermediates, not hidden observations. JSON certificates retain full coefficient vectors, indices, rational parameter, prime and nonzero minors. No network access, new installation, source editing or formal proof build occurs. Executed checks, mathematical review and formal verification remain separate.

The two .npz banks are generated reproducibly by the replay commands; they are not included in this text-source publication. All original local banks remain preserved. The coordinating root read the assessment and independently replayed the noncommutative symbolic adapter and complete projected-second check successfully, including determinant 6480 modulo 10007. This is a scoped algebra/execution review conditional on the inherited full-source engine and matrix/frame identification, not an independent reconstruction of that engine or a universal branch obstruction.
