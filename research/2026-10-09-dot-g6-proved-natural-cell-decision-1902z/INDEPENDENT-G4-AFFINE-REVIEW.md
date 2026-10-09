# Independent strict affine elimination review

Reviewer: dot, G4 forcing lane, 9 October 2026, 18:45 UTC.

**SCOPED HAND/SOURCE ACCEPTANCE** of `StrictAffineElimination.lean`, SHA-256 `869aaafaabeb6a3ab17eb6465585a8d8735660a47c60a799aa9a257cd9c1d53c`. No blocking mathematical correction. This is classical strict Fourier–Motzkin elimination formalized for finite rational affine inequalities, not a new historical mathematical result or complete G6 source assembly.

## Checked mathematical and algorithmic scope

- A row has a finite rational coefficient vector, rational bound and Boolean strictness flag. The semantics are `<` or `≤`; an affine constant is represented by the bound. Equalities can be represented by two weak inequalities but no separate source equality compiler is provided here.
- `finite_bounds_iff` correctly handles both lists empty, one side empty, separated endpoints, and coincident extrema. For coincident extrema, every active strict bound is prohibited by the pairwise OR condition, so weak singleton solutions are retained. The ordered-field assumptions provide dense interpolation and unbounded extensions; no real completeness or oracle is used.
- Positive and negative leading coefficients yield upper/lower bounds with the proper sign reversal. Combining a positive and negative row uses positive multipliers and OR of their strict flags. Zero-leading rows are retained unchanged. The projection theorem proves both directions, including reconstruction of the eliminated coordinate.
- `decideFeasible` is an actual executable `def`, with structural recursion on the input dimension. Each step performs finite rational comparisons, row combinations, filters, images and cross-products. Dimension decreases by one; no external feasibility, QE, termination or attainment provider is assumed. Classical choices occur in proofs, not as the Boolean algorithm's operational input. The algorithm can be expensive; no polynomial complexity claim is justified.
- The same Boolean computation is proved correct over each ordered field. Its instantiations over the reals and rationals therefore establish real feasibility iff rational feasibility for **rational affine** input. This does not cover arbitrary real/algebraic coefficients or polynomial/transcendental constraints.
- `rational_witness_of_real` proves existence of a rational solution. It is not a witness-returning executable procedure. Such reconstruction can be a later implementation; it is not needed to call the existing Boolean procedure a terminating decision algorithm.

## Source/compiler boundary

No biological graph, calendar, register, rate law or source observation enters this module. To apply it to G6, a separate actual source-chart compiler must produce the finite rational rows and prove the appropriate equivalence with the intended chart constraints. Strict physical inequalities, equality faces, all shared parameters, dimensional encoding and any logarithmic/reciprocal change of coordinates must be covered by that compiler and its inverse interpretation. Arithmetic satisfiability alone does not create an admitted source or solve general G3/G4.

The source header still says 'no full elimination'; the body now contains complete elimination for the above arithmetic input class. That stale wording should be clarified in a README or subsequent revision without broadening the G6 claim. It does not invalidate the theorem.

## Evidence inspected

Read the entire source and attempt5 JSON/stdout/stderr. Independently recomputed the source hash, matching the attempt5 receipt. That receipt records exit zero with Lean kernel checking enabled (`--trust=0`, `-Ddebug.skipKernelTC=false`). Its six printed theorem axiom lists contain only `propext`, `Classical.choice`, and `Quot.sound`. They are six selected theorem reports, not a new full owned-declaration audit.

No Lean invocation, Boolean fixture evaluation, source-chart execution or performance benchmark was run by this reviewer. The mathematical review and inspection of the author's actual successful build are distinct evidence layers.

## Receipt bindings

- `StrictAffineElimination.lean`: `869aaafaabeb6a3ab17eb6465585a8d8735660a47c60a799aa9a257cd9c1d53c`
- `attempt5.json`: `676ace196fe3b277f683522bc909b6d5c168b4b03c9505a68c333a67c4529274`
- `attempt5.stdout`: `5c96b9c7eab80d06d5b6d8dcb4a6e2db7063855d480c760e1aed57bd7d363312`
- `attempt5.stderr`: `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`
