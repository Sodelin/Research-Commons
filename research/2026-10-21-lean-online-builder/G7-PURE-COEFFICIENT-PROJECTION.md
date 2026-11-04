# Exact finite rational coefficient comparison

Three selected endpoints of the pure polynomial projection passed actual
hosted type and axiom checks. They identify a list's rational coefficient
sums, prove zero at absent exponents, and prove `checkExpr_sound`: if sums
agree on the union of both lists' exponent supports, the rational polynomials
are equal. Duplicate terms contribute their sums. No numerical samples or
floating-point comparisons occur.

The original3023-byte projection4febe046c4c7ed900adc84e391dcb7a4530dc5bedebe9395e275e3cae4d5a899
was submitted unchanged and REJECTED. Its negative simp branch left
`k = z.1 -> z.2 = 0` under `hz : z.1 != k`. The clean absent-coefficient
subaudit is not a partial PASS. Exact original bytes, failed diagnostic and
the two nonstandard axiom lists remain in the revision review.

The proof-only repair separates the equality and inequality branches and
keeps `eq_comm` in the equality branch. It also explicitly supplies
`Ne.symm hz`; the hosted linter reports that argument unused. Definitions
and theorem statements are unchanged. Corrected3137-byte source:
`lean/proposals/PopulationCoefficientProjection.lean`, SHA256
ea3b6538a10be5ba470d372a30a70bc6e7f53b8b98880501c4d90f5b7bc3b15c.
Submitted source with all three audits:
edf359872c8adcb2c1990dbc8ed6759ebca503afa35fb7c2003b0a577addbef8.
Zero errors; three benign unused-simp/deprecation warnings. All three
complete printed types and propext/Classical.choice/Quot.sound lists were read.
The service reported Lean4.35.0/mathlib56a005 and the unchanged3bafb347
before/after manifest. Full hashes are in `CHECKED-FOLLOWONS.json`.

`G7-PURE-COEFFICIENT-PROJECTION-REVIEW.json` retains the exact proof diff,
failed revision and successful selected scope. The original source map is
retained separately. Its four original byte-range/hash equalities were
independently reproduced before the proof repair. The source-only header is
a preserved preparation snapshot; the selected pure virtual document is now
checked. The full imported population-certificate context remains unelaborated.

This virtual document uses original declaration names. It must not be
co-imported with their full original modules. It remains OUTSIDE the777-module
native selection and adds one bounded hosted case only. It supplies no Code
validity, merger recurrence/destination support, Table/check soundness,
actual population probability, physical sparse-row composition or native
emitter/parser/result origin. Those full source joins and native first-writer
requirements remain open.
