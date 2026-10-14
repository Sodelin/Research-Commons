# Affine exposure change at one actual bigon

**Source only, uncompiled and unselected.** This packet derives the unequal-arm analogue of the existing equal-exposure splice identity. It preserves all existing source packets and selected programs.

For every clade `D`, the real value of the original normalized weight is the value of the fixed base splice plus

```
if D = original child bridge cut then
  exposure(actual registry-selected arm) − exposure(fragment parent0)
else 0.
```

The base tuple is literally the previous `splicedNetwork`, `splicedCalendar`, `splicedRegistry`, and `splicedRates`. Its new edge always uses entry + fragment-parent0 + child exposure, independent of the removed bank bit. The original chosen arm is literally `(H.parents removedHybrid).parent (coin removedHybrid)`; it is identified with a kept fragment edge through original switching uniqueness. The registry order is never assumed to match the fragment order, and no Gamma, source rate, or calendar is refitted. Real subtraction permits either sign of the increment.

The proof first establishes a balance over nonnegative real weights using the exact retained-edge sum and four removed occurrences. It then casts to real numbers. The unselected arm contributes no fibre; the entry, child, and selected arm share the actual child bridge cut. That cut is nonempty, proper, and bank-independent by the proposed bridge-cut source, not by a supplied profile equality.

For two whole original banks agreeing everywhere except possibly the removed hybrid, their restrictions agree. Their fixed base profiles therefore cancel, leaving exactly the difference of the two actual chosen-arm exposures at this single cut coordinate. Finite linear summation gives the directed-exposure difference for inside-to-outside pairs and zero otherwise. The final theorem reuses the selected `weightedNormalize_directedExposure` provider to state the same result for the existing sum over original selected edge occurrences.

These are pointwise scalar/profile identities. They assert no equal-arm law preservation for unequal arms, no PMF factorization or probability positivity, no repeated-cell or equal-cut chain theorem, no support/count bound, no protected eligibility, and no physical representative or G3 decision. The finite-coordinate auxiliary premise is instantiated by the derived original-source identity in the final theorem; no desired source-law equality is an input.

`SOURCE-PINS.json` binds the exact providers and original selected catalog. The aggregate and Lake supplement are proposed future integration entry points. Inline `#print axioms` commands are unexecuted requests. No compiler, import query, test, materializer, object audit, or Git operation ran. Source-byte and lexical checks do not establish kernel correctness or a dependency axiom audit.

The initial unexecuted affine draft is preserved under `evidence/unexecuted-draft-3ac2`; its successor adds the explicit `G1CutChildPorts` namespace open without changing a statement or proof body. A bounded census found the same missing open in ten frozen predecessor modules. Those originals remain unchanged and are pinned here as the source-review basis. A later aggregate must select and authenticate the separately preserved namespace-repair successors before claiming a successful build; this packet does not silently reinterpret old dependency hashes as repaired inputs.
