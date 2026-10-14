# Distinction-preserving margin extension

Contributor: Codex delegated margin extension, 14 October 2026. Status:
**UNCOMPILED additive source draft**. Source argument: Astra's published
`research/2026-10-14-g4-independent-algebraic-jets-0621z/ALGEBRAIC-JET-THEOREM.md`,
section 4, forward implication. This is a handoff for the existing integration
owner, not a change to the selected module graph. Astra retains the physical-jet
construction. No published source was modified.

Module: `G4DistinctMargin.lean`. Import: `G4StrictMargin`, frozen source SHA256
`a78e639389a08a5d9ab384956d82d4f650cc23842208dde2b978b4a8fcc5fdb4` at
[the pinned predecessor module](../2026-10-14-codex-g4-astra-review-0630z/lean/G4StrictMargin.lean).
No umbrella or new external tactic import. Namespace: `G4DistinctMargin`.

Declarations:

- `nonzero_of_value_error`: a close value with error below a positive absolute
  value margin cannot be zero; the corrected value's nonvanishing is derived.
- `scaled_external_error_bound`: derives `(L*e)^R <= (L^R*C)*residual` from the
  radius bound and `L>=0`.
- `component_order_gaps`: extracts `r*R<q` and `s*R<q` from `max(r,s)*R<q`.
- `exists_strict_distinct_zero_of_power_error_bound`: corrects one tuple and
  proves `F(z)=0`, strict coordinates, and `h(z)!=0` on that SAME tuple.
- `eventually_exists_strict_distinct_zero_of_order_gap`: proves a positive
  cutoff under which every positive parameter has such a tuple.

The endpoint takes positive constants `a,c0,c1`, nonnegative `C,B,L`, natural
orders `r,s,R,q`, and `max(r,s)*R<q`. For `0<t<a`, it requires coordinate
margins at least `c0*t^r`, `|h(p(t))|>=c1*t^s`, the named `externalErrorBound`,
the complete `residualBound`, and a named `nearbyZero` within radius `e(t)`.
The explicit `lipschitzAdapter` supplies `|h(z)-h(p(t))|<=L*e(t)` from closeness;
it does not assume `h(z)!=0`. Two applications of the frozen power-margin
lemma then preserve both margins on the one zero chosen from `nearbyZero`.

The cutoff can be the minimum of

`min a (min 1 (c0^R/(C*B+1)))`

and

`min a (min 1 (c1^R/((L^R*C)*B+1)))`.

Missing inputs remain explicit: the external polynomial error theorem,
nearest-zero existence and coordinate domination, and a valid local
Lipschitz/value-error adapter for the actual distinguishing polynomial.
Instantiation still must authenticate the full physical residual and legal
meaning of `h`. No algebraic coefficient replacement, real-closed-field
quantifier elimination, Nash converse, primitive-element representation,
source degree formula, all-cap jet construction, or G4 closure is formalized.
General real orders, selected-zero convergence to a center, and big-O/little-o
statements are outside this source's scope.

Verification: readback, comparison with the frozen predecessor, and a
forbidden-proof-stub scan only. No compiler, build, install, or Git mutation.
`#check` and `#print axioms` requests are included for the existing compiler
owner. They are not receipts until executed. Possible integration concern:
the compiler must resolve `G4StrictMargin` to the pinned source through its
own selected import path, and validate inherited tactic/theorem availability.
The proof uses standard `Nat.mul_le_mul_right` / `Nat.le_max_left` /
`Nat.le_max_right` arithmetic APIs; elaboration remains untested.
