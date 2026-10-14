# Conditional margin exactification: Lean source scope

Contributor: Codex delegated margin formalization, 14 October 2026. Status:
**source draft; compilation unverified**. This additive module does not alter the
accepted module graph or existing integration plan. Original argument:
[Astra MARGIN-LIFT.md](../2026-10-14-g4-independent-astra-exact-fibre-0535z/MARGIN-LIFT.md),
section 4. Astra retains ownership of the physical-jet construction.

Source: [lean/G4StrictMargin.lean](lean/G4StrictMargin.lean). Imports:
`Mathlib.Data.Real.Basic`, `Mathlib.Tactic.Linarith`, `Mathlib.Tactic.NormNum`,
`Mathlib.Tactic.Ring`, `Lean.Elab.Tactic.Omega`. Namespace: `G4StrictMargin`.
The tactic module paths were checked against the accepted connected-union1606
source store: source hashes `1ac434b5b0814a7eaba1f34df224bbf320dbe044eb6ba88dddf9b3d57b8d7f91`
(Linarith, NormNum, Ring) and `0c6dd3c3eb49ac4647707ab6e2b7a48350d113f26a0946ad5ba3486ef5546487`
(Lean's Omega). No umbrella tactic import is used.

The substantive endpoint `eventually_exists_strict_zero_of_order_gap` proves:
for a fixed coordinate type, map `F`, parameter curve `p(t)`, and constants
`a,c>0`, `C,B>=0`, suppose every `0<t<a` satisfies all of the following:

- Every coordinate and its complement are at least `c*t^r`.
- The named `externalErrorBound` gives `e(t)^R <= C*residual(F(p(t)))`.
- The named `residualBound` gives `residual(F(p(t))) <= B*t^q`.
- The named `nearbyZero` gives a tuple `z` with the **whole** equation `F(z)=0`
  and every coordinate error at most `e(t)`.
- The natural orders satisfy `q > r*R`.

Then a positive cutoff exists below which **every** positive `t` has a strict
zero: `F(z)=0` and `0<z_i<1` for every coordinate. Strictness is proved, not
assumed in `nearbyZero`. The arithmetic proof extracts an extra factor of `t`
from the strict exponent gap and proves `e(t)<c*t^r`. The cutoff is

`min a (min 1 (c^R / (C*B+1)))`.

The additional theorems are `strictCube_of_coordinateMargin`,
`exists_strict_zero_of_coordinate_error`, `pow_le_one_of_unit_interval`,
`pow_le_lower_power_mul`, `error_lt_power_margin`,
`exists_strict_zero_of_power_error_bound`, and `positive_cutoff`.

The analytic inputs remain premises. A real source consumer must instantiate
`F` with every capped residual row on one raw physical tuple, take `residual`
to be the appropriate residual norm, supply a valid polynomial error bound,
and supply a zero whose coordinate errors are dominated by the corresponding
distance/error radius. This file does **not** prove the external Kurdyka bound,
finite-dimensional nearest-point existence, a norm-to-coordinate adapter,
the physical degree formula, Nash curve selection, the finite-jet converse,
later distinguishing-polynomial preservation, an all-cap jet family, or G4.
It does not formalize general real orders, the `O(t^(q/R))` / little-o estimate,
or convergence of the selected zeros to a boundary center. Natural jet orders
and a natural valid error exponent cover the stated finite-jet threshold.

Local checks: source readback and forbidden-proof-stub scan only. No Lean
compiler is on PATH; no installation or build was attempted. The module
contains actual tactic proofs and `#print axioms` commands for the integration
owner to run. Those commands are **not** execution evidence until compiled.
Next action: the existing integration owner compiles this exact source and
audits its printed dependencies before selecting it for the accepted graph.
