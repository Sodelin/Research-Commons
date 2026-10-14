# Diagonal tangent Lean scope

Contributor: delegated Codex diagonal formalization, 14 October 2026. Status: **source-authored / UNCOMPILED**. No Lean or Lake invocation, toolchain installation, Git mutation, or active-plan change was performed by this contributor. The integration owner retains compiler execution and dependency-graph ownership.

The source file is [G4DiagonalTangent.lean](lean/G4DiagonalTangent.lean), namespace `G4DiagonalTangent`. SHA-256: `f465f35b62cd9ad6eca139cee2ac990c0715dc65832ad02dd3030409772227c4`. It contains 24 theorems and 22 definitions. Static inspection found no proof holes or added axioms. This is an inspection result, not a successful elaboration or kernel receipt. Eleven substantive endpoint `#print axioms` commands are included for the compiler owner's later audit.

## Actual coverage

The principal endpoint is `source_weighted_ward_identity`: for every natural arity `n`, and every real `rho` with `1 + rho != 0`, the actual source binomial weights satisfy

    sum_k w_k (3 lambda_k + lambda_(n-k))
      = lambda_n b_n(rho,rho,1/(1+rho)).

`wardResidual_zero` proves the equivalent zero residual, and `fixed_target_all_arity_residual` specializes it to `rho=1/2`. The source summand is defined verbatim as `choose(n,k) g^k (1-g)^(n-k) x^lambda_k y^lambda_(n-k)`, not as arbitrary symmetric weights. `lambda_n` is defined as `Nat.choose n 2`; `cast_lam` proves its real quadratic expression.

`source_polynomial_partial_identity` strengthens this to `rho*(3 bigonDx + bigonDy)=lambda_n bigon` using explicit polynomial-partial sums with the actual exponent-reduced powers. Per-term multiplication by `rho` recovers the source-weighted coefficient. `power_differential_mul` handles exponent zero separately, so there is no division by `rho` or additional nonzero-`rho` premise. This supplies the full algebraic source-partial identity while leaving only its analytic derivative interpretation to the derivative adapter.

The proof derives the normalized source weights, proves their natural exponent symmetry under `k -> n+1-k`, proves `k choose(n,k) = (n+1-k) choose(n,n+1-k)`, and then proves the weighted symmetry. Only after these source-specific steps is the general reflected-sum lemma used. The positive-root sum has indices `k=1,...,n`; the unpaired `k=0` residual vanishes. Thus arities 0 and 1 are covered without a positivity or nonempty-domain assumption.

The additional endpoints prove the exact pair curve `(13/48)(1-t^2)`, its target value, its disagreement for every nonzero real `t`, and strict legality of all five curve coordinates on `-1/3<t<1/3`.

The cap-four endpoints reproduce all five target contrast/partial values and the two directional values `81/32768`. `contrastB_increment` proves an exact polynomial expansion with the stated partial polynomials as its linear coefficient. `cap_four_curve_expansion` independently extracts the coefficient `81/32768` from each actual padded contrast polynomial, with an explicit polynomial remainder multiplied by `t^2`. These polynomial identities establish the algebra underlying the hand differentiation; no analytic derivative API is used.

## Theorem inventory

| Theorems | Exact role |
|---|---|
| `lam_succ`, `cast_lam` | Natural triangle exponent and its real quadratic expression |
| `diagonalWeight_normal_form` | Normalization of the actual binomial source summand |
| `diagonalExponent_reflect` | Source exponent reflection for `1<=k<=n` |
| `binomial_weight_reflect` | Actual binomial coefficient identity on that domain |
| `diagonalWeight_reflect` | Source weighted symmetry derived from the preceding identities |
| `sum_range_eq_zero_of_reflect_neg` | General reflected finite-sum lemma, with its symmetry premise explicit |
| `positive_root_cancellation` | Source-specific cancellation on `k=1,...,n` |
| `quadratic_coefficient_identity` | Residual coefficient `k(2k-n-1)` |
| `wardResidual_zero`, `fixed_target_all_arity_residual`, `source_weighted_ward_identity` | All-arity actual source finite-sum identities |
| `power_differential_mul`, `bigonDxWeight_mul`, `bigonDyWeight_mul`, `source_polynomial_partial_identity` | Original exponent-reduced polynomial partial sums and their all-arity identity |
| `pair_curve_identity`, `pair_target_value`, `pair_curve_ne_target` | Exact pair control and failure of collision |
| `strict_curve_parameters` | Strict physical parameter interval for the single tuple |
| `contrastB_increment` | Exact source contrast polynomial coefficient extraction |
| `cap_four_target_values`, `cap_four_directional_values`, `cap_four_curve_expansion` | Exact cap-four values and actual curve linear coefficients |

## Imports and signature inspection

The nine imports are `Mathlib.Data.Real.Basic`, `Mathlib.Data.Nat.Choose.Basic`, `Mathlib.Algebra.BigOperators.Intervals`, `Mathlib.Algebra.BigOperators.Ring.Finset`, `Mathlib.Tactic.FieldSimp`, `Mathlib.Tactic.Linarith`, `Mathlib.Tactic.NormNum`, `Lean.Elab.Tactic.Omega`, and `Mathlib.Tactic.Ring`. No `Mathlib` or `Mathlib.Tactic` umbrella import is used.

Primary upstream source reads checked the signatures of `Nat.choose_succ_succ`, `Nat.choose_one_right`, `Nat.choose_symm`, `Nat.choose_succ_right_eq`, `Finset.sum_range_reflect`, `Finset.sum_range_succ'`, `Finset.sum_mul`, and `Finset.mul_sum`. The consequential choose, reflection, range decomposition and sum multiplication signatures were also checked against the accepted Mathlib pin `0df444a360eaa60ab8c11dca51a86af692955474` from `union1613/scripts/build_connected.py`, using the primary raw files at that commit. The product reflection/decomposition source declarations generate their sum counterparts through `to_additive`. The `Omega` import was corrected to the Lean module; the upstream `Mathlib.Tactic.Omega` path did not exist. Cast proofs use `congrArg` and cast simp lemmas, avoiding a separate `exact_mod_cast` import dependency. These are source-signature checks, not compiler validation. Exact dependency closure must be included in the integration owner's frozen compilation plan.

## Sources and precise remaining gates

The supplied hand source [DIAGONAL-TANGENT-COUNTERCONTROL.md](../2026-10-14-g4-independent-astra-exact-fibre-0535z/DIAGONAL-TANGENT-COUNTERCONTROL.md) has SHA-256 `a6735d8c8a59b6a26168a90b236b16576d6d3be7408f8ea760f78812660f7649`. Its companion [source_diagonal_controls.py](../2026-10-14-g4-independent-astra-exact-fibre-0535z/source_diagonal_controls.py) has SHA-256 `b50a61221ac3df9af5f0013e94ed5f820a7a33823526d1313f182f3228a1efe6`.

The scope remains **G4 master in progress**. The following gates are not supplied here:

1. Compilation and actual axiom audit of this exact Lean SHA against the selected pinned toolchain and Mathlib graph. Possible remaining uncertainty is elaboration/tactic behavior; no failed compiler check has been hidden because no compiler was run.
2. Analytic correspondence of the explicit polynomial-partial sums to `rho(3 partial_x b_n + partial_y b_n)=lambda_n b_n`, including derivative rules for the finite polynomial and the scaled padded kernel. The all-arity identity of those explicit polynomial-partial sums is established in source form; an analytic `HasDerivAt`/multivariate derivative theorem is not declared.
3. Binding the polynomial definitions to the inherited original source compiler, complete topology coordinate adapters, original graph/IDs, and once-occurring completion menu. The definitions match the supplied formulas, but that full semantic bridge is inherited and not re-proved here.
4. Source-jet cancellation of the visible cap-four response in a before/after construction, the full projected residual including body curvature, and any all-cap exact rival/common zero. No such construction, sign result, or master closure is claimed.

Next action: the integration owner freezes this exact SHA and these imports in the selected source graph, compiles it, and resolves any elaboration failure before upgrading the evidence label. The analytic adapter can then be proved against the accepted source-kernel interfaces without changing the all-arity cancellation into a hypothesis.
