# ProofBridge: one checked integer rounding step

The original input remains a `commons.linear-int.v1` record with an exact, independently hash-pinned target and supplied nonnegative multipliers. The extra input is one concrete scale `g` in [1,1000]. The weighted intermediate must prove `g(a·x) ≤ g(b+1)−1` with the existing coefficient and bound limits. The generated Lean consumer imports that checked theorem, clears all original premises, and verifies `a·x ≤ b` by integer arithmetic. The extension is not valid over rational variables. No solver search, multiple cuts, or general SMT reconstruction runs here.

```sh
python3 test_rounded_witness.py /path/to/pinned/lean
```

The two examples accept `x≤1` from `2x+y≤3, −y≤0` and `x≤−2` from `2x+y≤−3, −y≤0`. Neither admits an unscaled integer combination with those target coefficients (it would require `2m₁=1`). The one-unit stronger targets are false at `(1,0)` and `(−2,0)`. In both tests the same consumer also rejects a valid imported provider with a bound too weak to round to the original target. [Cloud machine receipt](rounded-witness.receipt.json).

Related: [bounded SMT witness baseline](smt_witness.py), [checked import route](import_reduced.py), [Chvátal's cutting-plane work](https://doi.org/10.1016/0012-365X(73)90167-2). This is a proof-checking capability, not a novelty or conjecture claim.

## Discover the scale and multipliers

`smt_rounded.py` accepts a pinned `commons.linear-int.goal.v1` record without a witness. The QF_LIA query jointly searches bounded integer multipliers and one positive scale. The query also limits the scaled coefficients and bound to the checker's existing numeric range. The solver's output has no proof authority: it must satisfy the exact generated certificate and pass the Lean provider and importing consumer. No-witness means only no witness for this bounded rule; a timeout is inconclusive.

```sh
python3 test_smt_rounded.py /path/to/libz3.so /path/to/pinned/lean
```

[Cloud replay](smt-rounded.receipt.json): both the positive and negative-bound examples found scale 2 and multipliers [1,1], with no witness at scale 1; both one-unit false overclaims found no witness up to scale 8 and have explicit counterexamples. The earlier pinned Goldbach budget implication also replayed with scale 1 and the same 187 conditional target, without addressing the analytic estimates. Z3 was executed through the existing library adapter. No Mathlib adapter or general SMT reconstruction is implied.
