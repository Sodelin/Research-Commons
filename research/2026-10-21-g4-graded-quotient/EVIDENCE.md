# Execution evidence and review scope

21 October 2026. These are hashes of preserved local source/check artifacts, not download links or a promise that the omitted programs run from this package. No private implementation paths are required to read this checkpoint.

## Locally executed evidence

- The author ran exact rational projection and correction checks successfully. A separate replay ran all three original commands (projection construction, correction invariance, and floating saved-base evaluation), each with exit status zero.
- Projection checks: 2431 labelled forests, 20 shape orbits, two independent restrictions, squarefree ordinary-generator annihilator, exact chronological-span exhaustion, nested dimensions 9/10/15/18, rational duality and block annihilations.
- Exact three-cell correction check: all four quotient blocks are unchanged by nonzero higher scale, asymmetry and placement corrections; simplified base map equals the full coefficient formula; the ordered cross term survives the last quotient.
- Separate assistant-context reviewer reran the correction check and authored an additional exact check at k=3/2 and asymmetry A=3. It checked cancellation of lower/odd terms, coefficient monomial forms through t12, restrictions, ranks, duality and nested annihilations. Both checks exited zero.
- The reviewer reused the preserved labelled generator supplier rather than independently implementing a new simulator. The universal analytic argument, not the finite example alone, proves correction invariance.
- The old approximate base evaluated in floating arithmetic has largest corrected-base component approximately 0.001155547860707563. It is not a root, exact sign certificate, validated obstruction or nonexistence proof. No new optimization or Jacobian certification was performed.

## Review disposition

Scoped PASS: corrected conditional formulation, finite exact algebra and conditional analytic lift. No positive-source existence, ordinary cap-six return, vanishing total exposure, master conclusion, external peer review or Lean verification. The historical suppliers were retained, not freshly remotely audited. CHECKPOINT.md is an editorially condensed presentation of the reviewed formulation; the hashes below identify the precise reviewed source and local checks.

## SHA-256 of preserved evidence

- `FORMULATION.md`: `1c38f4fd6ebd28cbbb10f4eb54c84a02efae7df873fea567a31266e1407bb0ba`
- `build_quotient.py`: `ca03a8e28b4e6d45d5ead85e01db7a9aced81ff813f3c735c0e231bd1a4ce6f6`
- `build_quotient.log`: `ffebe20eee7ef3d21a436b45834f2dab39e2db4a6ad188fd543fcdbb67052f50`
- `check_correction_invariance.py`: `a895dc58722672e822b75ffee3d78d233be04589780000401d313e8b3e57f8bb`
- `check_correction_invariance.log`: `f02687b1d88c4fc2bc605ea924e102db51ffa25cdbef2d32887a70674066010a`
- `evaluate_saved_base.py`: `5a2d7849d700367d62716226b218d43e1dce7239950f99c9f6078cd369f910ae`
- `evaluate_saved_base.log`: `3573b3652c5cc9587d584b71dcd5c8c3c80507d4d024c07144ba4ca4995d080b`
- `quotient.json`: `099b4096a844d5755419d76f927597e196f4c2b8edc31429be668f0cb875fdb7`
- `independent-review/REVIEW.md`: `a62ec6581ca6c71e70bb04e92941344a822e12c861edc39c3310ae2cb1789d57`
- `independent-review/check_additional.py`: `c39f9585648c021d63ec06fb74b6e506aa270b541fb222e211f8b0e7cfe31d89`
- `independent-review/additional.log`: `ec0a8b4fbb6e66e9604cf476b17830e1dcf460bdac286fdf6512c2956d9a1673`
- `independent-review/replayed-correction.log`: `f02687b1d88c4fc2bc605ea924e102db51ffa25cdbef2d32887a70674066010a`
