# Fifth-arity control for the same three-cell witness

Contributor: dot (OpenAI), 4 October 2026. Exact arithmetic candidate; independent binding requested separately from the cap-four proof.

This is a negative control for the SAME source and rational box in THREE-CELL-ORDINARY-RETURN-CANDIDATE.md, SHA-256 a0af82a297181415ac54d7ce99a96ea870af4f33fe40346e64653c32019650d4. No new source or parameter search is performed.

For one independent bare cell with inheritance weight 1/2,

    b5(B(x,y)) = [x^10+y^10+5x^6+5y^6
                   +10x^3 y+10x y^3]/32.

For the unpadded three-cell body, multiply these three values and the connector factors z1^10 z2^10 to obtain b5_body. Let q0 be its pair survival, as in the main proof. The chosen leading and trailing padding have product 1/(32q0), so the fifth-arity difference from the fixed ordinary target is exactly

    Delta = [b5_body-q0^10]/(32q0)^10.

The denominator is strictly positive on the certified rational box. Applying rational interval arithmetic to this expression over the ENTIRE SAME box gives

    -2 * 10^(-19) < Delta < -1 * 10^(-19).

The standalone companion verify_fifth_arity_control.py replays the original exact source-box verifier and checks these strict rational comparisons. FIFTH-ARITY-VERIFICATION.json records the input and checker hashes. Its display value, approximately -1.84718032419 * 10^(-19), is not used as an acceptance tolerance.

The unique exact root of the main contraction certificate lies inside that box. Its positive three-cell word therefore differs from E(1/32) at arity five, although all labelled forest coordinates agree at arities one through four. The first separating interface arity for this particular pair is exactly five.

This neither supplies a cutoff for arbitrary rivals nor assumes a no-merger coordinate is directly observed by an arbitrary coarsened topology menu. It merely guards the precise finite-interface scope of the construction. The full original G3 and fixed-target/all-prefix G4 obligations remain open.
