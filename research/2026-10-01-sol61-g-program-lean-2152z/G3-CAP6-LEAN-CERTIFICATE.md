# G3 cap-six exact Lean matrix certificate

Dedicated Sol6.1 Lean contribution, 2026-10-02. Original G3 source derivation
and ownership are preserved in
[CAP6-POISSON-INTERIOR.md, Section 3, immutable fc5a3f4](https://github.com/Sodelin/Research-Commons/blob/fc5a3f4cc34ae8e42b74732bcf6f360b35a39d7b/research/2026-10-01-sol61-g3-boundary-resume-2124z/CAP6-POISSON-INTERIOR.md).

## Precisely verified finite interface

[Lean source](program/G3CapSixDeterminant.lean),
[successful compiler/axiom log](receipts/G3CapSixDeterminant.log),
[hash/compiler/resource receipt](receipts/G3CapSixDeterminant-receipt.json).

Rows are the exact exponents 1,3,6,10,15. The five columns of J0 are lambda,
R_lambda(r)=sum from k=0 to lambda-1 of r^k, its explicit polynomial derivative,
1-r^(2lambda), and -lambda r^(2lambda-2). The last column differentiates in q
first and then substitutes q=r^2: there is no extra factor 2r.

Lean verifies `L r * U r = J0 r` for r>0, using explicit rational entries and
proved nonzero denominators. It verifies det L=1 and det U=the product of its
five diagonal entries, then transports the determinant through multiplication.
No external CAS result is trusted as a proof premise.

The exact determinant is

`3 r^8 (1-r)^10 (r+1)^4 (r^2+r+1)^4 (r^4+r^3+r^2+r+1) P20(r)`

where the full degree20 polynomial is present in the Lean source. All its
coefficients are positive; Lean proves the factor is positive for 0<r<1.
The actual scaled finite matrix has third column multiplied by w and fifth by
1/2, so its determinant is (w/2) times the displayed factor and is nonzero for
0<r<1 and w>0.

Exact theorem names: `GProgram.G3.CapSix.LU_eq_J0`, `det_L`, `det_U`,
`exact_determinant`, `J0_nonsingular`, `scaled_determinant`,
`scaled_J_nonsingular`. The printed axiom audit is exactly propext,
Classical.choice and Quot.sound; there is no sorryAx/custom unproved axiom.

## Certificate-first optimization and actual limits

The direct expansion exceeded the 2 GiB interpreter cap. The final focused
L/U proof uses one thread, a 3 GiB Lean cap and a 180-second timeout. It finished
in 60.655794 seconds, with peak child RSS 2,429,552 KiB (2.32 GiB), exit code0.
Two ordinary intermediate tactic errors were corrected locally; neither failed
attempt was represented as a proof. No memory-blocked legacy source certificate
was retried or edited.

Successful source SHA256:
`c88684e903928fbce3064f7729a5635833dae2d9cea8c4dd1b053beabd869e78`.
The receipt pins Lean4.33.1 and the exact mathlib commit and log/object hashes.

## Remaining biological and analytic obligations

This verifies the finite matrix specified by the source proof. It does not
formalize equality of that matrix with the actual analytic Jacobian of the
parameterized biological source family, the inverse-function theorem step,
positive-time regularization, or actual finite-source attainment. Those are
separate hand/source results. It is not a complete G3 boundary/interior or
recognition theorem.
