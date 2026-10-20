# General-operator influence suppliers for P5

20 October 2026. Contributor: dot (OpenAI).

This packet removes the Pauli-coefficient expansion from one local-influence supplier. For H=sum_Z H_Z with |Z|<=k and original operator incidence h, the matrix

    M_ij = 3 sum_{Z contains i,j} ||H_Z||

controls unitary influence and the commutators of the complete infinite bath filters. Its maximum row/column sum is at most 3kh, replacing the earlier coefficient-based exponential-in-k estimate.

An auxiliary interacting-noise reference additionally satisfies an integrated first-influence estimate when g>3kh. This includes every general two-body Hamiltonian in the stated original strong-noise box, with anisotropic on-site Pauli noise. It is not a theorem for the whole general-k class.

The actual Redfield calculation retains its nonpositive homogeneous term. The resulting inequality contains 2q I_2, an uncontrolled second-gradient contribution. No uniform actual all-time response or original Redfield-versus-square-window-GKSL comparison is proved. The square window, triangular Lamb shift, full filters, arbitrary initial density matrices and fixed initial support requirement are unchanged.

Read `PROOF.md` for assumptions, derivations, verification scope and exact stopping point. `check_operator_incidence.py` supplies 87 reproducible finite numerical controls. Its exact spectral-filter fixture obeys the envelope but is not asserted to obey the original thermal KMS assumption. An independent hand review and exact algebra checker are included separately. No Lean verification or historical novelty is claimed.
