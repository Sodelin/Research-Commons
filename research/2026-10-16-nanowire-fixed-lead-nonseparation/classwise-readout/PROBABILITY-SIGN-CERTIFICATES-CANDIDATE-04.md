# What transport probabilities can certify about reflection sign

Author: dot, working with Nolan. Date: 2026-10-17 UTC.
Status: hand-proof candidate, independent review pending. No new physical counterexample or universal identification theorem is asserted.

## Summary

There are useful phase-insensitive sufficient certificates that apply to every member of the declared finite Rashba class, because they use only its exact zero-energy scattering constraints. Ordinary local charge conductance g_LL<1 or g_LL>3, measured in e²/h with current into the device, certifies positive reflection determinant for two electron channels. Channel-resolved reflection probabilities can additionally certify either sign by a strict permutation-dominance test. These rules may abstain. They do not establish that a finite local/nonlocal conductance menu identifies the sign for every admitted wire.

The generic claim that probabilities can never certify sign is therefore too strong. Conversely, generic scattering ambiguity does not prove nonidentifiability in the particular finite connected Rashba chain. An exact physical realization or a class-wide inverse theorem is still required.

## Exact common assumptions

At E=0, use the fixed loss-free two-lead model of the finite-pair packet, grounded condensate and zero-temperature linear response. There are two electron modes in each normal lead, with spin already counted. On the left lead, a sector-preserving real basis change takes the packet's electron indices (old 0,old 2) and hole basis (−old 3,old 1). Its particle-hole operator J=σ_y τ_y then becomes τ_x followed by complex conjugation. This changes neither determinant nor sector-summed probabilities.

In this canonical order write

    r = [[A,B],[B*,A*]],    s = transmission from left to right.

Here * denotes entrywise conjugation; † denotes adjoint. The full scattering matrix is unitary, so r†r+s†s=I_4, although r itself need not be unitary. Define

    R_N=||A||_F², R_A=||B||_F²,
    T=sum of transmission probabilities for the two incoming electron modes.

Then R_N+R_A+T=2 and

    g_LL=2−R_N+R_A=2R_A+T.

These follow from the same current and channel conventions already reviewed in conductance certificate 03. Particle-hole symmetry makes det(r) real. No assumption of translational invariance, a long wire or unitary reflection is introduced.

Primary suppliers: Rosdahl et al., PRB 97, 045421 (2018), Eqs. (3)–(5), https://doi.org/10.1103/PhysRevB.97.045421 ; accessible PDF https://pure.tudelft.nl/ws/portalfiles/portal/46877558/PhysRevB.97.045421.pdf (article 045421-3, PDF page 4). Beenakker et al., arXiv:1012.0932v3, Section II, gives canonical particle-hole relations and explains that its reflection-only Andreev-eigenvalue formulas additionally assume unitary r: https://arxiv.org/html/1012.0932v3 . Those reflection-only assumptions are not silently imported here.

## 1. Ordinary local conductance gives a positive-sign certificate

**Claim.** Under the preceding assumptions, g_LL<1 implies det(r)>0.

From the incoming electron block of unitarity,

    A†A + (B*)†B* + s_e†s_e = I_2.

The last two terms are positive semidefinite and have total trace R_A+T. Therefore

    sigma_min(A)² ≥ 1−R_A−T.

Also ||B||² ≤ ||B||_F²=R_A. If g_LL=2R_A+T<1, it follows that sigma_min(A)>||B||. The path

    r_u = [[A,uB],[uB*,A*]],  0≤u≤1,

is nonsingular: its block-diagonal part has smallest singular value sigma_min(A), whereas its off-diagonal perturbation has norm u||B||. The path remains particle-hole symmetric, so its nonzero real determinant cannot change sign. At u=0 it is |det(A)|²>0. This proves the claim. The homotopy is an algebraic proof device; it need not consist of realizable Rashba wires.

For two electron channels, g_LL>3 also implies det(r)>0. Indeed 2R_N+T=4−g_LL<1. Repeating the proof with normal and Andreev blocks exchanged deforms to [[0,B],[B*,0]], whose determinant is (−1)^2 |det(B)|²>0. Thus negative reflection determinant requires 1≤g_LL≤3. These are sufficient conservative inequalities, not a claimed sharp characterization.

**Readout error.** If a measured dimensionless local value y has a certified absolute error bound η and y+η<1, or y−η>3, the positive-sign conclusion follows for every admitted device compatible with that report. A point near g=2 is not certified by these rules. The previously certified plus device has g<0.004 and satisfies the first rule; the minus device near 1.209 does not. That contrast does not make the rule complete.

## 2. Channel-resolved probabilities can certify either sign

Assume the individual reflection probabilities p_ij=|r_ij|² are known or enclosed in the canonical particle/hole basis. This is stronger information than the four spin-summed charge conductances and requires a separately justified mode-resolved measurement capability.

Let π be a permutation of the four channel labels that commutes with the electron/hole pairing: π(bar i)=bar π(i). Suppose every row satisfies

    |r_(i,π(i))| > sum over j≠π(i) of |r_ij|.             (1)

Keep just the chosen entry in every row to form a monomial matrix M. Both M and r−M preserve particle-hole symmetry. After permuting columns, M+u(r−M) is strictly diagonally dominant for all 0≤u≤1. Such a matrix is nonsingular: if it killed a nonzero vector, choose a coordinate of maximal absolute value and use the strict row inequality to obtain a contradiction. Hence the real determinant retains its sign along this path.

The four selected entries form two conjugate pairs, so their product is strictly positive. Consequently

    sign det(r) = sign(π).

The identity permutation certifies positive sign. A permutation that exchanges one electron channel with its paired hole and leaves the other pair fixed has negative parity, and certifies negative sign. Thus phase information is not always necessary. No loss-free assumption is needed for this particular dominance implication beyond particle-hole symmetry, though the physical interpretation here retains the original model.

For interval probabilities, a sufficient robust version of (1) is

    sqrt(lower p_(i,π(i))) > sum_(j≠π(i)) sqrt(upper p_ij).

One can compare outward-rational square-root bounds. This handles bounded readout error without reconstructing phases. It is a conditional class-wide certificate, not a demonstration that ordinary experimental contacts resolve these channels or that every wire satisfies the condition. No claim is made that it certifies the existing minus example.

## 3. Why the scattering constraints alone do not make aggregate conductance complete

The following explicit algebraic comparison illustrates the missing inference, but is NOT an admitted finite-chain counterexample.

Take a fully reflecting two-electron-mode lead. In canonical particle/hole order define

    r_plus = [[A,B],[B,A]],  A=σ_x/sqrt(2), B=σ_z/sqrt(2),
    r_minus = [[C,D],[D,C]], C=diag(1,0), D=diag(0,1).

Both are real symmetric, particle-hole symmetric and unitary. For r_plus, A²+B²=I and AB+BA=0. Its ± particle/hole combinations give A+B and A−B, each with determinant −1, so det(r_plus)=+1. The minus matrix is the permutation exchanging the second electron/hole pair, so det(r_minus)=−1. Both have R_N=R_A=1 and hence g_LL=2. Attach an identical independent reflector at the right lead: both full scattering matrices have g_LL=g_RR=2 and g_LR=g_RL=0, and total determinant +1. Their sector-summed probabilities also agree.

This example respects even the real-symmetric scattering constraint expected from the packet's real symmetric H and scalar lead self-energy. But it has exact zero interlead transmission and supplies no realization by the connected finite Rashba chain with its fixed nonzero hopping/contact matrices. It is therefore only a counterexample to an inference from these algebraic constraints alone. Nor does it match responses at several fields/energies. It must not be promoted to a no-finite-menu theorem for the physical source class.

## 4. Exact remaining physical obligation

To establish a complete finite-menu claim, fix the admitted potentials, length, contacts, controls and noise model and prove that every pair of admitted devices with opposite target signs has disjoint observation sets for that menu. To refute it, construct actual admitted devices (with one fixed profile per device across the menu) whose local/nonlocal conductance reports overlap while the target signs retain the requested margins. The scattering matrices above do not supply those devices.

A calibrated phase-sensitive reconstruction of the full reflection matrix would directly determine its determinant when its uncertainty set excludes zero and both signs, but no such measurement protocol is established here. Additional mode-resolved probability information can already provide the narrower dominance certificate above. Neither route identifies topological protection or thermodynamic phase merely from finite-device TV sign.

## Attribution and strength

Landauer–BdG transport, particle-hole symmetry, singular-value perturbation, homotopy of invertible real-determinant matrices and strict diagonal dominance are established methods. The two sufficient certificates above are explicit applications proposed for scoped review; no historical novelty is claimed. This packet does not supersede the finite-pair conductance result, demonstrate fabrication usefulness, or establish universal conductance-only identification.
