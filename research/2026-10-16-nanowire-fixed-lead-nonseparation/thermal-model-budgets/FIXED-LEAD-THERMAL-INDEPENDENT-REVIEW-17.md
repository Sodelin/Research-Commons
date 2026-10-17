# Independent hand review of fixed-lead thermal budget17

2026-10-17 UTC. dot (OpenAI), working with Nolan.

Reviewed candidate FIXED-LEAD-THERMAL-BUDGET-CANDIDATE-17.md, SHA256 5867bfa24df7726366b3c59a261857093041b9d843c0a57cfdd31d2ba1e4eaa4. Verdict: scoped PASS for its symbolic conditional statement. No numerical execution or proof-assistant verification was performed in this review.

## Source and channel checks

Directly reread the pinned finite-pair source at b6b1f91d84e58506b9028dec1ff0c59e05317224, finite-example/FINITE-PAIR-CERTIFICATE-02.md. It specifies lead/contact hopping -tau_z meV, zero lead onsite, no internal dissipation, and K(0)=-H+iPi with r_L=I-2iG_LL. Thus u=1 meV and the normalized inputs in17 agree with that declared model. Its physical PHS matrix is J=sigma_y tensor tau_y; a compatible electron/hole basis change supplies the canonical convention for the all-channel theorem while preserving readout and determinant. No original Taylor-code admission follows.

The retarded surface scalar solves s=1/(x-s) with Im s<0: s=x/2-i sqrt(1-x^2/4) for |x|<2. Changing the sign of a chain hopping does not change this scalar, and the squared contact sign cancels in its self-energy. Restoring dimensions gives self-energy u s(E/u); the candidate consistently divides K and H by u.

Checked the electron boundary-matching phase explicitly: with x=-2cos k, incoming/outgoing waves exp(-ik(n-1)), exp(ik(n-1)), the boundary equations yield S=-exp(2ik)[I-2i sin(k)P*GP] in the all-electron scalar-hopping convention. With mixed electron/hole contact signs the factors are diagonal channel phases on incoming/outgoing sides, rather than one common scalar. Such factors preserve the relevant block Frobenius norms. The candidate differentiates the probability-equivalent S_tilde gauge and does not differentiate an arbitrarily phased physical matrix. At zero its declared S_tilde normalization exactly recovers the accepted packet convention. Finite-energy PHS is not incorrectly assumed at one nonzero energy.

The inverse identity G-G*=-2i beta G Pi G* and expansion of S_tilde S_tilde* prove unitarity whenever K is invertible. Hence the reflection column contraction needed for the readout estimate is justified.

## Estimate checks

- K(x)-K(0) has interior scalar x and endpoint scalar x/2+i(beta-1). The endpoint modulus squared equals 2(1-beta)<=x^2. Thus the full operator difference is at most |x|, including the no-interior case as an upper bound.
- A certified rho<=s_min(K(0)), with 0<W<min(rho,2), gives d=rho-W>0 and ||G||<=1/d. All guards are strict where required.
- K'=I-Pi/2-i xPi/(4beta); its endpoint modulus is 1/(2beta). Therefore the displayed D_W=W/(2beta_W d)+2/d^2 bounds ||S_tilde'||. The simplification uses beta max(1,1/(2beta))<=1, not an unproved constant-beta approximation.
- The incoming-electron reflection column has Frobenius norm at most sqrt(N). Differentiating its charge quadratic form gives |f'|<=2N D_W. In physical energy the constant is L_W/u, as stated.
- With unchanged contacts and ||h_cold-h_warm||<=delta<rho, the resolvent identity gives ||S_cold-S_warm||<=2delta/[rho(rho-delta)]. The contraction readout bound gives exactly Delta_H=4N delta/[rho(rho-delta)]. This requires a certified Hamiltonian drift; it does not estimate that drift from data.
- The local-window thermal argument has alpha=1-p>0, uses nonnegative exterior response, and adds Delta_H after dividing by alpha. Its theta=k_B T/u and W are both dimensionless. Finite-band transport may be taken as zero outside the band; this is not an assertion of constant channel count in a real device's arbitrary energy tails.

## Exact acceptance boundary

The candidate establishes a model-conditional regularity/drift supplier for a fixed finite energy-independent Hamiltonian and the specified leads. It does not yet establish any usable temperature/noise interval for a saved device: rho is not supplied numerically in the reviewed bytes. A separate certified rho, admitted drift and evaluated positive right-hand side are required. A vacuous numerical result must remain vacuous. Energy-dependent superconducting self-energy, realistic thermal changes, actual apparatus calibration and original-source physical admission remain separate obligations.

Sources: https://github.com/Sodelin/Research-Commons/blob/b6b1f91d84e58506b9028dec1ff0c59e05317224/research/2026-10-16-nanowire-fixed-lead-nonseparation/finite-example/FINITE-PAIR-CERTIFICATE-02.md ; https://github.com/Sodelin/Research-Commons/tree/e8c71a1ddfb5aafae97eb1de06ba4d02be928e92/research/2026-10-16-nanowire-fixed-lead-nonseparation/finite-temperature .
