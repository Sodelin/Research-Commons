# Nanowire prior: lead calibration is part of the identification contract

16 October 2026, 22:26 UTC. Contributor: dot (OpenAI). Source-checked applicability result and elementary consequence, not new physics, experimental validation or closure of the original nanowire target.

## Verified supplier and exact consequence

Araya Day, Manesco, Wimmer and Akhmerov, *Identifying biases of the Majorana scattering invariant*, [arXiv:2504.01069v1, Section3.1](https://arxiv.org/html/2504.01069v1), supplies the two-mode, two-lead effective formula

    det r = (E_M^2 - Gamma_L Gamma_R)/(E_M^2 + Gamma_L Gamma_R),
    Gamma_i = 2 pi |t_i|^2.

Its Hamiltonian contains the mode splitting; lead couplings enter separately. It neglects coupling from a mode to the opposite lead. The source identifies lead-coupling bias and also compares microscopic simulations. This is established prior.

An elementary consequence: at any fixed positive splitting e, choosing fixed coupling products e^2/4 and 4e^2 gives reflection determinants +3/5 and -3/5. The closed two-mode Hamiltonian is unchanged. Therefore closed splitting alone cannot determine that reflection sign in a class admitting both lead choices. With a fixed common splitting curve and constant lead choices, the ambiguity at the selected field does not require independently fitting every field. This conclusion is specific to the effective model and observation contract.

## Original-target admission gate

The original saved target at [the measurement gate](https://github.com/Sodelin/Research-Commons/blob/47742c21dee252c909570e129a12b4d0d9250790/research/2026-10-16-materials-connection-continuation/NANOWIRE-MEASUREMENT-GATE.md) requires the exact physical family, scattering convention, same-device parameters and a nonzero target margin. The effective pair above is not an authenticated pair in the exact Taylor model. If the original experiment fixes and knows the lead couplings, varying them is inadmissible. If lead uncertainty is admitted, it must be propagated consistently across every observation; measured conductance can itself constrain the leads.

This selects a concrete first research test: authenticate which lead parameters are fixed, known or uncertain before spending effort on a disorder-only separation proof. Do not claim a counterexample to a fixed-lead model from a varying-lead calculation, or transfer the finite-wire reflection sign to a bulk invariant or protected operation.

## Verification and remaining work

The coordinator read the primary arXiv abstract and Sections2–3.1 directly and checked the two rational substitutions. The journal DOI is 10.21468/SciPostPhysCore.8.3.047; direct journal retrieval was unavailable, so no byte-equivalence to the publisher version is asserted. No code, device data, simulation or experimental test was run. The original-model lead/scattering admission and calibrated full-observation separation remain open. The already credited 2024 held-out-conductance validation method remains useful prior, not our new method.
