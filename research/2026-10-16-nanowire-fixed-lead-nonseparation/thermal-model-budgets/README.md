# Model-specific thermal certificates: valid but conservative

17 October 2026 UTC. dot (OpenAI), with Nolan.

This packet supplies an exact finite-energy lead/resolvent adapter and reproducible thermal budgets for the unchanged positive 60-site mathematical wire at B=2 meV. It combines reviewed hand proofs with exact integer/rational residual certificates. It is not Lean verified and establishes no useful laboratory-temperature guarantee or historical novelty.

## Results and limits

- The original global inverse bound certifies a chosen sufficient temperature about 5.24444e-12 K, error 0.001 e²/h, identical warm/cold Hamiltonian, and Q>0.98119.
- Contact-projected bounds retain exact matrix-product cancellations. The strongest of four predetermined sufficient choices reaches about 9.75154e-7 K, with the same error/drift/model and Q>0.90922. This removes conservatism from a bound; it does not improve a device.
- Neither temperature is claimed optimal. The original bound cannot certify positive Q at T>=1 mK for any allowed window when y>=0 and error is 0.001. That is a limitation of that bound, not a physical impossibility or a limitation of all methods.
- Both calculations first bound the model's actual thermally convolved response, then cover every reported y within the specified error. No favorable measurement is invented and no experiment was performed.
- The 1 eV endpoint barrier's effective-model realism remains unestablished. Energy-dependent proximity self-energies, temperature-induced Hamiltonian changes and experimentally justified calibration remain additional obligations.

## Contents and reproduction

[Proof17](FIXED-LEAD-THERMAL-BUDGET-CANDIDATE-17.md) retains its original candidate header; its [independent hand review](FIXED-LEAD-THERMAL-INDEPENDENT-REVIEW-17.md) records the accepted scope.

[Exact original certificate explanation](thermal-budget-execution/CERTIFICATE-EXPLANATION.md) explains the saved inverse, residual and rational thermal inference. The [independent verifier/review](thermal-budget-independent/INDEPENDENT-REVIEW.md) reconstructed the matrix and replayed the integer certificate without recomputing a floating inverse. Run `python thermal-budget-independent/check_saved_certificate.py`; dependencies are the adjacent saved data. The author proposal generator uses installed NumPy, but the independent verifier uses the standard library only. Do not use Python -O.

[Contact-projected proof](CONTACT-PROJECTED-THERMAL-DERIVATIVE-REVIEW-20261017.md), [execution handoff](contact-projected-execution/REVIEW-HANDOFF.md) and [coordinating replay](contact-projected-execution/COORDINATING-REPLAY.md) preserve their historical statuses. The coordinator subsequently approved this complete packet after reading the derivation/checker and replaying all four rational controls. Run `python contact-projected-execution/check_contact_budget.py`. This is a replay of the same checker, not a separately implemented second contact checker.

All inputs, original/initial logs and scripts are preserved. Exact SI constants are k_B=1.380649e-23 J/K and 1 meV=1.602176634e-22 J. Conductance is in e²/h; electron channels include spin. The leads/contact hoppings are -tau_z times 1 meV, with zero lead onsite and no internal dissipation.

The methods are classical surface Green functions, resolvent perturbation, norm enclosures and thermal probability bounds. The [classical conductance audit](../conductance-classical-audit/README.md) supplies the prior classification. Later refined piecewise candidates are not included or accepted by this packet. MANIFEST.json records exact byte sizes and SHA256 hashes.
