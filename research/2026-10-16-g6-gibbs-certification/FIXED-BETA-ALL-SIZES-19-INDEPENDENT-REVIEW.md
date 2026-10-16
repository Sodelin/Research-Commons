# Independent review: all-size padding corollary 19

16 October 2026. Independent mathematical hand review by OpenAI assistant for Nolan. **Scoped PASS.** Reviewed `FIXED-BETA-ALL-SIZES-COROLLARY-19.md`, SHA256 `05e2dbff9d0acfe5b183b003488fe2af7418a5722b0e7810330326e94dce4583`, in full. No execution or formal verification is claimed.

The previously reviewed construction supplies a uniform upper envelope N_s<=C_beta s log s for every sufficiently large s at fixed beta and accuracy. It need not supply a monotone sequence. Taking C_beta>=1 and s=floor(N/(2C_beta log N)) gives N_s<=N/2 once s is in that regime. For N/(2C_beta log N)>=2 it also gives s>=N/(4C_beta log N). Thus the original Omega(s^(4/3)) lower bound becomes the stated Omega_beta(N^(4/3)/(log N)^(4/3)) lower bound for every sufficiently large N.

The zero-Hamiltonian spectator construction preserves beta, locality and individual Pauli coefficients. Tensoring the source difference with a density matrix preserves its full trace norm exactly. The sample-only reduction appends independent fair bits, incurs no new leakage and consumes no unknown-source samples. Equality, the far promise, arbitrary collective processing and the hard total-copy convention therefore survive.

This corollary validly removes the size-sequence restriction without a monotonicity assumption. It does not remove fixed accuracy, coefficientwise admission, growing degree/per-site energy or unresolved novelty restrictions. The original note18 and its review should remain unchanged as historical artifacts, with this subsequent completion linked separately.
