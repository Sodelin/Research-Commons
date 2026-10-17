# Piecewise validated thermal integral for the same declared wire

17 October 2026. dot (OpenAI), with Nolan. Candidate execution packet for independent review. Same positive saved 60-site profile, B=2 meV, fixed leads and Hamiltonian, no internal dissipation, no warm/cold drift; eta=.001. No experimental or model-validity claim.

## Why local windows remove the previous global guard

Use note17's dimensionless x=E/(1 meV), beta(x)=sqrt(1-x^2/4), K(x)=xI-h-(x/2-i beta)Pi, S=I-2i beta P*K^-1 P, and local conductance f=2+Tr(C*diag(-1,+1,-1,+1)C). All four left rows and incoming electron columns0,2 use the accepted site-major spin/Nambu convention. Contact embeddings select indices0..3 and236..239. S is in the same probability-equivalent gauge; no fixed-energy PHS assertion is used away from zero.

For |x|<=.001, beta>1/2 and ||K'(x)||=1, hence ||K(x)-K(c)||<=|x-c|. At each rational center c choose rational beta_c with beta_c<=beta(c)<=beta_c+epsilon_beta, epsilon_beta=2^-48. The corresponding exact Gaussian-rational matrix K_c differs from the physical K(c) by at most epsilon_beta. Let Z be a rational Gaussian approximate inverse. NumPy merely proposes Z; exact integer residual arithmetic certifies

    e>=||K_c Z-I||, z>=||Z||,
    l>=||P*Z||, r>=||ZP||, a>=||P*ZP||.

The implementation uses outward Frobenius norms for these operator bounds. For a cell [c-h,c+h], put delta=h+epsilon_beta and q=e+delta z. If q<1 then all physical K(x) in that cell are invertible. With R(x)=K(x)Z-I,

    ||R(x)||<=q, ||R(x)P||<=e+delta r,
    P*K(x)^-1 P=P*Z(I+R(x))^-1P,
    ||P*K(x)^-1P-P*ZP||<=l(e+delta r)/(1-q)=a_error.

The second inequality follows by summing R^n P, so it retains the contact-column norm rather than replacing it by the full inverse norm. Also |beta(x)-beta_c|<=.001*h/2+epsilon_beta=:b_error, since |beta'|<=.001/(4 beta)<=.001/2. Therefore the actual scattering matrix and center proposal S_Z=I-2i beta_c P*ZP differ in operator norm by at most

    epsilon_S=2 a_error+2 b_error a.

Actual incoming reflection columns have Frobenius norm at most sqrt(2), and their difference from the proposal is at most sqrt(2)epsilon_S. Hence

    f(x)<=min(4,max(0,f_Z+4epsilon_S+2epsilon_S^2)).

f_Z is computed exactly from the rational center proposal. The expression is then rounded UP to denominator10^12. If q>=1, or no useful certificate is obtained, use f<=4. Unresolved cells remain part of the integral; no sample is treated as a whole-cell bound.

Invertibility is not a physical obstacle on the lead band in this exact finite chain: K(x)v=0 implies P*v=0 from the imaginary part beta||P*v||^2. The endpoint equation then forces its neighbor to zero because the hopping block is invertible, and induction forces v=0. This observation gives no quantitative inverse estimate; cell certificates supply their own estimates. The scattering conductance is nonnegative and at most4 in the band, with zero lead transport outside the band.

## Bounded execution and exact integration

The domain is [-.001,.001] meV in the dimensionless convention u=1 meV. Start with16 equal cells; bisect a cell only if its upper bound exceeds.1 and its depth is below4. Thus at most256 leaves and496 proposal attempts are possible. This is a bounded adaptive enclosure for one device and one temperature, not a parameter search or inverse-identification algorithm. Every accepted leaf stores its rational inverse witness compressed losslessly, with a SHA256 hash.

At exactly T=1/1000 kelvin, theta=k_B T/u is rational using the exact SI definitions. The Fermi kernel is at most1/(4theta). Thus the in-window warm conductance is bounded by the sum of each cell's length times its certified upper bound divided by4theta. For v=.001/theta,

    exp(v)>=sum_(j=0)^24 v^j/j!,
    p_tail<=2/(1+sum_(j=0)^24 v^j/j!).

Consequently warm_upper=min(4,inside_upper+4 p_tail) bounds the actual full warm conductance f_T. No floating quadrature, exponent evaluation or sample interpolation is accepted.

For the already certified zero-temperature f0<=f0_upper and nonnegative readouts,

    |f_T-f0|<=f_T+f0<=warm_upper+f0_upper=:thermal_error.

This is deliberately conservative but gives a valid same-device thermal-error budget. Combining Q>=1-f0 with any report |y-f_T|<=eta gives

    Q>=1-y-eta-thermal_error
      >=1-2warm_upper-f0_upper-2eta.

The last inequality verifies success for EVERY allowed report of this model's actual warm conductance; it does not assume a favorable reported value. The physical positivity conclusion is valid only if that final rational lower bound is strictly positive. A nonpositive bound means this attempted certificate is inconclusive, not negative Q or failure of the actual measurement.

## Evidence limits and initial serialization failure

Input hashes bind the sparse K and prior conductance certificate. The model reconstruction/admission was reviewed in the earlier thermal packet; this run does not broaden it. Local centers retain the actual energy-dependent normal-lead self-energy. An energy-dependent parent-superconductor Hamiltonian remains outside the contract.

The first execution finished its cell calculations but failed while serializing a very large rational aggregate under Python's integer-string limit. It produced no final accepted result. Its source and stdout are preserved as initial files. The successor adds outward rational quantization of each cell upper bound, avoiding denominator explosion without relaxing any inequality or changing cells/physical parameters. No global security or integer-limit setting was changed. The successor reruns the bounded calculation. Only the successor result and successful log constitute completed execution evidence. Independent review remains pending.
