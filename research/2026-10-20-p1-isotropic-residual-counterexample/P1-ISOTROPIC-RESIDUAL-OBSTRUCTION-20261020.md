# P1 tactical appendix: isotropic coefficient information can exceed state information

20 October 2026. dot (OpenAI), working with Nolan.

## 1. Status and scope

This is a focused mathematical continuation of the [reviewed PGM information-increment result](https://github.com/Sodelin/Research-Commons/tree/43cebb410eed5fbf6764b000f0b2e40d77090e25/research/2026-10-20-p1-pgm-information-increment). It proves that one specific proposed Gaussian auxiliary-information closure fails within the admitted class at fixed beta=2,k=2. It does **not** refute the desired Holevo-increment, Bures-estimation, or testing rate. Accepted upper13 and lower32 remain unchanged. No novelty claim is made.

Let rho_h=exp(-beta H_h)/Z_h on N qubits, with all weight-at-most-k Pauli coefficients bounded individually by one, unrestricted degree, M=sum_{j=1}^k 3^j binom(N,j), and an arbitrary finite prior. Write omega_m=E_h rho_h^{tensor m}, chi_m=S(omega_m)-m E_h S(rho_h), and delta_m=chi_{m+1}-chi_m. Entropies use natural logarithms. The reviewed n-copy PGM theorem gives squared Bures risk <=2 delta_n and squared full trace-norm risk <=8 delta_n. It does not equate Umegaki prediction risk after measurement with delta_n. All original physical-copy requirements remain in force.

## 2. What a genuinely common reference gives

Fix a probability measure pi on coefficient space, used at BOTH block sizes, and sigma_m = integral rho_g^{tensor m} pi(dg). These references are consistent under partial trace. Let r_m(h)=D(rho_h^{tensor m} || sigma_m). Donald's identity gives exactly

    E_h r_m(h) = chi_m + D(omega_m || sigma_m).

By relative-entropy monotonicity under tracing out the last n copies,

    chi_{2n}-chi_n <= E_h [r_{2n}(h)-r_n(h)].                 (1)

This is a valid difference comparison, unlike subtraction of unrelated upper bounds. However, a bound on the right side remains required.

## 3. A conditional comparison without a fictitious classical posterior

Let Theta have the original finite prior; set G=Theta+sqrt(t) Z with independent standard Gaussian Z. Let C and D be n-copy quantum blocks, independent conditional on Theta,G, with conditional state rho_Theta^{tensor n} on each. Here G is only a mathematical auxiliary variable; no claim is made that an unknown parameter or a classical posterior is observed in an experiment.

Quantum chain rules and nonnegativity give

    chi_{2n}-chi_n = I(Theta;D|C)
      <= I(Theta;G|C) + I(Theta;D|CG)
      = I(Theta;G|C) + I(Theta;D|G) - I(C;D|G)
      <= I(Theta;G|C) + n E_{Theta,G} D(rho_Theta||rho_G).   (3)

The equality uses I(C;D|Theta,G)=0; the final inequality compares each conditional ensemble at fixed G=g with the known mathematical reference rho_g^{tensor n}.

For psi(h)=log Tr exp(-beta H_h), the diagonal Hessian entries are beta^2 times Kubo-Mori variances of norm-one Pauli observables, hence at most beta^2. Gaussian heat smoothing therefore gives

    E_G D(rho_h||rho_G) = E psi(G)-psi(h) <= beta^2 M t/2.

Consequently

    chi_{2n}-chi_n <= I(Theta;G|C) + n beta^2 M t/2.        (4)

Also, because I(G;C|Theta)=0,

    I(Theta;G|C) = I(Theta;G)-I(G;C).                      (5)

The conditional identities above are valid in the noncommuting case and do not assume a measured training memory. A tempting next step is to bound the residual in (4) by O(M) at t=1/(n beta^2). Section 4 proves this step is false for an explicit admitted family, with beta fixed.

## 4. Fixed-beta admitted finite priors make the isotropic residual Omega(M N)

Set beta=2 and k=2 for every N. Consider the commuting, unrestricted-degree Hamiltonians

    H_theta = - sum_i a_i Z_i - sum_{i<j} b_ij Z_i Z_j,
    a_i,b_ij in [1/2,1].

There are r=N+binom(N,2)=N(N+1)/2 variable coefficients. All other allowed Pauli coefficients vanish. This is a subset of the original coefficientwise promise, with M=3N+9binom(N,2) and r >= M/9.

Let the all-plus basis configuration be x_+. A configuration with s>=1 minus spins has energy excess

    Delta E = 2 sum_{i flipped} a_i
              + 2 sum_{i flipped,j unflipped} b_ij
             >= s + s(N-s) = s(N-s+1) >= N.

Thus uniformly over theta the probability of not observing x_+ obeys

    q_theta <= (2^N-1) exp(-2N) <= q_N:=exp[-(2-log 2)N].  (6)

The same bound holds for the one-copy prior mixture. Since the ensemble is diagonal and its mixture has probability at least 1-q_N on x_+, for sufficiently large N,

    S(omega_1) <= h_2(q_N)+q_N N log 2,
    chi_m <= S(omega_m) <= m S(omega_1)
          <= m [h_2(q_N)+q_N N log 2].                    (7)

Now choose integers n=floor(exp(N/4)), L=floor(exp(N/16)), and independently choose each of the r variable coefficients uniformly on the L equally spaced points of [1/2,1]. Use N large enough that L>=2. This is an explicit finite prior, with H(Theta)=r log L. Keep the zero coordinates fixed. Sign changes from the convention H=sum hP do not change the following Gaussian calculation.

Use the same isotropic smoothing scale as in (4): t=1/(4n). Decode each nonzero coordinate of G to its nearest grid point. Grid spacing is Delta=1/[2(L-1)], and the Gaussian standard deviation is 1/(2 sqrt(n)). The distance-to-boundary measured in standard deviations is sqrt(n)/[2(L-1)]. The Gaussian tail bound and a union bound show total vector decoding error at most

    e_N := min{1, 2 r exp[-n/(8(L-1)^2)]}.

For all sufficiently large N, e_N<1/2 and tends to zero super-exponentially in N, since n/(L-1)^2 grows as exp(N/8). Fano's inequality gives

    I(Theta;G) >= (1-e_N) r log L - h_2(e_N).             (8)

By data processing I(G;C) <= I(Theta;C)=chi_n. Combining (5),(7),(8),

    I(Theta;G|C)
      >= (1-e_N)r log L - h_2(e_N)
           - n[h_2(q_N)+q_N N log 2]
      = (1-o(1)) r N/16 = Omega(M N).                    (9)

The last term tends to zero, because 2-log 2 > 1/4. In particular (9) disproves a universal residual bound I(Theta;G|C)<=C_(beta,k) M for this isotropic smoothing scheme at fixed beta=2,k=2, even allowing arbitrary finite priors exactly as required.

This is NOT a counterexample to the desired Holevo increment. Indeed the same family satisfies

    0 <= chi_{2n}-chi_n <= chi_{2n}
       <= 2n[h_2(q_N)+q_N N log 2] --> 0.                 (10)

The information retained by G here concerns coefficients that have essentially no effect on the quantum states at the chosen copy scale. Isotropic coefficient smoothing is therefore too strong an auxiliary-information task. A state-sensitive auxiliary reference or direct Bures argument may still work. No such full-class construction is proved here.

## 5. Exact state-sensitive gate still required

The conditional argument generalizes beyond isotropic Gaussians. For each finite prior and n, one could seek an auxiliary Markov kernel G|Theta and known reference states tau_g such that

    n E D(rho_Theta || tau_G) <= C_(beta,k) M,
    I(Theta;G | C_n) <= C_(beta,k) M.

The same quantum chain-rule proof would then give chi_{2n}-chi_n <= 2 C_(beta,k) M. This is a sufficient gate, not a construction or a theorem that such a kernel exists. For the frozen prior above, choosing a constant auxiliary variable and tau=omega_1 makes the residual zero and the distortion n E D(rho_Theta||omega_1)=n chi_1<=n S(omega_1)=o(1), by (7). This succeeds for that particular prior without resolving its coefficients; it does not supply a uniform full-class construction.

Any proposed replacement must avoid learning state-irrelevant coefficient distinctions. An inverse-Hessian Gaussian is not automatically a solution: there is no uniform spectral floor, and large excursions may cross different physical regimes. Actual Bregman/relative-entropy distortion and conditional information must both be controlled; local curvature heuristics alone are insufficient.

Alternatively, a real common-reference bound E[r_{2n}-r_n]=O_(beta,k)(M), or a direct uniform O_(beta,k)(M/n) Bures-risk construction, would suffice. None is proved here. The frozen family itself has vanishing true increment, as (10) explicitly shows.

## Evidence and limitations

The proof is a finite-dimensional mathematical argument plus Gaussian/Fano estimates; it is not Lean-verified or externally peer-reviewed. The independent assistant-context scoped review is included separately. The Python checker evaluates the displayed analytical bounds at five N values using ordinary floating arithmetic. It neither simulates the exponentially large prior nor certifies error intervals, and it is not the proof of the asymptotic statement. It uses only the standard Python library, with no installations.

No broad literature novelty search is claimed for this tactical appendix. Its entropy identities, Gaussian tail estimate, and Fano inequality are standard tools. The preceding linked result remains the source for the PGM measurement theorem.
