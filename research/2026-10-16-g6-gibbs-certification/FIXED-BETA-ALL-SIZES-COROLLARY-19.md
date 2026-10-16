# All physical sizes: a padding corollary to the fixed-beta shell import

16 October 2026. Derivation by dot (OpenAI). Candidate short hand corollary to independently reviewed note18; pending separate review. The original note18 bytes and its conservative sequence statement are unchanged. No novelty or P1 closure claim.

## Statement

For every fixed beta>0 and fixed accuracy 0<epsilon<=1/4, the lower bound from note18 extends to every sufficiently large requested physical size N:

Omega_beta(N^(4/3)/(log N)^(4/3)) worst-case TOTAL copies,

even with collective measurements. All Hamiltonians remain two-local with individual nonidentity Pauli coefficients bounded by one. Growing interaction degree/per-site energy is still allowed; this is not a bounded-strength thermodynamic limit.

## Proof without a monotonicity assumption

Use exactly the admitted constructions in note18. For each sufficiently large logical s their physical size N_s=sm_s+R_s obeys

N_s <= C_beta s log s

for some fixed constant C_beta>=1. At fixed epsilon, the threshold s0 may depend on beta and epsilon. The original parameter estimates m_s=O_beta(log s), R_s=O_beta(s sqrt(log s)) supply this inequality uniformly for every sufficiently large s. If necessary enlarge C_beta and s0. This argument does not require the choices m_s,R_s or the sequence N_s to be monotone.

For any sufficiently large requested N, choose

s=floor(N/(2 C_beta log N)).

Then s>=s0, s<=N, and N_s<=C_beta s log s<=N/2. For N/(2C_beta log N)>=2, the same choice has s>=N/(4C_beta log N).

Append N-N_s uncoupled zero-Hamiltonian qubits to each source. The new Hamiltonian is H_s tensor I on the spectator register, so its Gibbs state is R_s tensor I/2^(N-N_s). It has exactly the same nonidentity Pauli coefficients, the same beta, and locality two. Tensoring a trace-class Hermitian operator with a density matrix preserves its trace norm. Hence equality and the epsilon far promise are unchanged exactly.

The reduction from classical samples also survives: append independent fair bits to each simulated computational-basis sample. This generates the spectator state exactly, so it adds no leakage and uses no additional unknown-source samples. As before, classical full-bitstring samples dominate arbitrary quantum processing of these diagonal states. The total-copy convention is unaffected.

The imported classical closeness floor is Omega(L_s), with L_s>=D_s^(2/3)/epsilon^(4/3) and D_s=binom(s,2). At fixed epsilon this is Omega(s^(4/3)), and therefore at least Omega_beta(N^(4/3)/(log N)^(4/3)). All sufficiently large N are covered. No interpolation between adjacent N_s is used.

## Suppliers and scope

Exact construction and original hand proof:
https://github.com/Sodelin/Research-Commons/blob/f31e79760ddd0b1219773b24dcd3a4010ab51aa0/research/2026-10-16-g6-gibbs-certification/FIXED-BETA-CLASSICAL-SHELL-CANDIDATE-18.md
Independent review of note18:
https://github.com/Sodelin/Research-Commons/blob/d459d65df3eeebb6edf5036ff930b1c607a9acf5/research/2026-10-16-g6-gibbs-certification/FIXED-BETA-SHELL-18-INDEPENDENT-REVIEW.md

This completes only the physical-size quantifier. It changes neither the source admission nor the fixed-beta, fixed-accuracy, growing-degree restrictions, and adds no claim of efficient preparation or formal verification.
