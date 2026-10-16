# Quantum shell encoding and an imported single-copy lower bound

Date: 2026-10-16. Attributed derivation by OpenAI assistant for Nolan. Status: complete hand-proof candidate, awaiting independent review; no Lean or execution claim. P1 remains open. The testing lower bound is imported from Chen–Huang–Li–Liu (CHHL), not claimed original. Novelty of this specific Gibbs encoding/import has not been established.

## Statement and primary supplier

Use the original n-qubit Gibbs class: H is a real linear combination of nonidentity Hermitian Pauli strings of weight at most k, with each coefficient in [-1,1]; the common inverse temperature beta is known. Distinguish equality of two unknown Gibbs states from trace-norm separation at least epsilon, with error at most 1/3. Here an adaptive single-copy protocol measures just one supplied state copy at a time, retains only classical information between copies, and may choose the next source adaptively. The budget is a worst-case total across both sources.

Let 2 <= k <= n, r=floor(k/2), d=binom(n,r), d sufficiently large, and 0<epsilon<=1/24. Set

L=d^(3/2)/epsilon^2, eta=1/(100L), lambda=n log(2)+log(100L).

If beta >= n lambda + d log(4d), this experiment requires Omega(d^(3/2)/epsilon^2) total copies. For fixed even k this is Omega_k(n^(3k/4)/epsilon^2), at the stated varying-beta regime. For odd k retain floor(k/2). It is not an unrestricted collective lower bound or a fixed-beta improvement.

Primary source: Sitan Chen, Brice Huang, Jerry Li and Allen Liu, *Tight Bounds for Quantum State Certification with Incoherent Measurements*, arXiv:2204.07155v2, Theorem 6.1 (Theorem III.1 in the conference numbering). Exact inspected statement: sufficiently large d and 0<alpha<=1/12; adaptive incoherent testing of I_d/d versus trace-norm distance greater than alpha needs Omega(d^(3/2)/alpha^2) copies, with any fixed success probability above 1/2. The measurement model is explicitly single-copy, with adaptive classical outcomes and no persistent quantum memory.

https://arxiv.org/html/2204.07155v2#S6
https://arxiv.org/abs/2204.07155

We use alpha=2epsilon and no parity restriction on d. All logarithms below are natural.

## 1. An exact shell realization with a positive extension

Index a d-dimensional basis by r-subsets S of [n]. Let V map |S> to the computational basis vector with ones precisely on S. Define hard-core lowering operators a_i=|0><1| on site i, a_S=product_{i in S}a_i, number operator W=sum_i |1><1|_i, and the weight-r shell projector P_r=VV*.

For any d-dimensional density matrix rho, set

rho_bar=(3/4)rho+(1/4)I_d/d, B=-log(rho_bar).

The spectrum of rho_bar is in [1/(4d),1], so 0<=B<=log(4d)I_d. Define

K_B=sum_{S,T} B_ST a_S* a_T,
E_B=lambda(W-r)^2+K_B.

K_B is Hermitian and positive semidefinite on the WHOLE qubit space, not only on the shell. Indeed, for A:v -> (a_T v)_T, K_B=A*(B tensor I)A. Also

A*A=sum_S a_S* a_S=binom(W,r),

as a diagonal operator, so ||A||^2 <= binom(n,r)=d and ||K_B|| <= d log(4d). No sign or commutation property of B is assumed.

Every a_S* a_T preserves W. On the weight-r shell, a_T|U>=delta_TU|vacuum>, hence V*K_B V=B. Consequently V*E_B V=B and Tr(P_r exp(-E_B))=Tr exp(-B)=1.

On the orthogonal complement of the shell, (W-r)^2>=I and K_B>=0. Both preserve each W eigenspace. Thus E_B>=lambda I on that complement and

Z_out=Tr((I-P_r)exp(-E_B)) <= 2^n exp(-lambda)=eta.

Let R_rho=exp(-E_B)/Tr exp(-E_B). Its shell block is exactly rho_bar/(1+Z_out) under V. Its remaining block is positive and orthogonal. Therefore

(1/2)||R_rho - V rho_bar V*||_1=Z_out/(1+Z_out)<=eta.

This is an approximation of the final finite-temperature state, with an exact conditional shell state. It does not replace the Gibbs model by a linear density.

## 2. Original locality and coefficient admission

Each a_S* a_T is supported on S union T, of size at most 2r<=k. Its sum K_B therefore has no Pauli coefficients above weight k. Hermiticity makes its coefficients real, including terms with Y. For every Pauli string P,

|2^(-n)Tr(P K_B)| <= ||K_B|| <= d log(4d).

Expand W=(n I-sum_i Z_i)/2. In (W-r)^2 the coefficient of Z_i is (2r-n)/2 and that of Z_i Z_j for i<j is 1/2. Their absolute values are at most n, since r<=n. Thus every nonidentity Pauli coefficient of E_B is bounded by n lambda+d log(4d). Set H_B=(E_B-c_B I)/beta, where c_B is the identity coefficient. Every coefficient is in [-1,1] under the displayed beta condition, all supports have weight <=k, and removing c_B I leaves the normalized Gibbs state unchanged.

The construction uses only the n physical qubits; no extra register or unknown auxiliary state is added. It permits the original unknown interaction supports and imposes no bounded-degree promise. The same supplied beta works for every rho. No claim is made that the sufficient beta threshold is optimal.

## 3. Exact null, separated alternatives

Let rho_0=I_d/d and let R_0 be its constructed Gibbs state at this same beta. If rho=rho_0 then rho_bar=rho_0, B=log(d)I_d and R_rho=R_0 exactly.

If ||rho-rho_0||_1>2epsilon, then ||rho_bar-rho_0||_1>(3/2)epsilon. By the two approximation bounds,

||R_rho-R_0||_1>(3/2)epsilon-4eta >= epsilon.

The last inequality holds because eta=epsilon^2/(100d^(3/2)), epsilon<=1/24 and d>=1. Thus each hard mixedness instance maps to a legal two-unknown Gibbs testing instance. The fact that the reduction knows the reference R_0 is allowed: any procedure promised to work for all unknown pairs must work on this subfamily.

## 4. Sample-only reduction preserves adaptive single-copy access

Given copies of unknown rho, we can produce V rho_bar V* without knowing B or rho: apply the known depolarizing channel rho -> (3/4)rho+(1/4)I_d/d, then the known isometry V. This requires at most one input copy for each requested unknown-source copy. Any one-copy POVM performed afterwards pulls back through this fixed channel to a legitimate one-copy POVM on rho; private randomness and known-state ancillas do not create quantum memory between copies.

For a request to the reference source, the simulator supplies the known state R_0 exactly (equivalently samples the specified one-copy POVM probabilities from its explicit matrix). This is a mathematical copy-complexity reduction with no computational-efficiency restriction. It requires no copies of unknown rho for that request. Reference outcomes can influence subsequent adaptive choices, but they are just classical random variables with known conditional distributions.

For any adaptive protocol of worst-case total budget T, replacing each unknown-source R_rho by its shell approximation changes its classical transcript distribution by total variation at most T eta. To prove this, condition on any common transcript before a step: the same source and POVM are selected, the one-copy output distributions differ by at most eta by trace-norm contraction, and a stepwise hybrid or maximal coupling accumulates at most eta per step. Variable stopping with a hard cap T can be padded with dummy steps. This proof does not cover merely expected-budget stopping.

If T<=L and a Gibbs protocol has error at most 1/3, the induced incoherent mixedness tester uses at most T unknown copies and has error at most 1/3+1/100, uniformly on null and alternatives. Its success probability is strictly above 1/2; constant repetition/amplification gives the convention in CHHL Theorem 6.1, changing copy counts only by a universal factor. That theorem, with alpha=2epsilon, therefore implies T=Omega(L). If T>L, that lower bound already holds. This proves the statement for adaptive single-copy P1.

## 5. Consequences and boundaries

This imports a specifically quantum measurement-class obstruction into the full Gibbs source class at explicit high beta. For k=2 it yields Omega(n^(3/2)/epsilon^2) single-copy complexity, stronger in n than the earlier classical shell closeness floor at constant epsilon. Compare maxima of bounds in their overlapping regimes rather than assert a uniform improvement for every k. For fixed k, the sufficient beta is O_k(n^2+n log(1/epsilon)+n^r log n).

The earlier classical shell closeness lower bound remains valid even for collective access; the present CHHL lower bound does not. The new reduction preserves the incoherent access restriction precisely. It does not prove a separation between optimal single-copy and collective Gibbs certification unless an applicable collective upper is also smaller in the same regime.

Known quantum mixedness testing and standard positive hard-core operator constructions supply the ingredients. No priority claim for their composition is made. Fixed-temperature optimal-copy questions and general varying-temperature upper/lower matching remain open.
