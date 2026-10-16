# Independent review: quantum shell single-copy import 17

Date: 2026-10-16. Independent source and mathematical hand review by OpenAI assistant for Nolan. **Verdict: scoped PASS.** No independent numerical, compiler or Lean execution is claimed. No novelty or full P1 closure is accepted by this review.

## Exact reviewed artifact and primary supplier

Reviewed `QUANTUM-SHELL-SINGLE-COPY-IMPORT-17.md`, SHA256 `ec5162ebf03546f4f8f63a474759870f64ad1451fdb30d1bfe2470f6070bef54`, in full.

The reviewer directly inspected Chen–Huang–Li–Liu, *Tight Bounds for Quantum State Certification with Incoherent Measurements*, arXiv:2204.07155v2, [Theorem 6.1](https://arxiv.org/html/2204.07155v2#S6) and Section 2's measurement definition. The source supplies the lower bound Ω(d^(3/2)/alpha²) for sufficiently large d, 0<alpha<=1/12, and adaptive measurements of individual copies retaining classical outcomes. Its fixed success constant may be changed to any constant greater than one half. The candidate uses alpha=2epsilon and epsilon<=1/24, so this supplier's stated domain is respected. The testing hardness is attributed to that primary source.

## Algebra and original-class admission

1. **Positive extension and index orientation.** With A mapping v to the indexed column `(a_T v)_T`, the (S,T) block of B tensor I yields exactly `sum_ST B_ST a_S* a_T`. Consequently K_B is positive semidefinite for every positive B, including complex Hermitian B. No transpose or entrywise conjugation is missing. The identity A*A=binom(W,r) implies the claimed norm bound d log(4d).
2. **Exact shell.** For two r-subsets T,U, a_T|U> is zero unless T=U; in the equal case it is the vacuum. Applying a_S* then gives |S>. Thus the shell matrix is B itself. Each term preserves particle number even when S and T overlap.
3. **Leakage.** The penalty vanishes on the shell and is at least lambda on its orthogonal complement. K_B is positive on that whole complement, not just on the shell. Number conservation removes cross-shell blocks. The shell partition weight is exactly one, and its normalized conditional state is rho_bar. This proves the stated half-trace error at most eta without assuming commutation of B with a basis matrix.
4. **Locality and coefficients.** Every term has support contained in S union T, of size at most 2r<=k. Hermiticity gives real Pauli coefficients. Their magnitude is bounded by ||K_B||. The displayed single-Z and pair-Z penalty coefficients are correct. Since k>=2, the penalty is admitted. The common beta bound dominates every nonidentity coefficient of E_B; removing its scalar coefficient preserves the Gibbs state. No bounded-degree promise is used or claimed.

## Testing and access-class reduction

The exact null is R_0, even though the sample-only simulator uses its shell approximation for unknown-source calls. On alternatives, smoothing multiplies the original full trace norm by 3/4. The two half-trace leakage errors cost at most 4eta in full trace norm, leaving more than epsilon separation. The explicit eta satisfies the final inequality throughout the stated domain.

For each unknown-source call, the known depolarizing channel followed by V consumes at most one copy of rho. Pullback of any one-copy POVM through this channel is a valid one-copy POVM on rho. There is no need to know B or evaluate unknown matrix entries. Known-reference outcomes can instead be sampled from their explicit conditional distributions, including when subsequent source choices depend on them. This preserves classical adaptation and does not introduce persistent quantum memory.

At a common transcript, the replacement changes the next unknown-source outcome distribution by at most eta; reference calls add zero error. Coupling/hybrid accumulation therefore gives total variation at most T eta under the hard total-copy cap. Padding handles early stopping. For T<=L, the resulting success remains a fixed constant above one half; CHHL and constant amplification imply T=Ω(L). If T>L the claimed lower bound already follows. The argument does not silently substitute an expected-copy budget.

## Accepted consequence and limits

The stated lower bound Ω(binom(n,floor(k/2))^(3/2)/epsilon²) is justified for the original bounded-Pauli-coefficient Gibbs class at the explicit sufficient high-beta threshold. The even-k exponent, odd-k floor, k=2 consequence and fixed-k beta growth are consistent with the formulas.

This acceptance is restricted to adaptive single-copy measurements with classical memory. It is not a collective lower bound, an improvement at fixed beta, an efficient physical preparation result, or a demonstrated separation from an applicable collective upper. The temperature threshold is sufficient and not optimized. Novelty of the encoding/import remains unestablished. No mandatory mathematical correction was found.
