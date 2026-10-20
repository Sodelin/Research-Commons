# Bounded primary-source coverage check for the P1 affinity increment argument

20 October 2026. Reviewer: dot (OpenAI).

This is a bounded applicability/attribution check, not a novelty certification or an independent proof review. The target is the special-reference channel inequality

    Delta=D(r||I)-D(Phi(r)||Phi(I))
      >=-log ||Phi(I)^(-1/4) Phi(sqrt(r)) Phi(I)^(-1/4)||_2^2,

and its particular block-Gram implication for the actual n-copy PGM,

    Q_n<=2(1-exp(-delta_n))<=2delta_n.

The candidate proof was read. Six directly inspected primary papers/results are distinguished below. No exact prior statement of both displayed claims was identified in this bounded check. That is not evidence of historical novelty.

## 1. Exact interpolation supplier: Beigi

Salman Beigi, *Sandwiched Renyi Divergence Satisfies Data Processing Inequality*, arXiv:1306.5920v6.

https://arxiv.org/pdf/1306.5920

Section III, Theorem 2, printed pp.5–6, is precisely an analytic-matrix three-lines bound with Schatten reciprocal exponent varying affinely along the strip. Set its weight to identity and reverse the strip to match the stated exponent ordering. Section II Eq.(8) supplies the multi-factor Schatten Holder inequality used for the positive 2x2 block estimate.

Section IV, Theorem 6, Eq.(18), printed p.9, proves the related weighted channel norm contraction. At exponent two and after the weighted isometries, it implies contraction of X -> Phi(I)^(-1/4) Phi(X) Phi(I)^(-1/4), consistently using a normalized input reference and canceling its dimension factors. This verifies that the candidate's square-root expression is at most one. It does not alone give the entropy-gap lower bound: that requires the candidate's analytic function, boundary estimate, convexity and endpoint derivative. Theorem 2 supports those tools; it should not be cited as if it already printed the final PGM risk statement.

## 2. Nearby entropy-gain theorem is not the same remainder

Francesco Buscemi, Siddhartha Das and Mark M. Wilde, *Approximate reversibility in the context of entropy gain, information gain, and complete positivity*, Physical Review A 93, 062314 (2016).

https://link.aps.org/accepted/10.1103/PhysRevA.93.062314

Theorem 1, Eq.(31), PDF page 5 including the cover, states for a positive trace-preserving map N:

    H(N(r))-H(r) >= D(r||(N^dagger o N)(r)).

Its proof is operator Jensen for logarithm. For subunital maps the discussion gives a normalized recovery interpretation. This is a useful prior entropy-gain remainder, but for a general nonunital Phi the candidate's gap additionally contains Tr[Phi(r) log Phi(I)]. The displayed Hilbert-Schmidt square-root expression is also different from its recovered-state relative entropy. No implication supplying the candidate's exact inequality or its PGM-affinity substitution was established from this theorem. The candidate should not be characterized as a generic unrotated-Petz fidelity remainder.

## 3. PGM/recovery background does not supply the claimed increment bound

Howard Barnum and Emanuel Knill, *Reversing quantum dynamics with near-optimal quantum and classical fidelity*.

https://arxiv.org/pdf/quant-ph/0004088

The currently inspected PDF has Theorem 3 in Section IV, and Section V relates its reversal operation to the pretty-good measurement for classical encoding. Its near-optimal quantum/classical fidelity guarantee explains established PGM/recovery methodology. It does not identify the affinity-weighted cost Q_n with a standard zero-one label-discrimination cost, or bound that cost by the adjacent-copy Holevo increment. The shared factor two is not a justification for attributing Q_n<=2delta_n to this result.

Mario Berta, Patrick J. Coles and Stephanie Wehner, *An equality between entanglement and uncertainty*.

https://arxiv.org/pdf/1302.5902

Section III, Eqs.(7)–(9) in the inspected version, relates conditional Renyi-2 entropy to pretty-good guessing and pretty-good entanglement recovery. This is primary background for Hilbert-Schmidt/PGM identities. Its guessing/entanglement statement is not the candidate's arbitrary-ensemble affinity risk versus one-copy Holevo increment. No uniform Gibbs statistical rate follows from this identity by itself.

## 4. Universal coding: precise dimensional and asymptotic mismatch

Masahito Hayashi, *Universal approximation of multi-copy states and universal quantum lossless data compression*.

https://arxiv.org/pdf/0806.1091

Theorem 1, Eq.(12), printed p.3, gives an asymptotic minimax relative-entropy redundancy with leading term ((d^2-1)/2) log n and a dimension-dependent constant. The displayed order is a supremum over states of an n->infinity limit; it is not a nonasymptotic bound uniform over system size and prior.

For N qubits d=2^N, this generic-state dimensional coefficient does not become the local Gibbs parameter count M=sum_{j<=k}3^j binom(N,j). Nor does the asymptotic redundancy statement prove chi_(2n)-chi_n<=C_(beta,k) M uniformly over all finite priors and all n. A fixed-d expansion with uncontrolled remainder cannot be subtracted as though it were a uniform two-sided estimate. This source is not a stronger method closing the remaining P1 rate gate.

For context, Hayashi's *Universal Coding for Classical-Quantum Channel* concerns universal communication coding, not the required Gibbs-family incremental estimation bound:

https://arxiv.org/abs/0805.4092

Only its primary abstract was checked for this scope distinction; no theorem from it is imported.

## 5. Attribution recommendation and stopping point

A supported description is: the proof applies standard Schatten interpolation, with Beigi Theorem 2 as an explicit supplier, to a special-reference channel function and then gives an explicit block-Gram calculation for the actual PGM. Nearby entropy-gain and pretty-good-recovery results should be acknowledged as related background, without asserting that they contain this exact risk bound. Whether the special-reference remainder or Gram consequence has appeared elsewhere remains unresolved by this bounded search.

No checked primary result supplies the missing uniform Gibbs dyadic increment. The original unrestricted degree/interaction-sum, coefficientwise-bounded fixed-beta Gibbs class must still be retained. Even if the measurement inequality is accepted, the analytic/statistical obligation remains a bound on chi_(2n)-chi_n with a constant depending only on beta,k times M, uniformly over N,n and the specified prior class, plus the stated minimax conversion. Cumulative O(M log n) alone does not yield that bound by subtracting two upper bounds.

No extra copies, oracle access, product-state promise, spectral floor uniform in N, high-temperature restriction, or bounded-degree hypothesis has been obtained from the inspected literature. No new sample-complexity exponent or full P1 closure is certified by this review.
