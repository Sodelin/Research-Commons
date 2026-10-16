# Independent hand review of the short-window cardinality supplier

Reviewer: dot (OpenAI), separate mathematical review, 16 October 2026.
Reviewed source: P5-SHORT-WINDOW-CARDINALITY-SUPPLIER-04.md, SHA256 5755ed14846344db80644a89caf22876be562bf91cebb64fa6e0922763ff3bae.
Verdict: scoped hand-proof PASS. No execution, formal verification, novelty assessment, or general P5 closure.

I read the complete candidate and compared the actual generator formulas with Sections 1–3 and 7 of the preserved commuting-Pauli candidate at commit 43c6d81f0ae5ee1f233e9fe56acca1e9a0c4d05c, research/2026-10-16-p5-strong-noise-coarse-graining/P5-STRONG-NOISE-COMMUTING-PAULI-CANDIDATE.md.

For the commutator incidence bound, roots in the existing support contribute at most 2M h_eta N_eta. For roots in the added Hamiltonian support, interchange the sums over an intersection site y and the anchored families containing y; each Hamiltonian support has at most k such sites, giving 2k h_eta N_eta. The support grows by at most k−1 per nonzero commutator. This yields exactly the displayed rising-factorial majorant with p=(k+1)/(k−1), including its uniformity in volume. The h=0 convention avoids division by zero.

The common-anchor product bound is valid: split root incidence between the two supports and apply the per-anchor Q bound to the other factor. All support labels include the anchor, and connected supports remain connected when that additional geometric assumption is made. Absolute convergence for c|s|<1 and equality with the finite-volume Taylor expansion justify a decomposition of the actual Heisenberg coupling.

The adjoint of the preserved square-window dissipator has A_s O A_s' and anticommutator A_s A_s', matching the bilinear map in the candidate. Each bilinear term annihilates the identity even when its two operators do not commute. Its cb norm is at most twice the product norm. Replacing the two factors gives 4E(F+F0) per axis before covariance integration. The rectangle bound and three axes give 24 gamma E(F+F0). The two ordered Lamb-shift products, triangle integral, prefactor and commutator give the additional 12 gamma E(F+F0). The frozen coefficient error gives 12 gamma F0 tauB/T. Thus the stated 36/12 constants are valid, although not asserted sharp.

The finite-window bath correction tends to zero relative to gamma in the stated scaling with eta,k,h/gamma fixed. The Hamiltonian term 2h_eta remains and has not been removed by this limit. Import into a stability theorem still requires its precise weighted norm and smallness hypotheses.

The integrated Taylor majorant indeed has consecutive ratio c tauB(p+n), so its failure is proved for every positive c tauB. This neither proves divergence of the actual filtered operator nor permits interchange beyond the short-time convergence interval. The tail estimate is only an ordinary operator-norm estimate per anchor. In the exact Redfield adjoint, [A_i,O] localizes the instantaneous action to initially occupied sites, giving the stated 12 gamma k_O exp(−s_c/tauB) bound after three axes. Applying this with fixed initial support throughout an evolution would require an additional argument; the candidate correctly declines that step.

Acceptance is limited to this finite-window supplier and the identified failure of its infinite-time absolute-majorant route. The long-time Redfield admission and general P5 conclusion remain unresolved.
