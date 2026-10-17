# Directed prior-work review: conductance and reflection determinant

2026-10-17 UTC. dot (OpenAI), working with Nolan. Local literature checkpoint for coordinator review; no novelty certification. Sources accessed 2026-10-17. This review concerns zero-energy canonical PHS reflection, exactly two electron modes (4×4 r), contractivity, and zero-temperature/zero-bias charge conductance g=2−||r_ee||F²+||r_he||F². Finite transmission is allowed; finite-temperature readout is not automatically covered.

## Result

The inspected primary literature contains exact stronger conclusions for **unitary reflection**, and an exact one-electron-mode predecessor. I did not locate the proposed arbitrary-contractive two-electron-mode bound det r≥|g−2|−1, or the earlier quartic bound, in this bounded search. This is not evidence establishing novelty. The proposed linear bound remains subject to the separate mathematical review; I have not reviewed its complete proof. Candidate05's weaker Schur-complement proof was hand-checked and I found no algebraic defect.

## Closest exact prior

1. Beenakker et al., *Random-matrix theory of Andreev reflection from a topological superconductor*, arXiv:1012.0932, Sec. IV A (PDF p5). https://arxiv.org/pdf/1012.0932 . For N=2 and Q=−1, G/(e²/h)=2 without fluctuations. With unitary reflection, Béri degeneracy and parity fix the two Andreev probabilities at 0 and 1. Thus det r=−1 forces g=2, stronger than 1≤g≤3 but only in the unitary subcase. Their long-wire numerical comparison suppresses transmission; it does not establish the claimed arbitrary-contraction extension. The linear candidate, if proved, recovers this unitary negative-sign limit exactly.

2. Diez, Dahlhaus, Wimmer, Beenakker, *Andreev reflection from a topological superconductor with chiral symmetry*, PRB86,094501 (2012), Sec. II, Eqs.9–10. https://arxiv.org/pdf/1206.3079 . Their reflection matrix is unitary after neglecting transmission. Bounds G/G0≥|Q| and G/G0≤min(N,N+(−1)^(N−|Q|)), with G0=2e²/h, are stated also to apply to class D Q=0,1 through Béri degeneracy. For N=2 nontrivial parity they again fix g=2. Do not confuse their conductance unit or integer/parity Q with the finite nonunitary determinant.

3. Marciani, Schomerus, Beenakker, *Effect of a tunnel barrier on the scattering from a Majorana bound state in an Andreev billiard*, Physica E77 (2016),54–64, Secs.VIII–IX, Eqs.48–60. Author manuscript: https://eprints.lancs.ac.uk/id/eprint/76997/2/tunnel_billiard.pdf . Eq.48 uses a nonunitary **2×2 real Majorana reflection block**, corresponding to one electron mode; Eqs.49–52 give gA=1−cosθ. In that parametrization det r=cosθ, so det r=1−gA (an immediate algebraic consequence, not an independently new identity). Their N1=2 counts electron and hole separately. This must not be mistaken for the current 4×4 problem. Later results concern ensemble distributions/averages, and distinguish full det S from subblock det r.

## Dissipative and finite-system comparisons

4. Das Sarma, Nag, Sau, *How to infer non-Abelian statistics and topological visibility from tunneling conductance properties of realistic Majorana nanowires*, PRB94,035143 (2016). https://link.aps.org/accepted/10.1103/PhysRevB.94.035143 . Sec.IV B/Fig.5 (PDF p9) compares TV and ZBCP while varying splitting/broadening/coupling parameters, finding a decreasing relation in those calculations. Sec.V discussion (PDF p13) uses an approximate half-ideal-peak criterion. Appendix A supplies scattering/conductance definitions and unitary identities. No universal two-mode linear determinant inequality was identified in these passages. These model-specific correlations neither establish the new inequality nor imply a universal negative-label inference from an intermediate peak.

5. Araya Day, Manesco, Wimmer, Akhmerov, *Identifying biases of the Majorana scattering invariant*, arXiv:2504.01069, Secs.2–3, Eqs.7,9,11. https://arxiv.org/pdf/2504.01069 . Explicit low-energy models show effects of finite length, tunnel coupling, quasi-Majoranas and quasiparticle sinks on reflection sign. Sec.3.3 explains why dissipative sinks can spoil equality of left/right determinants and yield misleading topological interpretation. No general conductance–determinant inequality was located. This reinforces the required limitation: a finite reflection-sign certificate is not itself a certificate of protected Majorana modes or thermodynamic topology.

## Search limits and disposition

Directed searches combined topological visibility, conductance, inequality/lower bound, det r, nonunitary reflection, and 1−G; primary texts above were inspected rather than relying on search snippets. This was not exhaustive citation traversal or a specialist review. The mode-resolved permutation-dominance rule is a classical strict-diagonal-dominance nonsingularity/homotopy application; novelty should not be assigned to the underlying matrix principle. Its physical measurement admission is a separate obligation.

Recommend retaining the linear result as an attributed candidate pending full proof review, explicitly citing the unitary and one-mode predecessors. Do not describe it as a new topological diagnostic, an experimentally validated protocol, or a resolved literature novelty claim.
