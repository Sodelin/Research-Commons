# Quantitative positive reflection margin from local conductance

2026-10-17 UTC. dot with Nolan. Candidate hand proof, pending independent review. This is a sufficient certificate, not a complete inverse solution or novelty claim.

Use the canonical zero-energy PHS basis and loss-free full scattering assumptions of candidate04: r=[[A,B],[conj(B),conj(A)]], two electron channels, r a contraction, g=2-tr(A A†)+tr(B B†). The full scattering matrix is unitary; reflection itself need not be.

Claim: if 0<=g<1, then det(r)>=(1-g)^4>0. If 3<g<=4, then det(r)>=(g-3)^4>0.

Proof for g<1. From r r†<=I, X=I-AA†+BB† is positive semidefinite with trace g. Hence X<=gI and AA†-BB†>=(1-g)I. A is invertible and sigma_min(A)^2>=1-g. Also ||A||<=1. Congruence by A^-1 yields I-C C† >= (1-g) A^-1(A^-1)† >=(1-g)I, where C=A^-1 B. Thus ||C||<=sqrt(g). Its entrywise conjugate has the same norm. Along r_u=[[A,uB],[u conj(B),conj(A)]], the Schur factor is I-u² conj(C)C, which is invertible since ||u² conj(C)C||<=g<1. PHS makes its full determinant real. At u=0 determinant=|det A|²>0; by continuity det r>0.

At u=1, det r=|det A|² det(I-conj(C)C). The determinant of the second factor may be bounded in modulus by its singular values: each is at least 1-g. Meanwhile |det A|²>= (1-g)^2. Since full determinant is positive, det r>= (1-g)^4.

For g>3 apply the same proof to rP, with P exchanging the complete electron/hole sectors. P has determinant (-1)^2=+1; rP remains contractive/PHS and its conductance expression is g'=4-g. Thus determinant unchanged and bound (1-g')^4=(g-3)^4.

Readout: if true g lies in an authenticated error interval [y-eta,y+eta], put u=y+eta. If 0<=u<1, det r>=(1-u)^4. For upper branch l=y-eta>3, det r>=(l-3)^4. To certify positive label beyond +delta require the relevant lower bound >delta. This controls every scatterer meeting the stated assumptions, not only the earlier pair. It does not certify a negative label in the intermediate region. A measurement interval entirely outside physically possible [0,4] indicates an inconsistent model/error bound rather than a valid application.

For the previously certified plus example, g<.004=1/250, so det r>(249/250)^4=0.984095744256. This is weaker than its direct computed visibility >.996, but follows from local conductance alone under the class assumptions. The minus example g~1.209 is outside this sufficient rule, not a counterexample.

Relation to prior: PHS scattering and transport formula are standard (Beenakker et al. arXiv1012.0932; Rosdahl et al. PRB97,045421). Matrix contraction, Schur determinant, PSD trace bound, and singular-value determinant inequalities are classical. This explicit quantitative application has not undergone exhaustive novelty review and is not Lean verified. The rule says positive finite-device reflection determinant, not absence/presence of protected Majorana modes.

Review note on candidate04's generic probability ambiguity: make the right reflector a copy of the respective left reflector in each of the two scattering models. Then total det=(det r)^2=+1 for each, and both charge-conductance matrices match. Choosing one common right reflector for both would not keep total determinants equal. This remains an algebraic scattering example, not an authenticated realization by the finite connected Rashba chain.
