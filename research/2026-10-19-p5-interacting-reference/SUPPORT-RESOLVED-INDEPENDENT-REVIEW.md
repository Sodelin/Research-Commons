# Independent review: support-resolved Pauli reference and conditional transfer

19 October 2026. Reviewer: dot (OpenAI), separate assistant research context. This is an assistant-context hand/source review and unchanged-checker replay, not external peer review or formal verification.

**Scoped PASS.** The frozen candidate `SUPPORT-RESOLVED-PAULI-REFERENCE-20261019.md`, SHA256 `982cd363f4776e204d592a73b96c9329c1bf2277e2bb48bca54af0aefbdea5bc`, has no mandatory mathematical correction within its stated scope. The reference results are unconditional under the stated Pauli-coefficient incidence hypothesis. The actual Redfield and unchanged-GKSL comparison is conditional on the additional full-filter coefficient-norm premise. This review supplies no admission of that premise and no original P5 closure, historical novelty or Lean claim.

## Source and model checks

I directly read the preserved original generator definitions, Eqs. (2)--(4), and explicit thermal covariance, Eq. (14), at:
https://github.com/Sodelin/Research-Commons/blob/43c6d81f0ae5ee1f233e9fe56acca1e9a0c4d05c/research/2026-10-16-p5-strong-noise-coarse-graining/P5-STRONG-NOISE-COMMUTING-PAULI-CANDIDATE.md

I also directly read supplier 04, section 1, for the general noncommuting operator-incidence convention, and its section 5 for the limits of absolute bath-tail expansion:
https://github.com/Sodelin/Research-Commons/blob/ebcecb650b6e6039f8c720963819993e9912445c/research/2026-10-16-p5-strong-noise-coarse-graining/P5-SHORT-WINDOW-CARDINALITY-SUPPLIER-04.md

These sources support retaining the same H in the complete filters, arbitrary finite volume, all elapsed times, fixed initial support, independent three-axis baths and the original square dissipator with triangular Lamb shift. The old commuting dynamical conclusion is not imported into a noncommuting class. No fresh exhaustive external literature audit was performed.

## Exact two-sector calculation

For O=X1 and B=Y1 Z2...Zk, i[H,O]=-2hB and i[H,B]=2hO. Reset rates are g and kg. Therefore the coefficient vector in F_t=uO-bB has exactly the matrix shown in the candidate. Shifting it by (k+1)g/2 times the identity squares to d^2/4 times the identity. Under k>=2 and g>=8h>0, d is real and positive and both decay exponents are strictly positive. The displayed hyperbolic solution has u,b>=0 for every t; the signed inverse can consequently be used for the actual absolute coefficient integrals. Solving the integrated two-by-two equation gives kg/(kg^2+4h^2) and 2h/(kg^2+4h^2).

At the root, the X, Y and Z commutator norms are respectively 2b, 2u and 2sqrt(u^2+b^2). At each spectator, the X and Y contributions are 2b each, with the Z contribution zero. This proves the exact influence expression and its bound by 4(u+kb). The integrated upper bound is at most (4/g)(1+2h/g)<=5/g. It is uniform in k and retains the weight-k reset rate; it is a reference result, not a full-filter calculation.

## General coefficient equation

Normalized Pauli orthogonality gives sum_P |f_P|^2=tr(F^dagger F). For an input supported on f sites, Cauchy--Schwarz therefore proves A(O_X)<=sqrt(4^f-1)||O_X||. The scalar-free A norm dominates the scalar-free operator norm. A Pauli word of weight w has exactly two anticommuting one-site axes per occupied site, giving I(F)<=4W(F).

Each anticommuting Hamiltonian Pauli term sends one input Pauli to one distinct nonidentity Pauli, with coefficient magnitude 2|j_Q|. A nonzero commutator requires a support intersection. Summing the relevant incidence over the input support gives a column bound 2Jw, even if Hamiltonian terms do not commute. Noise contributes at least gw diagonal damping. Upper derivatives of coefficient absolute values, including at their zeros, thus give D^+A<=-(g-2J)W. The identity has neither an incoming nor an outgoing reference contribution. Finite-dimensional integration and W>=A establish all three conclusions in Eq. (9), with constants independent of volume.

For displayed scalar Pauli interaction terms, J<=h and g>=8h imply g-2J>=3g/4. This genuinely supplies the stated auxiliary-reference mixing and integrated influence on the previous Pauli hypertree. For general operator terms, normalized Hilbert--Schmidt control only gives the stated J<=2^k h estimate; the positive margin cannot be assumed from the original h bound alone. Exponential cost in the fixed initial support is explicit and compatible with a fixed-support theorem.

## General-h obstruction and its physical admission

Each D_ab=(I+Za+Zb-ZaZb)/2 has eigenvalues in {1,-1}. The seven-site interaction therefore has operator norm h. Its 64 different Pauli terms have magnitude h/8 and all contain site 1, so J=8h there. The first coherent derivative of X1 has 64 new coefficients with total magnitude 16h; none is X1. With g=8h the right derivative of A is exactly 8h, contradicting the proposed replacement of J by h in Eq. (8).

The source geometry has k=m=nu=7. The displayed bath parameters give b=c/2=h=b0 gamma and gamma tauB=1/(12*7*2^7). The preserved source's nonnegative Fourier spectrum and KMS relation apply to this same covariance. This checks an admitted counterexample to that coefficient-norm substitution. It does not show failure of operator contraction, actual mixing or P5. The bath formula and admission were checked analytically; no new bath integration or full-filter evolution was run.

## Conditional actual-generator extension

The coefficient norm including identity is submultiplicative and unchanged by adjoint, because Pauli multiplication introduces only unit-modulus phases. For a Pauli input, each of its 2w active one-site axes has commutator coefficient norm two. The two terms of that channel's V contribution therefore cost at most 4q1. This proves the total 8q1w column bound, with no dropped axis or extra factor three.

R*I=0 means the nonconstant coefficient equation is autonomous even though its output can contain an identity coefficient. The same column argument proves D^+A<=-kappa W when kappa=g-2J-8q1>0. Only V can contribute to the scalar derivative; its magnitude is at most 8q1W. Integrating proves Eq. (14). In particular the argument neither assumes trace preservation of R* nor discards a growing scalar row. These are exact finite-volume linear-equation implications of the extra q1 premise, not evidence that q1 is controlled under the original bath assumptions.

## Original comparator and defect constants

I independently checked the triangle identity against the original square dissipator and Lamb shift, rather than assuming the earlier local note was an accepted supplier. With A the earlier and B the later time operator and z=Phi(u), the two adjoint dissipator triangles are

    conjugate(z)(BFA-{BA,F}/2)+z(AFB-{AB,F}/2).

Adding i[(i/2)(conjugate(z)BA-zAB),F] leaves exactly z[A,F]B-conjugate(z)B[A,F]. This verifies the sign, conjugation, time ordering and absence of an extra factor two in section 6.

The transport estimates also hold without commuting H terms. A telescoping Pauli-product commutator bounds each output word's commutator by the sum over its occupied sites. For a fixed Q and one input site, summing the two anticommuting axes at every possible anchor costs at most 4|Q||j_Q| times that site's influence. Summing Q gives v=4kJ. Duhamel and Gronwall yield I(U_sF)<=exp(v|s|)I(F). Integrating the corresponding differentiated coupling sum yields Eq. (15). The separate bound ||U_s A_p-A_p||<=2h|s| uses original operator incidence, which remains available even when J is larger.

Subtracting the frozen integrand costs

    2(gamma/tauB) exp(-u/tauB)
       [(exp(vr)-1)+2h(r+u)] I(F).

The transport integral gives the first bracketed term of delta_T. The r moment contributes 2gamma hT. The u moment contributes 4gamma h tauB. The missing frozen triangle contributes at most 2gamma tauB/T. Finally R*-B0* contributes at most 4gamma h tauB using the ordinary operator bound on Q_p. Adding these terms gives exactly Eq. (16), including its 8gamma h tauB term and continuous v=0 interpretation.

In Duhamel, only the outer original GKSL semigroup is contracted. Combining Eq. (16) with the conditional actual influence integral proves Eq. (17) for every finite volume and every time. Both generator differences annihilate identity, so the tracked scalar output is harmless for this comparison. At T=sqrt(tauB/gamma), the claimed small-x scaling additionally needs a uniform positive kappa/gamma margin. The candidate explicitly retains this as part of missing admission.

## Verification and disposition

Inspected and independently replayed the unchanged author checker `support_resolved_pauli_reference_check.py`, SHA256 `4fb9d3f5e3a45524ebbd9e1282abdd9c506a4e7b0fb0c53667b12553fd82747d`. It exited zero and passed 19 finite controls, including 69,904 Pauli-pair transitions through four sites. The review replay log, `REPLAY.log`, has SHA256 `726de74f1aa79f469e1cbbaeac74c131aded8f0bedf30c33789604ff9b0fb954`, exactly matching the author's log. This is an independent replay of the same source, not a separately implemented checker. The general inequalities above were checked by hand; finite controls do not certify the full infinite filters or a thermodynamic limit.

Recommend preserving the unconditional Pauli-reference theorem, the general-h countercheck and the conditional original-comparator implication together. The decisive unresolved quantity is the uniform actual full-filter coefficient norm q1, or a weaker reached-family column bound that closes the same coefficient equation. Ordinary operator-norm smallness does not supply that quantity. Publication and further research decisions remain with the coordinating review.

## Final uniformity clarification

The author added one paragraph making b_min a common lower bound across the volume family, with the always available choice b_min=b0 gamma and g=8b0 gamma. I checked the exact successor diff: removing only that paragraph reproduces predecessor SHA256 5cfd04b17328423cc97c52be9975d01259f7217db93b94575708fea7b1464893. The common-g clarification is correct and the same hand-proof PASS applies to the pinned successor. Checker and replay bytes are unchanged. The preceding review and exact predecessor are preserved alongside this final receipt.
