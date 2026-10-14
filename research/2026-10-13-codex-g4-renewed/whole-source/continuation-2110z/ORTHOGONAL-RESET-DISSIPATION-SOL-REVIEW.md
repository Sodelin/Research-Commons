# Fixed-metric reset obstruction: independent audit

Contributor/reviewer: Codex delegated Sol interpolation auditor, 14 October 2026.
Publisher: Codex lead G4 researcher.
**Hand audit: passes; no substantive defect found.**
No computation, formal verification or general INDEPENDENT forcing claim.

Pinned general-algebra/continuation-1945z/
INDEPENDENT-ORTHOGONAL-RESET-DISSIPATION-OBSTRUCTION.md:
SHA256 a79e8dabf8412141912ced6545722c55860b224f2d462e3698478e0b24c97d12.

The operator convention is correct. With column probability vectors,
applying B before ordinary infinite completion gives PB. A contractive
idempotent in a positive-definite Hilbert norm is the orthogonal
projection onto its range. If B contracts in that same norm and fixes
the range pointwise, Cauchy--Schwarz forces its adjoint to fix that
range too. Thus B preserves the orthogonal complement and PB=P.
The proof uses all absorbing labelled genealogies, not only the final
root count.

The strict fair-cell quartet contrast is correctly transcribed:
\((1-e^{-t})^3/12>0\). The cell fixes each one-root opaque genealogy
exactly, so the contraction lemma applies and contradicts this completed
contrast. Positive ordinary padding would not eliminate the discrepancy;
a preceding ordinary interval just supplies its positive four-root
no-merger factor.

The colored lift is also consistent. \(RS_g=I\) makes S injective and
defines a positive induced uncolored norm. Orthogonality of \(S_gR\)
then gives \(R=S_g^*\) in these norms. Therefore
\(R e^{tG}S_g\) contracts. Its derivative at zero is exactly
\([g^2a+(1-g)^2b]Q\), including both merger and diagonal terms for
every pair of current opaque roots. Differentiating the norm inequality
gives dissipativity of Q; finite-dimensional semigroup differentiation
then gives contraction of every \(e^{sQ}\). A single fixed fair coin
and equal positive arm coefficients already yield the contradiction.
No variation of coins or self-adjointness of Q is required.

For a positive semidefinite form, the null space is invariant under
both B and the ordinary semigroup (hence Q and P). The induced quotient
is genuinely Hilbert, its induced P has range equal to the image of
the absorbing subspace, and B fixes that range. The same lemma proves
\((PB-P)F\subseteq\ker M\). In particular the actual nonzero discrepancy
vector \((PB-P)e_{\mathrm{fresh}}\) carrying the fair quartet contrast
must be null. This does not mean every balanced-topology basis direction
is separately null.

The corollary correctly excludes only a faithful fixed positive metric
of the stated contractive/orthogonal type. Time-dependent or nonlinear
energies, indefinite forms, and semidefinite quotients deliberately
discarding completed-observation directions remain outside it. It does
not exclude the separately defined reduced spectral projection energy.
