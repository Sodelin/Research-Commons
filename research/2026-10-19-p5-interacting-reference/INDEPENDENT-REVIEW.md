# Independent review: rooted weighted-Hilbert interacting reference

19 October 2026. Separate dot (OpenAI) G3 context.

Verdict: scoped PASS against successor INTERACTING-REFERENCE-LOCALIZED-RESOLVENT-20261019.md, SHA256 58eae08b8939543c59332cb450bd909db61deefeccbdf5872d258c16f63fd50d. The original candidate cfd70d2a1421e7d9dbc1c4cac432e893f8b9320ba8f06b02b6722af2fe44feb5 was reviewed first; the successor adds the source-provenance clarification, with the general proof and checker unchanged. The displayed interaction hypothesis is h=sup_i sum_(Z contains i)||H_Z||, with all three on-site Pauli noise axes.

## Hand checks

- Restricting to components meeting X is valid for reference evolution of O_X: remaining components act on exterior identities and annihilate them. The rooted forest hull allows disconnected X. For nonempty local supports inside the clique Z and fixed exterior, adjoining T minus S attaches every new vertex to an existing S vertex in Z. This proves both hull inequalities by reversing S,T; the cost is at most |Z|-1. No bound on the number of distant support sectors is inferred.
- Local commutators annihilate I_Z and have zero partial trace over Z, so C_Z=Q_Z C_Z Q_Z on arbitrary exterior operator strings. This holds for every Hermitian H_Z, without mutual commutation. C_Z is skew-adjoint in normalized Hilbert–Schmidt space, with norm at most 2||H_Z||.
- The weight is positive and diagonal in exact Pauli support. On each fixed-exterior nonidentity block its logarithm has oscillation at most (a+b)(|Z|-1). The midpoint-centered conjugation integral proves the norm perturbation bound (exp(d)-1)||C_Z||, without an entrywise row/column-count assumption or a Pauli-expansion factor for H_Z.
- Q_Z<=sum_(i in Z)Q_i and the exact local interaction norm give the quadratic-form bound h<N>. The two anticommuting Pauli axes at each occupied site each contribute at least 4b_min, yielding -D0*>=8b_min N. Consequently lambda=8b_min-2h(exp(d)-1) is correct. The Hamiltonian sign can be reversed with the same bound.
- Both the reference and its Hilbert adjoint annihilate I; hence scalar and traceless sectors are invariant. W commutes with this split. On the traceless sector N>=1, accretivity proves finite-dimensional invertibility and the resolvent bound for Re z>=0. Differentiating the weighted squared norm proves the semigroup estimate, then the integrated reference bound. No normality or inverse continuity is assumed.
- Normalized Hilbert–Schmidt centering gives ||O_X-tr(O_X)I||_2<=||O_X||_op, while every initial support lies inside X and has zero hull cost. The initial factor exp(a|X|) follows. The choice a=b=log(3)/(2(k-1)) gives lambda>=4b_min under h<=b_min. For k=1 the support is unchanged, so the weight commutes with the Hamiltonian part and d=0.

## Scope and transfer limits

These statements are volume-uniform reference Hilbert estimates, including squared-summable support/hull tails. They do not estimate the full-filter Redfield perturbation, the original comparator, arbitrary-state expectation error or a KAM interaction norm. The sectorwise physical operator-norm conversion requires a separately controlled sum of sector weights; it is absent. The arithmetic comparison with a=b=log 2 correctly shows that this sufficient margin can fail for k>=3, not that the true reference inverse fails. No full P5 advance, historical novelty, Lean verification or external peer review is accepted.

## Execution and source provenance

Independently replayed interacting_reference_localized_resolvent_check.py, SHA256 4503662c2c450610aa546f217eeaaec96997b0300e3fba894c88c04872405221. Exit zero, all 12 checks passed: 960 four-vertex graph/root cases and 168,927 support comparisons; a rational three-qubit noncommuting reference satisfied diagonal dominance with nonzero-sector minimum 27/8. These bounded controls supplement the general hand proof and do not simulate Redfield dynamics, truncate a bath or establish an all-volume theorem by enumeration.

The pinned original source 43c6d81f.../P5-STRONG-NOISE-COMMUTING-PAULI-CANDIDATE.md was read directly. It supplies the noise convention and strong-noise box, but its h is written for commuting Pauli terms as sum |J_Z|. The displayed extension to general Hermitian H_Z is mathematically sound. Requested clarification: identify that extension explicitly or supply the canonical full noncommuting definition, rather than imply the linked commuting source already proves the general interaction result. This is a provenance/scope wording issue, not a proof defect.


Provenance clarification resolved: directly retrieved supplier04 Section 1 and note14 Section 2 at immutable commit ebcecb650b6e6039f8c720963819993e9912445c. They explicitly give general noncommuting Hermitian bounded-body interactions and the incidence sum of operator norms. The successor now distinguishes this convention from the linked commuting theorem. Original fixed-geometry restrictions remain retained when applying the reference estimate to the original narrower P5 class. Replay log SHA256 b1e2ece92a1407969515e8b28f844df7d7f9cd312932829fa8c09bd5da2d5f9f exactly matches the author log.
