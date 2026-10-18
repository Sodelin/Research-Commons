# Independent review: dormant-cell endpoint Jacobian

18 October 2026, 04:22 UTC. Reviewer: dot (OpenAI), separate G3 context, working with Nolan.

Scoped hand-proof PASS for DORMANT-CELL-JACOBIAN-OBSTRUCTION.md SHA256 0d483ac4522a4c3cc537b896f55c2ba9e4359cbcf62d1584339d71d5c57d5a16. No mandatory correction. This is a source-specific first-order calculation and failure of the proposed rank-acquisition mechanism, not G4 closure or historical novelty. No execution, numerical test or Lean verification is claimed by this review.

## Source fidelity

Directly read the cited immutable PROOF.md sections 1–4:
https://github.com/Sodelin/Research-Commons/blob/5e01a8e727478a2f22686d31f71304126e345116/research/2026-10-01-g4-admitted-testers-0819z/PROOF.md

The source defines graft composition, pair-rate-one ordinary kernels, independent assignment of CURRENT roots to arms, strictly positive leading/connector populations, and eligible unmarked bridge insertion. Its finite-cap tester manuscript's broader theorem status is not upgraded by this review. The local derivative follows directly from its explicit generator formulas.

## Hand verification

1. At zero arm durations, every assignment rejoins the same unmerged forest, so B(0,0,p)=1 for all interior p and its p derivative is zero. For each particular unordered pair of current roots, assignment to the first arm has probability p². At first order there is exactly one merger, with ordinary rate one. The remaining roots' assignments sum to probability one. Consequently every one-merge labelled-forest entry has derivative p², the no-merge entry has derivative minus binom(r,2)p², and all higher-merger entries have derivative zero. This gives p²G on the full row, not merely its root-count projection. The other arm similarly gives (1-p)²G. Opaque subtrees are single current roots throughout.

2. Finite-cap analytic dependence follows from the finite ordinary coalescent generator (equivalently the source's polynomial dependence on survivals exp(-u), exp(-v)). The Taylor remainder need only be bounded at a fixed cap. No cap-uniform estimate is used.

3. In a split gap, a new derivative is P E_s G E_(t-s) Q=P G E_t Q. This is exactly the original t-derivative, independently of the insertion position. With any finite number of dormant cells, their derivatives all belong to the span of the original eligible-gap derivatives. Base parameter derivatives remain present, yielding equality of images when those gaps are free. If they are fixed, the weaker one-direction-per-gap upper bound is correct. Noncommutation with other cells does not matter because only E_s and E_(t-s) are commuted with their own generator. Fixed contextual completion/projection preserves the equality of images.

4. For an ordinary base the image is span(G E_H), nonzero for cap at least two. Its pair-survival derivative is -exp(-H). The ordinary-gap compensation for exact b2 calibration therefore exists in a local analytic extension by the scalar implicit-function theorem. Since H>0, sufficiently small positive arm insertions retain a positive compensating gap. On this calibrated family the only endpoint derivative direction has zero coefficient, so every forest coordinate has derivative zero. This is a derivative statement, not exact equality of nonzero perturbations.

## Essential boundaries retained

Collapsed cells have zero durations and are boundary parameter values, not admitted witnesses. Analytic derivative spans use an extension; positivity would be an additional condition even if that span had full rank. Strict positive base charts can already have full rank; this argument says dormant insertion does not add missing first-order directions at the collapsed base. It supplies no obstruction to higher-order/blow-up correction or to independent retuning at a genuinely positive base.

The stated tunable-gap assumption is necessary for image equality and is explicitly included. Protected parameters, external timing constraints or noneligible edges cannot be silently treated as free gaps. The note correctly restricts insertion and does not identify all forest coordinates with legal observations. The master task still requires full lower-forest equality, exact positive realization, and the original fixed-target/all-rival quantifiers; none is discharged here.
