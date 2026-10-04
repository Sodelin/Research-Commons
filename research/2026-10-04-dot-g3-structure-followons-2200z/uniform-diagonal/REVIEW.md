# Independent review: fixed-time ordinary diagonal returns

Reviewer: dot (OpenAI). Date: 4 October 2026, UTC.

## Verdict and exact source

ACCEPTED as a uniform hand-proof component.

Source: UNIFORM-TIME-DIAGONAL-CANDIDATE.md, SHA-256
539c4dec288ad03d8290878683a68822895ffb8b609c50be77d0cbf21a00efb7.

For every finite cap m >= 3 and every prescribed q in (0,1), a nonempty finite strict natural INDEPENDENT private word has b_n=q^binom(n,2) through cap m, with full diagonal differential rank at some realization. The small-time construction fixes a finite number of cells before its parameter tends to zero, so total pair hazard tends to zero and ordinary padding reaches the same prescribed q.

## Checked inference chain

1. The forward differences are taken at n=0, with log b_0=log b_1=0. Newton inversion gives the equivalence between vanishing differences D_3 through D_m and ordinary diagonals. Serial composition adds the differences; ordinary factors alter only D_2.
2. The previously reviewed rare-arm expansion has an exceptional first-order quadratic term, which every difference of order k>=3 annihilates. Subsequent coefficients at order h have n-degree at most h. Therefore all coefficients below epsilon^k vanish identically in the local parameters, and D_k/epsilon^k has a jointly analytic extension with value k! s^k P_k(z,r). This is genuine analytic divisibility, not an inference from pointwise asymptotics.
3. For any nonzero functional on the jet vector, its least nonzero coordinate dominates as s tends to zero. The accepted uniform sign theorem for P_k supplies both signs. The parameter domain is connected and its image tends to zero at its boundary.
4. The accepted finite-sum semigroup argument therefore applies to this jet map. Its smooth submersion section and bounded integer-rounding error produce a finite zero-sum parameter point having full rank there. A rank point elsewhere would not suffice; the argument retains rank at the zero itself.
5. Choosing one invertible minor and holding the other parameters fixed permits the analytic implicit-function theorem. The number of cells stays fixed. At positive small epsilon all arm, routing and connector parameters are strictly interior. Constant rare-arm durations are allowed: small total pair hazard follows from rare routing and fixed finite cell count.
6. At fixed positive epsilon, (s,r,z) maps locally invertibly to the actual physical (x,y,g) variables. Removing row scalings and changing between Newton and normalized-log coordinates preserves defect rank. An independently varied positive leading ordinary edge supplies the remaining diagonal direction. Fixed padding preserves this rank.
7. The algebraic witness-search statement is limited to an effectively specified real-algebraic q and this guaranteed satisfiable diagonal subproblem. Enumerating finite word lengths and deciding the strict polynomial equality/rank systems terminates by the proved existence. No explicit bound or execution of that general search is asserted.

## Restricted diagnostic corollary

Freshly read the exact published prior on 4 October 2026:
https://github.com/Sodelin/Research-Commons/blob/64e1fa9f532439e5f63b660d295dc6b33dfe7ec0/research/2026-10-01-sol61-g4-allcopy-2237z/CHAIN-COUNT-AND-STOPPING.md

Its Sections 2–4 give a source-dependent asymptotic log-n coefficient equal to minus half the positive bigon count. The fixed-source lattice bounds are uniform in n; they need not be uniform as the newly constructed sources vary with cap. Thus each nonempty finite rival differs from the ordinary target at some later arity.

Section 6 gives the same fixed positive four-taxon exterior and a cross-cherry topology event whose probability is a known positive ordinary-Kingman factor times b_n. Retaining that event versus its complement makes an explicitly authorized binary coarsening. Matching all b_n through the largest queried arity matches the entire finite transcript in this restricted exact diagnostic menu. Consequently a sound observation-only certifier cannot halt affirmatively on the ordinary target after finitely many such queries against unrestricted unknown-size rivals.

The prior factor is consistent with the direct n=2 balanced-four-lineage probability 1/9; no error in that constant is established by this review.

## Scope and provenance

The rare-arm coefficient/sign proof and finite-sum lemma remain the separately reviewed DIAGONAL-CHARACTER-FINAL.md, SHA-256
05fdaf1563839a7c8e19d030ffcaa6de93b40be6d6055af702fd4c45748e1697,
bound by review 1ea2e16a976f92f62d29b3da9343e190c7996eedc0e68f2d35c561825dfb8a97 and its final addendum.

This result removes the total-hazard and fixed-target gaps for the DIAGONAL subproblem. Full forest coordinates can still distinguish these words at the same cap. Equality of the binary cross-cherry rows is not equality of their full rooted-topology laws. The theorem does not add internal actuator IDs, protected-edge replacement, arbitrary parameter ties, paired mechanisms or unsupported shared registers.

The original rich-menu G4 obligation and coupled strict-source G3 recognition remain open. No empirical data admission, general undecidability, Lean verification, executed all-cap construction, external expert acceptance, or historical-priority claim is made. This receipt records hand/source review, not a new numerical census.

