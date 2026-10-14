# Root acceptance: exact energy-template obstructions and the surviving source duty

Reviewer/publisher: Codex G4 lead, 14 October 2026, 03:30 UTC.
Status: scoped hand acceptance. Neither original G4 alternative is closed.

## Statements and attribution

The Sol lane's [exact quadratic reduction](../general-algebra/continuation-1945z/EXACT-NINE-STATE-QUADRATIC-CERTIFICATE-REDUCTION-SOL.md),
SHA256 `c032a131f1584f0dfeb45744877f625d65b50c1be1251b63c0de30e1ce67d9cc`,
gives the exact three-by-three negative-semidefinite test for a proposed
energy. Its [independent laplace review](../general-algebra/continuation-1945z/EXACT-NINE-STATE-QUADRATIC-CERTIFICATE-LAPLACE-REVIEW.md),
SHA256 `533398f7cc0d27f71a18f40bedf4e9c656b1bfd0aae35b210de6a8d40d83f35b`,
checks the actual diagonal completion, singular Schur cases and exact
source witness. It also reproduces the one rational sign countercheck.

The lead proposed, and the Sol lane developed and checked, the separate
[fixed-clock C1 extension and actual-prefix supplement](../general-algebra/continuation-1945z/FIXED-CLOCK-DIAGONAL-VANISHING-C1-ENERGY-OBSTRUCTION-SOL.md),
SHA256 `47bc01028dd7719fc4f6c67951a1409b3cd0ce1985ad48b22cb2fc54f637843b`.
The [whole-source review](../general-algebra/continuation-1945z/CLOCK-AWARE-ISOTROPIC-ENERGY-WHOLE-SOURCE-REVIEW.md)
separately checks that extension. The earlier frozen candidate's escape
discussion is historical: clock dependence is now excluded only within
the more precise hypotheses of this successor.
The whole-source review has SHA256
`afc45f7ce389b6c4fb67bde6400391008fe50f27f6be16a62e694b4d34f837e1`.

## The accepted implications

Use the inherited actual nine-coordinate spectral state, normalized by
`a=X/b7, b=Y/b7, v=V/b4`. Keep the entire finite diagonal vector
`d=(b2,...,bm)`, m>=9, so its pair clock is available.

**Unrestricted-state certificate.** For any fixed H>0, no energy

    F_d(a,b,v)=v+P_d(a,b)+Phi(d)

has all the following properties: P_d vanishes on a=b and has zero
derivative at the upper origin; Phi agrees at the identity and E_H;
and every physical append decreases F for both signs of sufficiently
small upper inputs at every actual prefix diagonal within clock H.
This includes arbitrary finite clock-dependent coefficients in
`P_d=c(d)(a^2-b^2)`, with no regularity in d assumed.

The bounded-clock witness uses a small strict full-rank diagonal return,
its local physical parameter section, and a weak exact f-zero cell with
`-h+2e!=0`. The chosen cell's small defect is cancelled in that section;
strict pads fill the prescribed H. Thus the constructed finite word has
exactly the E_H diagonals. At virtual upper input zero, each genuine append
maps the upper coordinates to (l,l), so only the Phi increment remains.
All increments are nonpositive, their finite sum is zero, and each is
therefore zero. At the f-zero cell a nonzero linear shear remains, whereas
the P difference is of smaller order. One perturbation sign increases F.

This uses a fixed **pair-hazard** budget, not bounded total arm exposure.
The one fixed rare arm remains positive. Every realizing word is finite
and strict; the limiting source is never a witness. The same word and
tuple supply every diagonal and selected state.

**Actual-prefix counterexample for zero potential.** With Phi=0 and
locally bounded c(d), even restricting
`F=v+c(d)(a^2-b^2)` to real source prefixes cannot make it monotone.
A weak strict cell U has a prescribed sign of f. The actual prefix
`E_L U_epsilon E_epsilon` has

    a=e^(-15L) f(U_epsilon)/p7(U_epsilon),
    b=a e^(6epsilon), v=0.

Appending one fixed strict cell B0 with f0=0 and e0!=0, and a positive
trailing pad, increases v by `2s0 e0 a+o(|a|)`. Choose the physical
U branch so e0 a>0. All quadratic corrections are O(a^2), so the
energy strictly increases for small positive epsilon. This is an
actual source word, not an arbitrary triangular matrix or virtual
prefix state. It is not asserted to return to an ordinary endpoint.

## Review and verification boundary

I checked the normalized append formulas, the exact positive clock
allocation, rank-to-local-section implication, finite telescoping,
zero-gradient remainder, and the actual-prefix linear-versus-quadratic
comparison. The two explicit weak branches have leading f coefficients
1/120 and -1/24 as stated. All source expansions and submersion suppliers
are inherited and attributed, not reconstructed as new results.

The rational fixture in the first note is a separate bounded exact
arithmetic check. It refutes only its displayed pointwise sign proposal.
The general hand arguments do not follow from that fixture. No Lean/Rust
build or proof-assistant verification was performed. Historical novelty
of these deductions is unassessed.

## Surviving master obligation and integration handoff

These results reject specified energy templates. They do not reject
energies using an actual-prefix constraint together with a nonzero
potential, a linear correction, nonzero values on a=b, lower T/U state
or additional forest information. In particular, they do not prove
ordinary no-return at cap nine or construct full-forest returns.

The finite INDEPENDENT master still requires a legal finite I certificate
forcing the fixed target's finite COMMON certificate against every
finite unknown-size original rival, or exact later-inequivalent admitted
rivals for every finite full-I prefix of one fixed target.

For the existing formal integration owner, the reusable proof interfaces
are: a strict finite diagonal path of total clock H containing a nonzero
f-zero shear; a finite monotone-sum equality lemma; and a derivative-zero
remainder lemma giving increase in one signed direction. These are
scoped certificate-obstruction interfaces, not source suppliers for G4
closure. The hand source-path provider and legal full-I adapter must
remain separate premises if an abstract component is formalized.

The next meaningful positive attack must establish an invariant on
actual chronological prefixes with information absent from the excluded
templates. The concrete uncontrolled term remains `2Xe`, coupled to
the lower bands and body parameters. No tooling or permission blocks
execution; the obstruction to finishing the master is mathematical.
