# Independent review: fair second jet and exact cap-three collision

Reviewer: Codex critical-review lane, 13 October 2026. **Scoped hand
acceptance**, with a separately labelled exact symbolic transcription
check and no formal verification claimed.

Reviewed [INDEPENDENT-LOCAL-CURVATURE-GATE.md](../general-algebra/continuation-1945z/INDEPENDENT-LOCAL-CURVATURE-GATE.md),
SHA256 `5fa2df8ca971a8ccc19340fd0c02e94908ee695c896093c6898da354092d5692`.
The inherited all-cap full-forest generator identity was inspected directly.

The fair specialization of that identity is correct: at g=1/2 the two
arm-time derivatives sum to the common-duration derivative, while
`B_gg=-2 B_p`. It gives `Q B=2 B_t-B_p/4`. At duration zero,
`B_t=(1-2p)Q` in the full labelled-forest algebra, because each specified
pair merges to first order exactly when it chooses one arm. Thus
`B_pt=-2Q`; differentiation in duration yields
`B_tt=(Q^2-Q)/4` at fairness. The finite-cap analytic extension legitimizes
this derivative calculation at zero without admitting a boundary source
as a rival. Expansion of the exact pair clock gives precisely the same
second jet for `E_tau`. Multiplication by fixed stochastic prefixes and
suffixes preserves the order of the remainder. This excludes a uniformly
nonzero transverse fair second-order term, not higher-order coercivity.

For the approximate N-cell construction, `N tau(c/N)` tends to c/2,
strictly less than H. The stated total ordinary gap is therefore positive
and can be divided into N+1 positive gaps. Replacing each fair cell by
`E_tau` leaves a product of ordinary kernels of total duration exactly H.
Stochastic telescoping bounds the full capped row-norm error by N times
the one-cell `O_m((c/N)^3)` error, giving `O_m(N^-2)`. The physical clock
is `H+N[c/N-tau(c/N)]`, which tends to `H+c/2`. Pair equality is exact;
the higher capped laws only converge. No exact-prefix conclusion follows.

The displayed pair/triple defect factorization, strict interior
parametrization and padding calculation are consistent. As p increases
to 1/4, the matched pair clock decreases to zero; hence every fixed
ordinary target admits the required strictly positive pads. Sampling
consistency on three roots gives `D2=D3+(2/3)P2`. Exchangeability fixes
the three two-root forest probabilities and the three one-root labelled
tree probabilities within their respective classes. Thus D2 and D3 do
determine the complete capped forest kernel through three, with opaque
inputs handled by the inherited grafting property. This is more than
equality of the two diagonal coordinates alone.

The cap-four expression is strictly negative on the parametrized
interior range: its denominator is positive and
`32p^2-32p+9=32(p-1/2)^2+1`. Multiplication by the positive ordinary-pad
factor preserves that sign, giving the stated exact separating row.
The reviewer independently formed d2,d3,d4 from their displayed binomial
expressions and used exact SymPy factorization to check identities (4)
and (6); both residuals were identically zero. This small transcription
check did not execute or alter the author's checker or receipt and is
separate from the all-cap hand argument.

No defect was found. These results show the limitations of second-order
clock-subtracted curvature and of cap-three testing for the private
INDEPENDENT ordinary target. They do not show that every finite prefix
has an exact inequivalent rival, and do not remove the arbitrary-count
weak reservoir. The fixed-COMMON higher-jet theorem is neither contradicted
nor applied outside its hypotheses. Historical novelty is unassessed;
no Lean or Rust verification is asserted.
