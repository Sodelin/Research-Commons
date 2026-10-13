# Fresh adversarial audit of the analytic finite-persistence argument

Contributor: Codex critical-review subagent, 13 October 2026, 20:59 UTC.

Status: **second hand audit; no defect located in the analytic argument**.
I previously contributed to and accepted this proof package. This is therefore
not a newly independent reviewer or formal verification. The lead requested
this fresh pass after the user challenged the main advance. I reread the
proofs and their resource/compactification suppliers, rederived the critical
inequalities, and actively looked for a counterexample or an omitted premise.
No computation or Lean check is being substituted for these arguments.

The conclusion of this review is deliberately separated: the standalone
summable-budget analytic finite-persistence theorem survives this pass. The
private finite-forcing composition additionally requires the finite boundary
comparison and the mixed-target local theorem. The lead is independently
reauditing the latter; this note does not preempt that audit or claim full G4.

## Exact bodies reread

| Body | SHA256 |
|---|---|
| [Carlson bridge](../chronology/continuation-1837z/CARLSON-CONTINUATION-BRIDGE.md) | `9411158e6523c33243c4c0a894441bf0b695af13648c55a13f413f6d7022a2a7` |
| [Meromorphic finite persistence](../chronology/continuation-1837z/MEROMORPHIC-FINITE-PERSISTENCE.md) | `2a02c32ee1961f2391d1e380baa73349fb6d225dae8bd2442ec676db2138bf2f` |
| [Private BOTH synthesis](../chronology/continuation-1837z/PRIVATE-BOTH-FINITE-FORCING.md) | `305d7d80f67f4702bc884ef53817a123c5650dec34fcfb5e7c7e2a17813c4170` |
| [Finite-persistent consequence](../general-algebra/FINITE-PERSISTENCE-AND-GLOBAL-GATE.md) | `c6797ec0c29b0a50a053804cc1d0481d2218fc4e2f3b64cb371df639b79b39ad` |
| [Inherited residual budgets](../../2026-10-10-dot-g4-negative-reservoir-diagnostic-1137z/EXACT-NEGATIVE-RESERVOIR-GATE.md) | `50f3fd24f18750b581c69c2a0e3e714a3c221b3b37006a8fd57e82397ea3401d` |
| [Inherited compactification](../../2026-10-10-dot-g4-countable-clock-compactification-1105z/BOUNDED-CLOCK-COUNTABLE-COMPACTIFICATION.md) | `06b4bcb812f6680eb0c404e4b449050c3380d26cc0697a09d9fb0188a98e1019` |

## 1. The Carlson bound uses fixed cell parameters

For each factor, `t,h` remain fixed while `z` varies. This is essential.
The unequal-arm substitution `h -> h+d-2dz` is not made in this theorem.
Its quadratic growth obstruction, recorded separately in the unequal-cell
gate, is therefore not a counterexample to the equal-arm statement.

The potentially delicate pairing on the shifted central contour is valid:
if the shifted cosine is `r exp(ia)`, the average of the values at opposite
angles is `r^(2z) cos(2za)`. Hence its modulus is at most
`r^(2 Re z) cosh(2 Im z a)`. This keeps cancellation before the modulus and
does not multiply the product by a factor two per cell. The argument does
not assert positivity of the original shifted heat density.

The Gaussian moment bound is also valid after wrapping: on the fundamental
interval, `|theta+2pi k|>=|theta|`, so the central integral of the increasing
even function `cosh(h Im(z) theta)` is bounded by the full real Gaussian
moment. The outer and vertical estimates retain exponential decay in `1/t`.
For the large-imaginary-part regime the raw bound
`exp(h^2/(4t))` is absorbed by `exp((8/pi)h^2 |Im z|)`.

Thus the stated bound `exp(3h^2|z|+8t)` is justified in the stated domain.
Peeling finitely many factors leaves an arbitrarily small coefficient of
`|z|`, while the removed factors have finite globally uniform right-half-plane
bounds. This proves zero exponential type without assuming `sum h^2/t`.
Applying Carlson after shifting by one avoids any ambiguity about extension
across the imaginary axis in versions of its hypotheses.

As a stress family, take `t_j=2^(-3j)` and
`h_j=(2^(2j)+1)t_j`. Then both required sums are finite but
`sum h_j^2/t_j` diverges. Every `h_j/t_j` is an odd integer, so this also
places every cell on the exceptional theta-zero branch. The proof's bounds
still apply: they require small absolute `h`, not bounded `h/t` or finite
energy. This is a check of the hypotheses and estimates, not a target-equal
source construction or a computational test.

## 2. Off-pole convergence does not assume a meromorphic infinite product

For a compact set avoiding the half-integer pole lattice, the central
contour can be shifted inside `[-pi/2,pi/2]` even when `Re z` is negative:
the cosine remains separated from zero. Its power is
`1+O_C(theta^2+h^2)` there. The omitted real Gaussian mass and the vertical
segments are exponentially small.

On the complementary interval, the finite Taylor-subtraction argument is
valid on a fixed complex neighborhood of `[0,1/2]`. The local inverse-angle
branches near zero both remain near `pi`; evenness removes the branch in
their composition with the heat density. For small absolute `h`, the
Gaussian's real distance from its centers exceeds its imaginary distance
uniformly. This supplies the exponentially small bounds on each fixed
number of Taylor coefficients and the remainder. No Taylor series is
assumed to converge across the whole segment. The denominators in the
continued Mellin integral are uniformly separated from zero on the chosen
compact set.

Consequently `U_i -> 1` normally away from the fixed pole lattice with a
summable `O_C(t_i+h_i^2)` majorant. The infinite product is holomorphic on
that punctured domain. It need not extend meromorphically through a lattice
point; the proof does not require it to do so.

## 3. The pole and zero argument survives both possible first poles

For real `h`, the theta product's zeros are exactly `h=s t` with odd integer
`s`, and are simple in `h`. At such a zero, differentiating its curve and
using the heat equation gives `H''(pi)=-s H_h(pi) != 0`. Thus the first
pole is genuinely `-1/2` or `-3/2`. This includes arbitrarily large odd `s`;
there is no uniform residue lower bound in the argument.

An infinite family has infinitely many factors with the same one of these
two first poles. On any fixed sufficiently small circle about that point,
the factors tend uniformly to one. Rouché applied to `(z-p)U_i(z)` then
gives an off-pole zero. Uniform convergence on every smaller fixed circle
forces these zeros to approach `p`; they must include infinitely many
distinct points. They cannot all equal `p` because the residue is nonzero.

At every such off-lattice zero all other factors are holomorphic and their
remaining product converges normally, so no pole can cancel that zero.
Carlson and the identity theorem identify this product with the finite
target product on the punctured plane. Only the **finite target product**
is then used as a meromorphic function at `p`. Its finite pole order cannot
accommodate infinitely many zeros accumulating at `p`. This distinction
removes the apparent infinite-product-at-a-pole objection.

## 4. Resource signs and compactification quantifiers

The inherited diagonal identity has `beta=delta/2>=0` at a common fixed
COMMON clock. Its order of limiting operations is legitimate:

1. `0<=phi_n/n^2<=t/4` and `sum t<infinity` give the quadratic identity by
   dominated convergence.
2. Nonnegative `psi_n` then permits Fatou at the linear scale and yields a
   finite bias budget `sum b <= B_T-beta`.
3. Only after this budget is known is the bound
   `0<=psi_n/n<=b+t/4` used for linear dominated convergence.
4. Subtracting the linear identity gives the absolutely convergent residual
   identity and therefore the exact integer product identity for `U`.

No sign has been silently reversed and no logarithmic-scale sum is
interchanged. `sum log cosh(h/2)<infinity` gives `sum h^2<infinity`, as needed
by the analytic theorem.

The compactification first selects one subsequence of ranked physical cell
parameters, their actual positions and one proxy-clock measure. This is
done before selecting a forest cap. Its estimates then hold at each fixed
cap along that same subsequence. Finite persistence means only finitely
many positive limiting strengths; the maximum of all unselected strengths
then tends to zero along that subsequence. It does not itself give a bound
on the number of small cells in an approximating source.

The finite-forcing contradiction only needs eventual all-law equality
along this selected subsequence. It does not claim eventual equality for
every sequence outside that subsequence. The separate finite-persistent
consequence uses finite boundary chronology and the mixed local theorem
to remove the remaining strict small cells; neither removal follows from
the analytic argument alone.

## Verdict and remaining audit obligation

This fresh pass found no mathematical counterexample or omitted premise
in the Carlson/meromorphic finite-persistence theorem, its resource input,
or the described compactification quantifiers. It does not increase the
verification level beyond a hand proof and a repeat adversarial audit.

The consequential open audit interface is the mixed-target local exclusion
used after finite persistence. If that provider fails, the analytic theorem
can remain valid while the private finite-forcing synthesis and its
original-source corollaries must be withdrawn or made conditional. The lead
is auditing that interface independently. General uncalibrated reticulate
targets and INDEPENDENT-only finite forcing remain outside these conclusions
regardless of the audit outcome.
