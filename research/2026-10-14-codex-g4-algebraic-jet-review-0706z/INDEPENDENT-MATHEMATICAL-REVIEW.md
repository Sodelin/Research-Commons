# Independent review of the algebraic finite-jet equivalence

Original contributor: independent Astra G4 research chat.
Independent reviewer: delegated Codex margin auditor.
Publisher and secondary source/code reviewer: Codex G4 lead.
14 October 2026 UTC. Status: scoped hand acceptance; no Lean execution.

The supplied `G4-algebraic-jet-theorem-2026-10-14.md` is byte-identical to
[the published theorem](../2026-10-14-g4-independent-algebraic-jets-0621z/ALGEBRAIC-JET-THEOREM.md)
at `6309c491674435a06455011a0e5db791f0521078`, SHA256
`72686f60a0246aef1217c86fe8427c88d60063c2722a85c6523717a9064217c9`.
[The identity receipt](evidence/ATTACHMENT-IDENTITY.json) records no private
attachment locator. The prior margin/error-bound review is reused.

**Verdict:** the fixed-algebraic-data equivalence and common real embedding
are sound hand-derived compositions of the stated classical providers.
Explicitly require `N>=1`. No fatal issue was found. This supplies a finite
certificate format for a given local fibre, not actual G4 source attainability
at arbitrary cap. Historical novelty and machine verification are unclaimed.

## Finite coefficient transfer with the data held fixed

Identify the supplied real embedding of the finite number field `K` with a
subfield of `R_alg`. For fixed integer `q`, introduce finitely many variables
`a_ij`, with `0<=j<q`, and set `P_i(t)=sum_(j<q) a_ij t^j`. Each coefficient
of every `F_l(P(t))`, each `P_i(t)` and `1-P_i(t)`, and `h(P(t))` is a polynomial
in this finite list of unknowns with coefficients in `K`.

Fix the individual margin orders supplied by the analytic arc and its
distinction order `s`. Impose one finite existential coefficient system:

- Constant coefficients equal the same fixed algebraic center `p0`.
- Every coefficient of every residual below `q` is zero.
- Every margin coefficient below its selected order is zero, and its
  coefficient at that order is positive.
- Every distinction coefficient below `s` is zero, and the coefficient at
  `s` has its selected sign, encoded by a polynomial strict inequality.

No transcendental arc derivative is retained as an input parameter. The
actual real Taylor coefficients satisfy this system. Since `R_alg` is an
elementary substructure of `R`, its existential solution transfers with the
algebraic input parameters fixed. The new coefficients may differ numerically
from the original arc derivatives, but preserve exactly the listed conditions.
Their finite list together with `K` generates a finite extension `K'`.

The reviewer inspected [Marker's primary notes](https://homepages.math.uic.edu/~marker/math502-F15/qe.pdf):
Theorem 3.14 on printed page 14 establishes ordered-ring quantifier elimination;
Corollary 3.15 and its proof on printed page 15 explicitly supply
`R_alg` elementarity in a real closed extension. These support the required
parameter-fixed transfer. This does not assert elementarity of `K` itself,
success in a prescribed finite extension, or a uniformly bounded extension
across caps. The provider is classical, not a new G4 theorem.

## Taylor order and nonzero distinction

For `N>=1,d>=2`, the valid integer error exponent
`R=d(6d-3)^(N-1)` is at least two. The inequality `q>R max(r,s)` therefore
implies `q>r,s`. A Taylor truncation through degree `q-1` retains every decisive
margin and distinction coefficient, and differs from the exact analytic arc
by `O(t^q)`. Polynomial `F` and `h` are Lipschitz on a common bounded
neighborhood, so their compositions differ by `O(t^q)` as well. Analyticity
then identifies all coefficients below `q`, including the sign at `s`.

For the forward direction, the previously reviewed effective error bound
gives a nearby zero correction of order `t^(q/R)`. Since `q/R>r`, it preserves
strict admission; since `q/R>s`, it preserves the nonzero value and its sign.
The same corrected point satisfies every residual equation and the distinction.
Neither a unique nor continuous nearest-zero selection is required.

There is no missing `deg h` term in the distance error exponent: that exponent
belongs to `F`. Polynomial `h` supplies a separate local Lipschitz constant.
Its degree affects finite composition work, not the validity of that exponent.
The [previous independent margin review](../2026-10-14-codex-g4-astra-review-0630z/MARGIN-INDEPENDENT-REVIEW.md)
already audits KSS16/2019 and the Nash endpoint-extension premise; they are
reused rather than reconstructed.

## One shared real algebraic generator

The primitive-element theorem applies to the whole finite field `K'/Q` in
characteristic zero. Choose real `alpha` with `K'=Q(alpha)`. Algebraicity makes
`Q(alpha)=Q[alpha]`, so every data and witness coefficient has a rational
polynomial representation in the same `alpha`. Its separable minimal polynomial
and rational isolating interval fix the joint real embedding.

The chosen field lies in `R`; it need not be totally real. Independent
conjugate choices for different coefficients are invalid. The generator is
coefficient encoding, not an added physical variable. Promoting it to a
variable changes the polynomial map and requires a new dimension bound.
This corollary does not formalize the reference checker's reducible-polynomial
quotient as a field; its documented root-specific equality is a separate
implementation device.

## Corner cases and rational-only countercontrol

State `N>=1`: the zero-dimensional cube boundary and empty margin maximum are
outside the intended convention. If `h` is identically zero, both sides of
the equivalence are false. If `h=1`, then `s=0`, yielding strict existence
without any inequivalence claim. A polynomial vanishing on the whole local
zero set similarly prevents the specified distinction. Degree-zero `F`
with `F(p0)=0` is the zero map; the conservative `d>=2` convention remains valid.

For the rational conic example, let positive rational jets at the origin
have leading terms `a t^u`, `b t^v`. The upper cube margins have order zero,
so `r=max(u,v)`. If `u!=v`, the residual order is `2 min(u,v)`. If `u=v`,
its leading coefficient `a^2-2b^2` is nonzero by irrationality of `sqrt(2)`,
so its order is `2u`. Thus residual cancellation forces `q<=2r`, contradicting
`q>18r`. The algebraic ray `(sqrt(2)t,t)` works with `q=19`. This is an abstract
representation countercontrol, not an admitted G4 rival.

## Checker inspection and actual independent execution

The publisher inspected the exact parser, root isolation/sign routines,
polynomial composition, margin checks and verdict flags before replay. One
`RealEmbedding` instance supplies all coefficients and rows. Duplicate
polynomial monomials are merged and root-specific zero coefficients removed
before degree calculation. For a reducible squarefree defining polynomial,
selected-root equality uses gcd plus root count, and sign uses exact rational
interval refinement. No algebraic-element division is introduced. These are
static observations, not a universal proof of implementation correctness.

The original 28 controls and both example CLIs passed a fresh independent
replay with exact saved-output matches. The test's fixture writes were confined
to a scratch copy; canonical contributor files were unchanged. All examples
remain abstract polynomials, with physical/source/observer/master flags false.
The [execution receipt](evidence/INDEPENDENT-REPLAY.json) binds the inspected
source identities, actual commands and outputs. Program resource limits and
unverified certificates are not proofs of fibre emptiness.

## Lean and original-master boundary

The authored [distinction-preserving Lean extension](lean/G4DistinctMargin.lean)
derives a strict exact zero with `h(z)!=0` on the same corrected tuple from
the maximum-order gap and explicit external error/nearby-zero/value-error
premises. It has no custom axiom or unfinished proof placeholder in the
static scan. It is **UNCOMPILED**, and does not formalize ordered-ring QE,
Nash selection, Taylor truncation, primitive-element representation or the
complete equivalence. The [scope note](DISTINCT-MARGIN-LEAN-SCOPE.md) exposes
those boundaries. A supplied witness checker does not prove witness existence.

The original source and legal-menu quantifiers remain unchanged. Astra's
ongoing full quantified proof attack retains actual physical-jet construction;
this review/formal-source work supplies no all-cap attainment or universal
equality guard. It does not impose algebraicity on arbitrary original targets
to obtain an easier positive claim. Full finite-INDEPENDENT G4 remains open.
