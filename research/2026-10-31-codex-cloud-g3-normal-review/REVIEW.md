# Independent review of the global cap8 normal and source-action conversion

Stable key: G3-GLOBAL-NORMAL-ACTION-CLOUD-REVIEW-20261031-01.
Reviewer: existing cloud main, 31 October 2026 UTC.
Author of the reviewed proof: Codex Terra. Verdict: **scoped HAND ACCEPT**,
conditional on the named completed physical-source, complete-commutator,
all-source cost and fixed-H bias suppliers. No Lean or new source-engine
verification is claimed. Original G3, AG-Pair and general G4 remain open.

## Exact reviewed statement and identities

The reviewed proof is `../2026-10-31-codex-terra-g3-normal-coercivity/GLOBAL-NORMAL-ACTION-BOUND.md`,
SHA256 `2a91b71cbe20758745fdd085612f751e749dea61ac4fab8620711cb84409bbd6`.
The separately reviewed action conversion is
`../2026-10-31-codex-terra-g3-return-residual/BIAS-FREE-ACTION-INTERFACE.md`,
SHA256 `04c9a70f3b50322796654eaa4bd37d2b8d73ad28f0ee70fb8f0af4edb2aecebe`.
Both concern one original strict paired equal-arm same-tuple finite word,
both original clocks, and the complete cap12 commutator with the unchanged
reference. Fix one sufficiently small allowed H BEFORE h tends to zero.
Counts, chronology, relative scales and strict rare coins are unrestricted.
Constants C_H are independent of those word choices.

Put L=H/4, e=1-x, d_i=1-q_i, X_i=d_i/e,
y_i=beta_i*u_i/h^2, and use the probability measure
`<f>=(1/L)sum ell_i*f_i`. The new conclusions are

    <X^2(1+X)(X-1)^2> <= C_H h^(1/3),
    <(X^2-1)^2> <= C_H h^(1/6),
    Action_h <= C_H h^(25/6).

The first two conclusions use no later coupled-energy/debt bootstrap.
The last uses the source-action conversion audited below, also without
that bootstrap. All these are weaker than the sufficient calibrated
phase input of order h^(6+delta).

## 1. Actual normal, inherited fair factor and new coefficient check

I read the exact-source bindings, the complete inherited fair proof and
its independent G4 review. The normal body is SHA256
`2844871e9c48a810df35670da4b5eb1f8c02c564d0c5bf3a13e43c141c097a3a`,
member `public-ready-fair-joint-v2/fullcap-normal/NORMAL-POLYNOMIAL.json`
of decoded public source archive
`baafd3589c9d2aab0f7c7a0e0d1b00a0f4bf0a2a61267804f3a3976b26ba2ad6`
at commit `704dd6521062dd485dee4375d3d8905a78964679`.
The old complete proof has SHA256
`01141169556ac7f4840c03f79e323c99b32d30edff8712a33ef07c57f7f863ea`;
its independent review has SHA256
`6f40846354e4e9a73670aa15a27e61a29c407fcd0b346f647633f4f30544cf8a`.

Those suppliers establish the SAME scalar f4, not a substituted leading
jet: all 8-to-6-to-4 cross paths lie in the annihilated vector, so the
full commutator gives exactly `sum W4_i*f4_i=0`. Each positive W4 is the
actual b8 prefix times b4 suffix, including all ordinary populations.
On the fixed COMMON budget it is bounded below by exp(-28H).

The inherited exact fair factor is
`f0=q^2*(q-x)^2*d^3*R0`. Its two positive loss derivatives at (1,1)
give c(d+e)<=R0<=C(d+e) on ONE weak rectangle, with bounded
derivatives. The independent prior review even supplies an explicit
rectangle. The inherited bias identity is
`partial_beta f4|0=(-28+2q partial_q)f0`.

I read the new corrected coefficient-check source and its actual exit-0
log. It selects the large polynomial factor in the SAME saved f4 and
checks the exact prefactor and both divisibility/corner identities for
beta degrees 2 and 3. The initial factor-selection error and exit-1
trace remain preserved. I did not rerun the source engine or this check.
I separately verified all 19 exact byte hashes in its original manifest
SHA256 `b41755b077903a5c45d4e7ecbf646f92e0b7e5738407a351ecd5a3369fa8f1b4`.

Dividing by (1-beta) gives the polynomial extension
`Fbar=f0+beta*f1+beta^2*R2`. Therefore
`f1=(-27+2q partial_q)f0`, with the corrected -27, and

    |f1| <= C d^2 |d-e| (d+e)^2,
    |R2| <= C d^3 (d+e).

The latter follows because the degree-2/3 core coefficients have a
factor d and their quotients vanish at the corner. It is uniform over
the closed beta interval, not a bounded-beta/e expansion.

## 2. Uniform coercivity including rare coins and microscopic cells

The EXACT physical gap is
`ell=log[1+(1-beta)d/(2q)]`. Its ratio to (1-beta)d has a bounded
positive removable extension. All divisions of coin factors in the
proof are therefore uniform, including rare strict coins.

With Y=beta*d/e^2, division by `C4*e^5*ell` yields the positive term
`c X^2(X-1)^2(1+X)` and errors bounded by

    C Y |X-1|(1+X)^2 + C(1+X)Y^2.

For X>=1/2, Young absorbs the mixed term because
`(1+X)^2/X^2<=9`; for X<1/2 it is bounded by CY. Y and y have
uniform comparable factors. Keeping the actual W4 in the exact zero
sum gives the claimed coercive inequality. The already accepted
`<y^2>=O_H(h^(2/3))` and separate all-coin physical maximum
`Xmax=O_H(h^(-1/3))` imply Q:=<X^2(1+X)(X-1)^2>=O_H(h^(1/3)).
There is no higher-normal-moment limit exchange or count loss.

The charge equation gives `<(u/h)^2>=4+O_H(h^(1/3))`. Converting to
X changes its average by O_H(h), since `<(u/h)^4>` is bounded and
`<u*(u/h)^2>=h*<(u/h)^3>=O_H(h)`. Thus `<X^2>=1+O_H(h^(1/3))`.
On X>=1/2, `(X^2-1)^2<=6F(X)`. On D={X<1/2}, the missing mass is
bounded by `C[|<X^2>-1|+sqrt(Q)]`. This proves BOTH the stated
variance bound and `<1_D>=O_H(h^(1/6))`. It explicitly eliminates the
zero-charge fair microscopic gap mass; bias suppression alone did not.

## 3. Independent audit of the action conversion

I read the old positive-transverse source cost, exact reference-calibrated
action, and the source coefficients reused by the accepted full-band
bias proof. They use the LEFT-normalized actual cell throughout:
`C=exp(-tau Q)B`, with its ordinary interval retained before the cell.
Their uniform closed-coin jets are

    J=v[54 beta^2 u^3-15 beta u^4+(3/2)u^5]+O(u*s),
    F=v[-beta u^2/5+u^3/30+O(beta u^3+u^4)],
    ell=2vu[1+O(u)],
    a_ref=360h^2+O(h^3), b_ref=12h^4+O(h^5).

The F coefficients agree with the J9/15 source: its quadratic is
-3v beta/15 and its fair cubic is u^3/120. No right-normalization or
diagonal-only rescaling is inserted. Dividing Phi=J-a_ref F+b_ref ell
by the ACTUAL ell*h^4 gives, with z=u/h,

    (3/4)(z^2-4)^2+27y^2-(15/2)y*z^2+36y
      +O((u+h)(1+y^2+z^4)).

The beta*z terms and signs in the submitted note are correct. Cauchy
with the old fourth moment and new y^2 bound controls the mixed term;
the separate maximum u controls the uniform remainder. Hence the
additive error after averaging is O_H(h^(1/3)), as claimed.

Finally `z^2-4=4(X^2-1)+O((u+h)z^2)` and the same fourth moment
control conversion of the squared discrepancy without assuming z^8.
This proves Action=O_H(h^(25/6)). The positivity/zero set of Phi is
the named old source theorem; it is not inferred from the signed
leading expansion.

## 4. Direct consumer input and exact remaining gap

For EACH FIXED sigma>0, cells with `u_i<=h^(1+sigma)` eventually
satisfy X_i<1/2. Consequently their ORIGINAL-fibre total gap obeys

    (1/L)sum_(u_i<=h^(1+sigma)) ell_i <= C_H h^(1/6).

This is a direct gap-mass estimate. It does not assume the full-operator
replacement jet, restore the clocks after replacement, prove a ratio
inverse, or repeat any consumer telescoping argument. It is available
as an input to those separately owned conditional implications.

No review of the later reference-energy, negative-jump debt, eighth
moment, improved normal rate or midpoint-alignment proofs is implied
by this acceptance. Those preserve their independent-review-pending
status. The source-action producer still needs a substantially sharper
correlated return estimate or another original-source route to phase
or a total recognizer. Fair subcase exact rigidity is inherited; a
vanishing aggregate variance does not force every finite-word coin
to be fair or every source length to equal the reference.

This is a source-bound hand review. No fresh cap, parameter grid, source
bank construction, physical execution or formal checker was run.
