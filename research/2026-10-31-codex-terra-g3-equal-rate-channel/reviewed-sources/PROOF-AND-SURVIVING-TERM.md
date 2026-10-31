# Matched cap5/cap6 rate: an actual-source bias-cost identity

Contributor: Codex Terra, 31 October 2026. This is a hand-derived
comparison of the existing cap5 5-to-2 and cap6 6-to-4 source channels,
with the targeted exact scalar and reference-diagonal checks described
below. It uses the SAME original strict equal-arm paired cap12 fibre and
named completed suppliers. Independent review and formal verification are
pending. The remaining signed endpoint/diagonal-correction inequality is
NOT proved. Original G3 remains open.

## 1. Existing source coordinates and normalization

Fix one sufficiently small allowed `H=(log 2)/m>0`, and write

    L=H/4, T=3H/4, c=exp(-H), h=-log t,
    x=t/(2-t), b=t^2(2-t),
    u_i=-log q_i, v_i=g_i(1-g_i), beta_i=(2g_i-1)^2,
    z2_i=b2(B_i), tau_i=-log z2_i,
    ell_i=log(z2_i/q_i), y_i=beta_i*u_i/h^2.

Keep one actual finite word, both exact clocks, all original chronological
gaps and complete `[K_I,S(t)]=0` through cap12. Put `lambda_r=binom(r,2)`,
`k_r=b_r(K)` and `s_r=b_r(S)`.

For a bare actual cell define, with per-labelled partition EPPFs,

    A_n=3p_n(2,2,1^(n-4))-2p_n(3,1^(n-3)).

The old exact root-drop-two identity is `d6=A6/9`; the audited cap5
5-to-2 source is `tau52=-(5/3)A5`. Their common proportional factors
cancel in their own whole-word commutator equations. The old cap4 bare
charge has a DIFFERENT normalization: `A4=(3/2)chi`, or `chi=(2/3)A4`.
No unscaled A4/chi identification is used.

Define the pair-normalized source **on the LEFT**, in duration notation,

    C_i=E(-tau_i) B_i,  J_n(C_i)=exp(lambda_n*tau_i) A_n(B_i).

The negative-duration factor is source algebra only, not a physical
actuator. This is NOT the G4 right-normalized J convention. Its positive
physical ordinary component remains in the original chronology.

## 2. Exact equal-rate endpoint and diagonal correction

Let `P_i` and `Q_i` be the actual products of ALL factors strictly before
and strictly after `B_i`, respectively, including ordinary populations.
For any such segment set

    D_r(X)=b_r(X)/b2(X)^lambda_r,
    W52_i=b5(P_i)b2(Q_i),   W64_i=b6(P_i)b4(Q_i),
    Delta_i=[D6(P_i)/D5(P_i)]*D4(Q_i).                      (1)

The exact whole-word single-insertion laws and complete commutation give

    sum W52_i A5_i = E52,
    E52=t^10*b*(k2-k5)/(s2-s5)*A5_*,
    sum W64_i A6_i = E64,
    E64=t^15*b^6*(k4-k6)/(s4-s6)*A6_*.                     (2)

The bare starred sources are from the actual fair reference cell. The
normalizations and all k-diagonals are retained; none is replaced by a
fractional reference power. The one-root-drop band vanishes, so there is
no hidden intermediate insertion in the 6-to-4 composition.

The paired I clock fixes `b2(K)=exp(-T)`. Multiplicativity of each
diagonal gives the EXACT, all-count weight identity

    exp(5T)*W64_i/W52_i = exp(5 tau_i)*Delta_i.             (3)

The rates are both 9 because `lambda_5-lambda_2=10-1` and
`lambda_6-lambda_4=15-6`. The current cell is omitted from BOTH prefix
and suffix in (1); its compensating `exp(5 tau_i)` is essential.

Define the signed actual diagonal correction and endpoint residual

    R_diag=sum_i W52_i*exp(5 tau_i)*(Delta_i-1)*A6_i,
    Z=e^(5T)*E64-E52-R_diag.                                (4)

Then the same-cell factors in (3) cancel EXACTLY:

    Z=sum_i W52_i*z2_i^10*(J6_i-J5_i).                      (5)

This is an original-source identity; no weighting is silently transferred
between the two channels and no sign is assumed for `R_diag` or Z.

## 3. The bias cost and the full-fibre error

Let

    s_i=v_i*(beta_i^2*u_i^3+beta_i*u_i^4+u_i^5),
    P_bias=sum_i W52_i*z2_i^10*v_i*beta_i^2*u_i^3 >=0.

The old all-n deletion rule gives the cubic coefficient
`[u^3](J6-J5)=-6v beta^2`. Its old fair rule gives the SAME coefficients
for J5 and J6 through degree five, and the old entire fair derivative
identity eliminates the potentially missing linear-beta terms. Uniformly
through the CLOSED coin interval after dividing the genuine v factor,

    J6-J5 = -6v beta^2 u^3 + O(u*s).                       (6)

The independently coded targeted scalar check below also establishes the
polynomial divisibilities behind (6) directly from the pinned old EPPF
provider; it does not generate a forest bank.

The `O(u*s)` remainder is o(`Hh^4`) only with the SEPARATE actual-arm
weakness theorem, not from weighted cost alone. We read and pin
`../2026-10-25-dot-g3-centered-action/ENERGY-FORCED-WEAKNESS.md`, SHA-256
`881114d6eaae438293cc627a92d8c893496dbe8bce92dad8b981ab27a4a5a6e8`,
Git blob `27277ea08dc79a2e5f6aca2912801f22220a0e9c`. At the paired,
equal-arm, complete-cap12 source scope it states:

    sum_i u_i^3 <= C H h^2,
    max_i u_i <= C H^(1/3) h^(2/3),
    'No division by a coin probability was used.'

Its u_i is the PHYSICAL bigon arm `-log q_i`, including arbitrarily rare
coins. The proof uses the inherited disjoint own-preceding nominal
intervals of length at least `3u_i/8` and full-fibre energy
`E_a<=C Hh^6`. It is not a statement inferred from `sum s_i` alone.
Together with `sum s_i<=C0 Hh^4`, (5)--(6) give, uniformly in all
physical source counts, scales, placements and coins,

    Z = -6 P_bias + Err,
    |Err| <= C H^(4/3) h^(14/3).                            (7)

In particular `Z<=C H^(4/3) h^(14/3)` for every full-fibre word. For
the EXACT actual gap, `2vu<=ell<=2 exp(H0)vu`. Coupling the same current
roots also gives `W52_i*z2_i^10>=c^10`: prefix b5 contributes its COMMON
product to power 10, the current b2^10 contributes `q_i^10`, and the
suffix b2 is at least its own COMMON product. Hence

    [c^10/(2 exp(H0))] h^4 sum_i ell_i y_i^2
        <= P_bias <= (h^4/2) sum_i ell_i y_i^2.             (8)

Combining (7)--(8), uniformly at this fixed H,

    [3c^10/exp(H0)] h^4 sum_i ell_i y_i^2
        <= -Z+C H^(4/3)h^(14/3).                            (9)

Thus the signed matched-channel residual Z is a single, all-source bias
cost receiver. Uniformly over nonempty full fibres,

    Z=o(Hh^4)  iff  sum_i ell_i y_i^2=o(H).                 (10)

This controls ALL scales, and would imply the earlier bounded-U biased
dust target. A rate for Z transfers without the previous square-root loss,
up to the inherited `h^(2/3)` remainder. Equation (10) is an equivalence,
not a proof of either side. A sufficient exact missing sign is

    liminf_(h->0) inf_(K in F_H(h)) Z/(Hh^4) >= 0,          (11)

with H fixed and only nonempty ACTUAL full fibres used. The automatic
upper bound from (7) then gives Z=o(Hh^4), and hence the bias conclusion.

## 4. Why the endpoint and diagonal correction cannot be dropped

Each diagonal factor in `Delta_i` is an actual pair-normalized prefix or
suffix product. The old charge and source-cost bounds give only
`Delta_i-1=O_H(Hh^2)` uniformly and `sum |A6_i|=O_H(Hh^2)`, so the safe
absolute bound on `R_diag` is `O_H(H^2 h^4)`. At fixed H this is NOT
o(`Hh^4`). It may have either sign because `A6_i` is signed.

More decisively, both the endpoint difference and the correction have a
nonzero h^4 coefficient even on the intended exact fair powers
`K=S(t)^N`, with integer `N=T/(3h)`. For r=4,5,6 their actual reference
diagonals satisfy

    log D_r(S)=-binom(r,3)h^3+O(h^4).                      (12)

For the j-th bare reference cell, `j=0,...,N-1`, its actual factors give

    Delta_j=[D6(S)/D5(S)]^j * D4(S)^(N-j-1),
    (Delta_j-1)/h^2 -> -[2a+(4/3)T],

where `a` is its limiting actual I-pair prefix time. The Riemann sum of
the REAL physical weights and `A6_*/h^3->1` gives

    R_diag/h^4 -> -exp(-T)/3
                    * integral_0^T exp(-9a)[2a+(4/3)T] da
      = -(2/243)[(1+6T)exp(-T)-(1+15T)exp(-10T)] < 0.     (13)

The strict sign follows because `(1+6T)exp(9T)>1+15T` for every `T>0`.
On the SAME fair powers the source difference contributes only `O(Hh^5)`,
so `exp(5T)E64-E52` has precisely the same nonzero limit (13).
Consequently neither term in (4) can be discarded, separately bounded by
o(`Hh^4`), or replaced by zero without breaking an intended full witness.
The exact cancellation BETWEEN them is the unresolved return-conditioned
step in (11).

## 5. The source is not pointwise signed

The targeted exact scalar calculation proves, with `q=exp(-u)`,

    z2^15*(J6-J5)|_(beta=0)
      = q(q-1)^6*(7q^4+17q^3+32q^2+7q-7)/8960.

Therefore `J6-J5=+u^6/160+O(u^7)` on weak FAIR actual cells. For a
fixed strictly biased coin its leading term is `-6v beta^2 u^3<0`.
These are strict source cells, but neither sign alone constructs a
fully commuting counterexample. The fair positive piece is precisely
covered by the `O(u*s)` remainder in (6), whose all-word smallness uses
the explicitly pinned physical-arm weakness theorem.

## 6. Evidence and exact remaining boundary

`check_scalar_identity.py` runs ONE symbolic 5/6-root EPPF comparison
against the previously reviewed, SHA-verified finite provider. It checks
the A4/chi normalization, A5, the A6-A5 deletion identity, the complete
fair numerator above, and the polynomial divisibilities proving the
uniform weak-source remainder. `check_reference_diagonals.py` checks the
three fair diagonal jets and the integral in (13). Both direct processes
exited 0; their actual logs are saved. This is a targeted scalar source
evaluation and exact algebra, not a new full forest bank, parameter grid,
Lean proof, or external service.

The scoped prior source, exact endpoint and old physical weakness bodies
are bound in `SHA256SUMS.txt`. Equation (11) remains a genuine signed
prefix/endpoint inequality over the ORIGINAL full fibre. No known source
sign permits dropping `R_diag`; no weak-limit/finite-grid result supplies
the required uniform lower bound. No general recognition, AG-Pair, phase
or original G3 closure is claimed.
