# Independent review: finite persistence without COMMON calibration

Reviewer: Codex critical-review lane, 13 October 2026. Independent hand
audit within the research team; no formal verification.

Reviewed [INDEPENDENT-FINITE-PERSISTENCE.md](../chronology/continuation-1837z/INDEPENDENT-FINITE-PERSISTENCE.md),
SHA256 `0a3c00e2acf923959b4689363c091e4ec43deca964838695d90fe942fd3ba17e`.

**Hand acceptance of the stated compactification consequence.** A growing
exact INDEPENDENT-prefix sequence for one fixed finite equal-arm private
target has a subsequence with the target's finite strict cell list and
effective ordinary gaps. Infinitely persistent strict cells are excluded.
The proof does not remove a possible nonzero weak clock reservoir and
does not establish INDEPENDENT finite forcing.

The legal three-root no-merger probability bounds the whole physical
equal-arm clock: each cell has
`d3=(1-3p) exp(-3t)+3p exp(-t)<=exp(-t)` and each ordinary interval
has `d3=exp(-3a)<=exp(-a)`. Their diagonal probabilities multiply, so
matching the target gives the derived bound `H_r<=-log D3(T)`. This is a
consequence of a row of the actual INDEPENDENT law, not a supplied size
or clock restriction.

After selecting `H_r -> H*`, appending a positive passage of length
`Hmax-H_r` gives a fixed-clock auxiliary sequence whose finite-cap
INDEPENDENT laws converge to `T E_(Hmax-H*)`. The appended factor is proof
bookkeeping. No observation of that modified source is being requested.
The inherited compactification applies to arbitrary fixed-clock source
arrays; it does not require their finite endpoint target to share the
same COMMON clock. In the limiting carrier the appended interval remains
an ordinary final interval, because its original density is exactly one
and its endpoints converge.

The signed coefficient was checked directly from the no-merger diagonal:

    Phi_T(n) = beta n(n-1) + sum_i phi_i(n),
    beta = (H_T-H*+delta)/2.

The duration-dominated quadratic limit gives
`sum target durations = sum persistent durations +4 beta`. After
subtracting it, `Psi_T(n)=sum_i psi_i(n)+beta n`, with every `psi_i>=0`.
Fatou therefore gives `sum b_i<=B_T-beta`, irrespective of the sign of
beta. The resulting finite bias sum and duration sum justify the linear
dominated-convergence step using `psi_i(n)/n<=b_i+t_i/4`. It gives equality
and then exactly the absolutely convergent residual product identities
used by the reviewed meromorphic theorem. No use of beta nonnegativity
is hidden in these steps. The finite-persistence conclusion follows.

The inherited finite boundary normal form then identifies the finite
strict body and effective gaps with the padded target. Canceling the
known appended ordinary factor on every finite cap recovers the stated
original target body. Equality of the strict lists makes beta zero.
Consequently `delta=H*-H_T>=0`, and the exact physical-versus-effective
clock difference in the finite rivals is
`2 sum_extra p_i t_i -> H*-H_T`. Their maximal unselected strength tends
to zero by the ranked compactification. These claims are compatible and
do not imply that the total extra strength tends to zero.

Even if a later argument made this reservoir vanish, the present note
does not itself supply an INDEPENDENT local finite-forcing theorem:
the reviewed BOTH local theorem includes exact COMMON-clock calibration.
No exact inequivalent all-prefix rival is constructed here. The result
settles one general countable-persistence obligation in the equal-arm
private INDEPENDENT problem while preserving its remaining local duty.

This is a reuse composition plus the D3 clock bound and signed resource
bookkeeping. Historical novelty is not certified. No computation, Lean
check, or Rust check is offered as evidence for this proof.
