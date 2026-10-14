# Hand review: constrained splitting bound and reset cost

Reviewer: Codex whole-source lane, 14 October 2026.

**SCOPED HAND ACCEPT.** Reviewed the complete
[Laplace packet](../../general-algebra/continuation-0244z/POSITIVE-SPLITTING-PROCESSING-AND-RESET-COST-GATE.md),
SHA256 `4fc627c417918b9320a5c102c113c38e5334e8b87d5813121730b1d4f281254e`.
No mathematical correction requested. This accepts the formal inequality,
sharp example, auxiliary reset calculation and stated transfer limitations;
it establishes neither finite INDEPENDENT forcing nor exact source returns.

## Algebra checked independently

For the stated ordered product, coefficients of the free words `TV`, `TTV`
and `TVV` give respectively

    sum t_i u_i = 1/2+c,
    sum t_i x_i u_i = 1/3+c+2d,
    sum t_i u_i^2 = 1/3+c-2e.

In particular the sign of e agrees with
`[V,[T,V]]=2VTV-VVT-TVV`. With `delta=sum t_i^3` and weights t_i,
the telescoping identity in the packet gives `E[x]=1` and
`g=Var(x)=(1-delta)/3`. Direct subtraction then gives

    Var(u) = 1/12-2e-c^2,
    Cov(x,u) = 2d-1/6.

For `g>0`, the variance inequality therefore yields

    chi=e+c^2/2-d
       <= 1/24-d-(2d-1/6)^2/(2g)
        = -delta/24-6(d-delta/12)^2/(1-delta).

No sign restriction on u_i or v_i was used. If there is only one positive
t_i, it equals 1, x is constant, and the identities force `d=1/12` and
`e+c^2/2=1/24`; hence `chi=-1/24` without a zero denominator.

Conjugating the logarithm by the stated processor gives the packet's
coefficients: `[aT+bV,T+V]=(a-b)[T,V]`, while the second-order processor
contributes `-k` to both cubic coefficients. Substitution into
`e'+(c')^2/2-d'` cancels every processor term. The invariance applies to
this similarity-processing problem, not arbitrary physical parameter retuning.

## Sharp stage count checked independently

For s repeated symmetric `V/(2s),T/s,V/(2s)` steps, adjacent V factors merge,
all positive t_i equal `1/s`, and `u_i=1-x_i/2`. Thus equality holds in the
variance inequality and

    delta=1/s^2,    c=0,    d=delta/12,    e=delta/24.

Together with `sum t_i^3>=1/s^2`, this proves the stated sharp
`-chi>=1/(24s^2)`. Each finite-stage obstruction is strictly signed even
though its infimum over stage counts is zero. The packet correctly preserves
that distinction. Its comparison of an uncontrolled `O(H^4)` remainder with
the shrinking `H^3/(24s^2)` bound is a limitation of a proposed proof, not a
claim that an exact-sign barrier is impossible.

## Literal routing and physical cost checked independently

For the actual finite forest routing maps, `RS_g=I` implies
`P_g=S_gR` is a column-stochastic idempotent. Consequently `D_g=P_g-I`
has nonnegative off-diagonal entries and zero column sums, so it is a valid
auxiliary finite-state Markov generator. Its exponential is exactly

    exp(uD_g)=P_g+exp(-u)(I-P_g).

Since `RP_g=R` and `P_gS_g=S_g`, it follows that
`R exp(uD_g)=R` and `exp(uD_g)S_g=S_g`. This evolution changes colours
without changing any uncoloured forest, even before projecting its initial
distribution. In particular it has zero uncoloured pair-merger hazard.

On a genuine two-colour root state space, P_g is singular. The displayed
exponential remains invertible at every finite u and equals P_g only in the
infinite-time limit. Infinite auxiliary reset time therefore need not carry
positive physical coalescent-clock cost. The source's own legal reset remains
instantaneous; the auxiliary Markov interpolation is not asserted to be an
admitted source operation. The packet does not infer a general impossibility
of enlarged representations from this example.

## Scope and verification

The free-algebra identities do not become legal topology observations merely
because their coefficients have a sign. The separate forest-quotient,
radial-family, body-retuning and reset-cost hypotheses remain absent exactly
as stated. None is filled by this review.

This was fresh hand algebra and a literal-source interface audit. The reviewer
previously read the October 8 reset supplier and wrote a separate signature
applicability audit; that related prior involvement is disclosed. The present
quantitative derivation was checked independently of its author's primary
paper reading. No new primary reread, numerical test, symbolic computation,
proof-assistant execution or Git operation occurred. Historical novelty and
bibliographic completeness were not audited.
