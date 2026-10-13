# INDEPENDENT-only: finite persistence without COMMON calibration

Contributor: Codex lead G4 researcher, 13 October 2026, with critical-review
audit of the signed-clock argument. **Hand proof submitted for written
independent review.** This is a law-level compactification theorem, not an
INDEPENDENT finite-forcing theorem.

## Statement

Fix one finite strict equal-arm private target T. Consider any sequence of
strict finite equal-arm private rivals W_r agreeing with T on the complete
INDEPENDENT forest rows through caps tending to infinity. No COMMON row
or bound on rival size or total clock is assumed.

There is a subsequence with a finite ordered persistent skeleton. Its
strict cells converge to T's cells, in their chronological order and modulo
arm exchange, and its gaps after replacing weak extras by their effective
ordinary passages converge to T's gaps. The remaining weak extras have
maximum strength tending to zero but can retain nonzero total common-clock
surplus. This last possibility prevents application of the BOTH local
exclusion theorem.

Thus the infinite-persistence branch is excluded for this INDEPENDENT
class too. This does not cover unequal-arm targets or arbitrary unequal-arm
INDEPENDENT rivals: unlike in BOTH, no COMMON Jensen reduction is available.

## 1. A legal INDEPENDENT row bounds the entire physical exposure

Let H(W) be total ordinary exposure plus one arm exposure per equal-arm
cell. Put p=g(1-g). The three-root no-merger probability of one cell is

    d3(t,p) = (1-3p) exp(-3t) + 3p exp(-t) <= exp(-t).

An ordinary passage of exposure a has d3=exp(-3a)<=exp(-a).
No-merger probabilities multiply along a private chain. Hence

    D3(W) <= exp(-H(W)).

Once the agreeing cap includes three roots, this gives the derived bound

    H(W_r) <= -log D3(T) = C_T < infinity.              (1)

All probabilities are strictly positive for the fixed finite strict target.
Only its legal INDEPENDENT forest row, or its admitted faithful completion
tests, is used. This is not a supplied rival-clock restriction.

Choose a subsequence with H(W_r)->H*. Choose a constant Hmax>C_T and append
an ordinary passage of exposure Hmax-H(W_r) to W_r. Denote this auxiliary
word by V_r. These words all have COMMON clock Hmax, and at every fixed cap
their INDEPENDENT kernels converge to those of the finite strict word

    T' = T E_(Hmax-H*).                                (2)

Appending is proof bookkeeping on the private kernel: no new observation
of the unknown source or independently chosen tuple is requested. Every
actual W_r still supplies all its original rows with its same tuple.

## 2. The resource proof allows a signed weak-clock coefficient

Apply the inherited fixed-clock compactification to V_r. It gives one
shared chronological carrier, before choosing any cap, with persistent
strict equal-arm cells (t_i,g_i), summable t_i, and ordinary weak residue.
Let delta>=0 be its COMMON-minus-INDEPENDENT weak clock expenditure.
Its endpoint INDEPENDENT law equals T'.

The total ordinary-plus-arm exposure of T' is H_T+Hmax-H*, where H_T
is T's physical total. Write phi_n(t,g)=log R_n(t,g), with
R_n=exp(binomial(n,2)t)d_n(t,g), as in the inherited resource diagnostic.
Then exact endpoint equality gives

    Phi_T'(n) = beta n(n-1) + sum_i phi_n(t_i,g_i),
    beta = (H_T-H*+delta)/2.                            (3)

Here beta is a finite real number; it need not be assumed nonnegative.
All strict target cells of T' are those of T.

Since 0<=phi_n(t,g)<=t n²/4 and sum_i t_i<infinity, dominated convergence
in the quadratic scale gives

    sum_l T_l = sum_i t_i + 4 beta.                    (4)

Put h_i=logit(g_i), b_i=log cosh(h_i/2), and
psi_i(n)=t_i n²/4-phi_i(n)>=0. Equation (4) yields

    Psi_T'(n) = sum_i psi_i(n) + beta n.

Fatou gives sum_i b_i<=B_T-beta<infinity. The inherited exact bounds

    0 <= psi_i(n)/n <= b_i+t_i/4

then justify dominated convergence at the linear scale. Therefore

    B_T = sum_i b_i + beta.

Subtracting the linear identity gives the same absolutely convergent
residual identity as in the paired case,

    rho_T'(n) = sum_i rho_i(n),
    rho_n(t,h) = -log E[exp(-t S²) cosh(hS)],
    S=Bin(n,1/2)-n/2.                                  (5)

No argument in this derivation required beta>=0. Summable b_i implies
summable h_i². At even n, exponentiating (5) gives precisely the integer
product equality of the reviewed meromorphic theorem. Consequently the
carrier has only finitely many persistent strict cells.

## 3. Exact finite-body consequence and the remaining reservoir

The inherited finite boundary chronological normal form compares the
finite persistent proxy word with T'. It identifies every strict cell and
its effective INDEPENDENT gaps. The known appended ordinary passage in
(2) may also be canceled capwise, or removed from the identified last gap.
Thus the selected strict cells in W_r approach T's strict cells, and its
effective ordinary gaps approach those of T.

The strict cell lists agree, so (4) implies beta=0. Equation (3) now gives

    delta = H* - H_T >= 0.                              (6)

Equivalently, for the unselected weak extras along this subsequence,

    max_extra p_i(exp(t_i)-1) -> 0,
    2 sum_extra p_i t_i -> H* - H_T.                   (7)

To see the second equality, collapse extras to their effective ordinary
durations (1-2p_i)t_i. The resulting finite selected body's total exposure
converges to H_T by the identified gaps/cells. Its physical clock differs
from H(W_r) by exactly 2 sum_extra p_i t_i.

Under actual BOTH equality the original COMMON pair row fixes H(W_r)=H_T,
so (7) tends to zero. That is the clock input used by the reviewed
mixed-target local exclusion. INDEPENDENT-only equality supplies no such
identity. A nonzero weak ordinary-clock reservoir in (7) is therefore
still permitted by this proof; maximum weakness tending to zero alone is
insufficient to invoke the BOTH theorem.

The conclusion is the strongest one justified here: **finite persistent
target body plus a potentially nonzero weak ordinary-clock reservoir**.
No exact later-inequivalent rival is constructed, no approximation is
promoted to exact agreement, and no INDEPENDENT finite certificate is claimed.

## Providers and status

Reuse: [bounded-clock compactification](../../../2026-10-10-dot-g4-countable-clock-compactification-1105z/BOUNDED-CLOCK-COUNTABLE-COMPACTIFICATION.md),
[resource identities](../../../2026-10-10-dot-g4-negative-reservoir-diagnostic-1137z/EXACT-NEGATIVE-RESERVOIR-GATE.md),
the finite boundary normal form referenced in the
[finite-persistent consequence](../../general-algebra/FINITE-PERSISTENCE-AND-GLOBAL-GATE.md),
and the reviewed [meromorphic theorem](MEROMORPHIC-FINITE-PERSISTENCE.md).

The addition is the D3-derived clock bound, signed-beta application, and
the precise surviving reservoir when COMMON is removed. Correctness is
hand-derived; primary classical analytic inputs retain their earlier
attribution; novelty is not certified; no numerical, Lean or Rust
verification has been performed.

