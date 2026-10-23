# Actual noncommuting Redfield comparison on chains and rings

21 October 2026. Author: Codex, P5 continuation. Status: hand-proof candidate,
self-reviewed; any finite executed controls are recorded in PROGRESS.md.
No separate review, formal verification or historical novelty is claimed.

## Verdict and precise restriction

The complete actual-response and original-comparator estimate follows for
finite graphs of maximum degree two: arbitrary paths, rings and disjoint
unions thereof. Interactions may be arbitrary Hermitian one- and two-qubit
operators and NEED NOT COMMUTE. All infinite filters, thermal channels,
arbitrary initial density matrices, times and volumes are retained.

This is a restricted P5 theorem, not closure for arbitrary admitted local
geometries or general k. Fix the common geometry bounds k=2, m=nu=3 and
retain their original box

    h <= b0 gamma,
    0 < x=gamma tauB <= 1/288,
    T=sqrt(tauB/gamma).                                 (1)

Every finite path/ring volume is covered using those SAME common bounds,
including a one-site or two-site volume. This statement does not silently
enlarge x to the bigger box available to an isolated smaller component.
Temperature, channel independence, positive type, KMS, envelope and floor
are exactly those in P5-SCOPE.md. No fixed-temperature limit is added.

Write H=sum_Z H_Z, with one-site terms or terms on edges, and

    h=max_i sum_(Z contains i)||H_Z||op.

For a matrix F expand in normalized Hermitian Pauli words:

    F=sum_P f_P P,
    a(F)=sum_(P!=I)|f_P|,
    w(F)=sum_(P!=I)|supp P| |f_P|,
    ||F||P=sum_P |f_P|.

For every fixed finite initial support X, let
c_X=sqrt(4^|X|-1). Then the ACTUAL evolution satisfies

    integral_0^infinity I(exp(tR*)O_X)dt
       <=(8c_X/(b0 gamma))||O_X||op.                   (2)

With B(T) from GENERATOR-COMPARISON.md, the ORIGINAL comparator satisfies

    sup_(Lambda,t>=0)||(exp(tL_T*)-exp(tR*))O_X||op
       <=(8 B(T)/(b0 gamma))c_X ||O_X||op.              (3)

In particular, with j=h/gamma and z=6j sqrt(x),

    error <=(8c_X/b0)[(6 exp(z)+2)j+2]sqrt(x)||O_X||op.
                                                                  (4)

All constants are independent of volume, time and the initial state. The
proof below supplies the previously missing actual full-filter coefficient
premise at this geometric scope; it does not assume actual contraction.

## 1. Exact expansion by boundary crossings

Fix a channel A=sigma_i^a and its connected component C. For a connected
interval J in a path or ring, let H_J contain the original Hamiltonian
terms fully inside J, and U_t^J its exact unitary adjoint evolution. If
F is supported in J, only boundary edges contribute to

    (D_C-D_J)F,       D_J=-i[H_J,.].

There are at most TWO boundary edges. Their summed norms are at most 2h,
so the sum of their commutator-map norm bounds is at most 4h. If J is one
site the sharper 2h is available, but is not needed. Applying a boundary
edge extends the connected interval by at most one site. On a ring the
interval may eventually fill the ring, at which point its boundary is empty.

The exact identity, for any such supported F, is

    U_t^C F=U_t^J F
      +integral_0^t U_(t-s)^C (D_C-D_J)U_s^J F ds.     (5)

Expand the boundary sum in (5). For each resulting operator, reapply (5)
with its enlarged interval. At depth n, every internal propagation is an
EXACT unitary on the current interval, with operator norm one. Every term
has support size at most n+1. Summing operator-norm bounds over ALL boundary
sequences at that depth and integrating the ordered time simplex gives

    sum_(depth n terms) ||term||op <=(4ht)^n/n!.        (6)

This includes all choices of left/right boundary, even where different
histories reach the same interval. There is no count proportional to the
interval's length: its arbitrarily many internal terms are inside U^J,
not expanded in absolute value.

In each finite component this expansion TERMINATES by depth |C|-1: once
the current interval fills C there is no boundary remainder. Thus (5)-(6)
are finite exact identities before any uniform upper series is introduced.
Disconnected components never enter the filter of A.

For a matrix supported on l qubits, Pauli orthogonality and normalized-trace
Cauchy--Schwarz give

    ||F||P <=2^l||F||op.                               (7)

The depth-zero contribution is U_t^{ {i} }A. Its difference from A has
operator norm at most 2ht and Pauli norm at most 4ht. Combining (6)-(7) at
all higher depths gives the actual unitary-orbit estimate

    ||U_t^C A-A||P <=4ht+2(exp(8ht)-1).                (8)

This argument uses norm preservation only for unitary Hamiltonian
propagation. It is not the invalid absolute full-H Taylor series, not a
radius-to-cardinality conversion on an expanding graph, and not an
assertion of Redfield positivity.

## 2. Complete infinite filters, without a bath cutoff

For every original channel put

    Q_p=integral_0^infinity Phi_p(t)(U_t A_p-A_p)dt.

Since (1) implies 8h tauB<=1/36<1, (8) is absolutely integrable against
the actual common covariance envelope. For every finite volume and channel,

    ||Q_p||P <= q1,
    q1=gamma h tauB[4+16/(1-8h tauB)].                 (9)

This is a bound on the ACTUAL oscillatory integral, with an integrable
majorant justified by (5)-(8). The upper series can be integrated because
it is now a scalar exponential. It is not obtained by interchanging the
previously failed factorial Taylor majorant and the bath integral.

Use b0<=1, which follows from the original envelope and floor. Equation
(1) gives the fully uniform bound

    q1/(b0 gamma)
      <=(1/288)[4+16/(1-1/36)]
      =179/2520.                                     (10)

The filters may have support on the entire component; exact finite support
is not being asserted or required. Distinct Phi_p are allowed and retain
their actual thermal admission. Only their common envelope was used in
this estimate.

## 3. General two-qubit interactions and the incidence constant

For a particular two-qubit H_Z and a fixed i in Z, there are precisely
12 Pauli words nonidentity at i. Their coefficients obey

    sum_(P nonidentity at i)|j_(Z,P)|
       <=sqrt(12)[sum_P |j_(Z,P)|^2]^(1/2)
       <=sqrt(12)||H_Z||op.

A one-site term has only three such coefficients and obeys the same safe
constant. Scalar terms have none. Summing ORIGINAL labelled terms before
any optional merging yields the genuine coefficient-incidence bound

    J=max_i sum_(P nonidentity at i)|j_P|
       <=sqrt(12)h=2sqrt(3)h.                         (11)

Thus no assumption J<=h or J<=h after changing normalization is imported.
The sharper site-specific counting (11), rather than the rough J<=4h,
is needed to retain a positive margin for all the general two-qubit
interactions in (1).

## 4. A closed equation for ACTUAL nonconstant Pauli coefficients

Let b_p=Re integral Phi_p and use g=8b0 gamma. The original generator is

    R*=D0*+i[H,.]+V,
    D0*F=sum_p 2b_p(A_p F A_p-F),
    VF=sum_p([A_p,F]Q_p-Q_p^dagger[A_p,F]).              (12)

On a Pauli word P of weight l, D0* has decay at least gl. Hamiltonian
commutation has absolute outgoing coefficient sum at most 2Jl. There are
exactly two anticommuting Pauli axes at every occupied site. Each such
commutator has Pauli norm two. The Pauli norm is submultiplicative and
adjoint invariant, so (9) gives

    ||VP||P <=8q1 l.                                  (13)

Identity annihilation R*I=0 makes the nonconstant coefficient equation
autonomous. Its scalar output is NOT discarded from the evolution; it
simply cannot feed back into that equation. The exact finite-dimensional
coefficient system, with upper derivatives at zero entries, therefore obeys

    D^+ a(exp(tR*)F) <=-kappa w(exp(tR*)F),
    kappa=g-2J-8q1.                                   (14)

There is no I_2 term or unproved reached-family assumption in (14): the
full-filter Pauli norm needed for its column estimate has been proved
uniformly in (9), specifically using the path/ring boundary expansion.

Using (10)-(11) and h<=b0 gamma,

    kappa/(b0 gamma)
       >=8-4sqrt(3)-179/315
       >1/2.                                         (15)

For an exact rational check of the last strict inequality, it is equivalent
to 4sqrt(3)<4367/630. Squaring positive sides gives
4367^2-48*630^2=19489>0.

At any finite horizon L, (14) implies

    a(F_L)+kappa integral_0^L w(F_t)dt <=a(F_0).

Each side is finite before rearrangement. Taking L to infinity by
monotonicity proves integral w<=a(F_0)/kappa. Pauli telescoping gives
I(F)<=4w(F), while a(O_X)<=c_X||O_X||op. Combining these with (15) proves
(2), for actual Redfield, not the auxiliary interacting-noise reference.

Scalar output remains controlled as well: if c(t)=tr(exp(tR*)O_X) under
normalized trace, then |c'(t)|<=8q1 w(exp(tR*)O_X). Its total variation is
at most 8q1 a(O_X)/kappa. Neither tracial stationarity nor R(I)=0 is assumed.

## 5. The original comparator and arbitrary initial states

The source-matched identity in GENERATOR-COMPARISON.md includes the exact
square dissipator and ordered Lamb shift. Its bound (2), with k=2, gives

    ||(L_T*-R*)F||op<=B(T)I(F).

Use finite-time Duhamel with exp((t-s)L_T*) on the OUTSIDE. That factor is
unital CP and contractive; the inside is the actual exp(sR*)O_X and is
bounded in integrated influence by (14). Thus

    ||(exp(tL_T*)-exp(tR*))O_X||op
       <=4 B(T)a(O_X)/kappa,

which proves (3). Applying equation (3) of that companion derivation gives
(4). No infinite-volume evolution or interchange of infinite limits is
needed: the same estimate holds separately in every finite volume.

For Hermitian O_X the operator-norm difference is exactly the supremum of
the absolute predicted expectation difference over every initial system
density matrix. Entangled states and volume-dependent states are included.
The evolved Redfield matrix is not assumed to remain positive.

## 6. Attribution and remaining original P5 obligation

The exact boundary Duhamel expansion, Pauli orthogonality, coefficient
column damping, and the conditional comparator mechanism are established
methods. The 19 October support-resolved packet already proves the
conditional signed-filter implication. This packet supplies its missing
actual-filter premise for the restricted graph class and checks constants
against the original general-operator normalization and box. Historical
priority or a stronger existing theorem has not been excluded.

The argument (6) relies on a connected active interval having a uniformly
bounded boundary. For a general allowed bounded-degree graph the number
of boundary edges can grow with the reached set. Replacing 4h by a
quantity proportional to n changes the coefficient majorant and destroys
this bath-integrability argument. That failure is not a counterexample to
the original comparison; signed cancellations or another invariant norm
may still suffice.

General geometry and general k therefore remain OPEN. The result here is
a complete restricted hand-proof candidate, subject to separate review,
not a claim that full P5 has been closed. No microscopic dynamics,
efficient simulation, multitime intervention, external peer review or Lean
verification is supplied.

