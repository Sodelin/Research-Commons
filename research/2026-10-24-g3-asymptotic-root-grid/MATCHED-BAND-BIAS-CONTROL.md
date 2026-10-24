# Matched-band control of cubic source bias

Stable key G3-MATCHED-BAND-BIAS-01. Existing G3 owner,24October2026UTC.
**PROVED BY HAND at the stated actual-source scope**, author self-review
complete. Independent correctness review and Lean formalization are absent.
No new source/coefficient/model/solver/native/formal execution occurred.

## 1. Statement on the unchanged original fibre

Use the same actual equal-arm private words and original current-root/
opaque-graft9/7/6/4 representation as COMPENSATED-SOURCE-JUMPS.md.
Keep the active SAME-tuple conditions

    K_COMMON=E(c), b2I(K)=c^(3/4), c=2^(-1/m),
    [K_I,S(t)]=0 through the complete nine-root carrier,
    H=-log c, h=-log t,

with unchanged S(t). All natural coins, relative cell scales and finite
counts remain arbitrary. Write the EXACT reference eigenbasis entries
as A_h,B_h,D_h,E_h,G_h. For an actual cell define

    q_i=exp(-u_i), v_i=g_i*(1-g_i), beta_i=(2g_i-1)^2,
    r_i=v_i*(beta_i*u_i^2+u_i^3),
    w_i=v_i*beta_i^2*u_i^3, l_i=v_i*u_i^5.

Let a(s)=R12(prefix)/R11(prefix) in that reference basis, with the SAME
positive nominal pair clock used in the existing proof. Put

    E_a=integral a(s)^2 ds,
    W=sum_i w_i, L5v=sum_i l_i.

There are fixed effective H0,h0,C>0 such that every such word with
0<H<=H0 and0<h<=h0 satisfies

    W<=C*(L5v+E_a+H*h^4).                          (1)

The constants have no coin or count margin. Each actual u_i<=H, because
the COMMON product is c. Thus the small-H condition controls every
original cell automatically. Choosing a sufficiently large FIXED m
is already permitted in AG-Pair; it adds no requirement to original G3.

The reference also satisfies the completed derived bound

    R_h:=A_h+D_h/kappa=O(h^4), kappa=5/3.           (2)

This is stronger than its immediate leading-eigenvector cancellation.
No sign or exact leading coefficient of R_h is asserted.

Equation(1) bounds a bias source sum USING energy and a fifth-order sum.
It does not bound either remaining quantity, force pointwise fairness,
supply V_h or an index, or close original G3.

## 2. Prior comparison and reused source identities

The full multiplicative representation and its lower bands are OLD:
research/2026-10-07-dot-g4-coupled-source-state-interface-0252z/
METHOD-COMPARISON-AND-SOURCE-STATE.md at Commons8b96f4fb,
6918B/SHA7da5c426153438a70513dc7bf703f5ab77630831d4196bd6e83f718c4f75470f.
Its COMPLETE body was read. The U,T and extra e source dependence is
retained, not replaced by independent matrix controls.

The immediate source supplier is
[COMPENSATED-SOURCE-JUMPS.md](https://github.com/Sodelin/Research-Commons/blob/b1fd4801188ccf19e43c04989eddd6b5fd3cfddc/research/2026-10-24-g3-asymptotic-root-grid/COMPENSATED-SOURCE-JUMPS.md),
14724B/SHA794bcb58e93ed33c2075b6176c229875c7235a788e1c5609a3890e4f2dd6e0e0.
Its complete source polynomial factors, all-coin bounds, conjugation and
known reference estimates are REUSED. The OLD independently scoped
source reviews remain its suppliers; this note has no new review receipt.

The later forced-trace9431B/
SHAe176acf212f0ace869445f7f9103cdc837d190e3ce6e2d853b08eb33222ed8fd
is also complete at its scope. It does not supply the matched-band
combination(2) or the positive weighted sigma balance used here.
The OLD nonlinear trace/R7 and near-fair R9 conclusions retain their
actual endpoint/coin scopes. No new nonlinear trace is claimed.

The complete old PSD-cocycle proof10166B/9798064c..., extension7740B/
c772b84e..., both later accepted reviews and README were read. Their
ALL-source algebraic PSD-cocycle exclusion remains PROVED/REUSE. This
argument instead uses the actual paired commutator boundary and bounds
one source moment with remaining energy; it claims no global monotone
PSD defect or tensor repair.

Relevant local current AND archived matched-band/sigma-balance aliases
were compared before this write. A bounded no-hit is not corpus absence
or historical novelty. The old source polynomials and all earlier
mathematical source bodies are unchanged.

## 3. The one-sided source term is already in the completed factorization

For one actual pair-normalized C=exp(-tau Q)B, keep its OLD entries

    C=[d1 F F 0; 0 d2 0 -kappa*F+sigma;
                    0 0 d3 kappa*F+rho; 0 0 0 d4].

The completed exact polynomial numerator of sigma has leading term
-v*beta^2*u^3. Uniform polynomial/denominator bounds from that proof give,
for all sufficiently small u and every strict coin,

    sigma=-w+O(u*w+v*beta*u^4+v*u^5).              (3)

This follows directly from its NU factor; replacing1-q by u changes
the cubic term by O(u*w). All constants are uniform at endpoint coins,
used for bounding only.

Young's inequality on the quartic mixed term gives, for fixed epsilon>0,

    v*beta*u^4 <=epsilon*w+v*u^5/(4epsilon).

First choose epsilon, then the uniform upper u threshold. Consequently

    sigma<=-c0*w+C0*l                              (4)

for fixed c0,C0>0. This is a one-sided bound, not a claim that sigma
has one sign on all cells. No new coefficient producer is needed.

We will also use the completed positive diagonal/source bounds
|dj-1|+|F|<=C*r and fixed bounds on dj and their reciprocals. For small
u they imply the analogous bounds on every displayed diagonal ratio.

## 4. The exact matched-band equation

In the reference basis let

    a=R12/R11, e=R24/(kappa*R22), Cstate=a+e,
    R_h=A_h+D_h/kappa.

The lower coordinate is an internal coordinate of the SAME actual
prefix. It is not an added legal observation or a frozen exterior.
Ordinary right evolution gives EXACTLY

    a'=15a-15A_h,
    e'=15e-15D_h/kappa,
    Cstate'=15Cstate-15R_h.                        (5)

For a source append put

    alpha=d2/d1, betaRatio=d4/d2.

The completed conjugation gives X=F+A_h*(d1-d2) and
U=-kappa*F+sigma+D_h*(d2-d4). Direct substitution in the two normalized
updates gives EXACTLY

    Cstate+=betaRatio*Cstate-+j,

    j=(alpha-betaRatio)*(a--A_h)
        +sigma/(kappa*d2)
        +F*(1/d1-1/d2)
        +R_h*(1-betaRatio).                       (6)

No diagonal ratio, source transverse term or affine constant is dropped.
In particular |alpha-betaRatio|<=C*r, and the third term is O(r^2).

## 5. Reference cancellation proves(2) without a new source expansion

Apply(5)-(6) to the KNOWN one-cell S(t) itself. Its actual pair clock
is3h and its initial/final Cstate values are0, since its represented
matrix is diagonal in the EXACT reference basis.

Along its ordinary intervals a=O(h^3), while A_h=O(h^2). Its single
fair normalized cell has r=O(h^3), sigma=O(h^5), F=O(h^3) by the
completed source bounds. Hence(6) gives

    |j|<=C*h^5+C*h^3*|R_h|.

Use the positive integrating factor for(5), with its inverse betaRatio
jump. It stays comparable to1, and its integral is at least c*h.
The zero endpoints therefore imply

    |R_h|*h <=C*h^5+C*h^3*|R_h|.

Absorb the final term for sufficiently small h. This proves(2). The
same argument does not set R_h to0 or infer a universal source sign.
Its effective constants come from the existing rational reference
formulas and removable zeros, without evaluating any new tuple.

## 6. Positive weights and the source-word inequality

For an arbitrary active word the nominal pair clock is T=3H/4. The
positive propagator Pi for Cstate has Pi'=15Pi and Pi+=betaRatio*Pi-.
Its completed-prefix value is the actual b4/b7 diagonal ratio.
Inside preceding nominal intervals it remains an actual positive
prefix followed by an ordinary interval consuming at most the remaining
COMMON budget. Therefore

    1<=Pi<=c^(-21).

Full commutation makes BOTH normalized matched-band endpoints zero.
Divide(5)-(6) by Pi and integrate. With positive weights
omega_i=1/Pi_i+ bounded above/below independently of count, exactly

    sum_i omega_i*j_i
       =15R_h*integral_0^T Pi(s)^(-1) ds.          (7)

The sigma coefficient omega_i/(kappa*d2_i) also has fixed positive
two-sided bounds for H below any fixed small upper threshold.

Insert(4) and bound only the remaining terms of(6). Equations(2),(7)
and the source bounds imply

    W<=C*[L5v+sum r_i*|a_i--A_h|
                      +sum r_i^2+H*h^4].          (8)

The R_h*(1-betaRatio) contribution is covered by H*h^4:
sum r_i<=C*H^2 when sum u_i<=H and u_i<=H<=1.
All constants can first be chosen uniformly for0<H<=Hbar<=log2.

The trace before each C_i has length at least tau_i>=3u_i/8.
Since (a-A_h)'=15(a-A_h) is homogeneous on that interval, the OLD
own-preceding exponential trace gives

    sum u_i*(a_i--A_h)^2
       <=C*integral (a-A_h)^2
       <=C*(E_a+H*h^4).                           (9)

This does not use a post-jump or adjacent-scale trace.

The source definition gives an elementary bound with no coin margin:

    r_i^2/u_i
       =v_i^2*(beta_i^2*u_i^3+2beta_i*u_i^4+u_i^5)
       <=(w_i+l_i)/2.                            (10)

Here2beta*u^4<=beta^2*u^3+u^5 and v<=1/4. Thus, with
delta=max u_i<=H,

    sum r_i^2<=delta*(W+L5v)/2,

and finite Cauchy-Schwarz in(9)-(10) yields

    sum r_i*|a_i--A_h|
       <=C*sqrt[(E_a+H*h^4)*(W+L5v)].

Insert these in(8). Choose the fixed H0 small enough to absorb its
delta*W term. Young's inequality then absorbs the square-root's W
part and proves(1). Zero W or zero energy creates no division issue.
Constants depend on the fixed source/reference formulas, not on actual
word length, minimum coin, minimum scale or a ratio between scales.

## 7. What remains for original G3

The matched forcing(2), exact balance(6)-(7) and bound(1) are completed
at HAND scope. They do not show L5v or E_a small in h. In particular
they do not discard tiny biased cells, exclude multiscale cancellation,
produce a physical replacement or make a source moment an observable.

The existing ONE mathematical frontier remains AG-Pair, or a materially
superseding source disproof. Signed chronological energy/source control
sufficient for the index is still unproved. No count bound, one-witness
H(D), unrestricted NO, original impossibility or master G4 result is
asserted. Current-root routing, SAME original register/tuple/clock/parent
and legal-caller conditions are unchanged. All original ownership,
no-local-Git/no-subagent and model/native/controller/held/privacy holds
remain. No new peer review/proof/build/model job is selected.
